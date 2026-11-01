import struct
import sys
# Maps are extracted once; Save creates revisions, Inject changes game archives.
sys.dont_write_bytecode = True
import json
from datetime import datetime, timezone
import hashlib
import html
import re
from io import BytesIO
from PIL import Image
import find_v5B as scenario
import zlib
from pathlib import Path

# Install if needed: python -m pip install PySide6 Pillow pefile capstone
from PySide6.QtCore import QItemSelectionModel, QPointF, QRectF, Qt, Signal
from PySide6.QtGui import QColor, QFont, QImage, QPainter, QPalette, QPen, QPixmap, QStaticText
from PySide6.QtWidgets import (
    QApplication, QComboBox, QHBoxLayout, QLabel, QMainWindow, QMessageBox,
    QPlainTextEdit, QPushButton, QTabWidget, QTextBrowser, QVBoxLayout, QWidget,
)

# Background textures are read from the installed game without extraction.
# Map snapshots and their index live in maps-extract.
# Known EU executable layout; verify its fingerprint before reading these RVAs.
# FUN_140f33cb0 indexes the HUD table; FUN_1410c75f0 indexes the pause table.
EXE_SHA256 = "ae09a34d05555298d12b130cc762f12d20abc5be57697c4ae79e6601a0561bb5"
TEXTURE_TABLE_RVAS = {"HUD": 0x14019D0, "Pause": 0x149B780}
IMAGE_OPTIONS = {}  # Populated from live archive bytes by load_backgrounds().

def discover_command_vtables(data, image_base, sections, offset, pe_header):
    """Recover opcode -> vtable from RTTI and native factory control flow.

    No factory addresses, jump-table addresses, opcode lists or vtable addresses
    are supplied. PE exception records bound functions; RTTI identifies command
    classes; RIP-relative references identify the two factories. Interpret their
    dispatch instructions, then follow each case to its constructor's vtable.
    This reads instructions as data, never executes code from the game.
    """
    from bisect import bisect_right
    from collections import defaultdict
    import capstone
    from capstone.x86_const import X86_OP_REG, X86_OP_IMM, X86_OP_MEM, X86_REG_RIP

    optional=pe_header+24
    scenario.require(struct.unpack_from('<H',data,optional)[0]==0x20B,'Expected a 64-bit PE executable')
    directory=optional+struct.unpack_from('<H',data,pe_header+20)[0]
    executable=[(start,start+length) for i,(_,start,length,_) in enumerate(sections)
                if struct.unpack_from('<I',data,directory+i*40+36)[0]&0x20000000]
    def is_code(rva):return any(start<=rva<end for start,end in executable)
    def file_rva(position):
        for _,start,length,raw in sections:
            if raw<=position<raw+length:return start+position-raw
        return None
    def occurrences(needle):
        position=data.find(needle)
        while position>=0:
            yield position
            position=data.find(needle,position+1)

    # MSVC x64 CompleteObjectLocator: signature, object offset, constructor
    # displacement, type descriptor RVA, hierarchy RVA, self RVA. Checking all
    # structural fields avoids mistaking arbitrary name/pointer matches for RTTI.
    classes={}
    for match in re.finditer(rb'\.\?AVCSc(?:Cond|Eff)[A-Za-z0-9_]+@@\x00',data):
        type_rva=file_rva(match.start()-16)
        if type_rva is None:continue
        kind='condition' if match.group().startswith(b'.?AVCScCond') else 'effect'
        for position in occurrences(struct.pack('<I',type_rva)):
            locator=position-12
            if not 0<=locator<=len(data)-24:continue
            signature,subobject,construction,_,hierarchy,self_rva=struct.unpack_from('<6I',data,locator)
            if (signature,subobject,construction)!=(1,0,0) or self_rva!=file_rva(locator):continue
            try:offset(hierarchy,16)
            except ValueError:continue
            for pointer in occurrences(struct.pack('<Q',image_base+self_rva)):
                vtable=file_rva(pointer+8)
                if vtable is None or vtable%8:continue
                try:
                    first,initializer=struct.unpack_from('<QQ',data,offset(vtable,16))
                except ValueError:continue
                if is_code(first-image_base) and is_code(initializer-image_base):classes[vtable]=kind
    scenario.require(classes,'No scenario command RTTI found in the executable')

    exception_rva,exception_size=struct.unpack_from('<II',data,optional+112+3*8)
    scenario.require(exception_size and exception_size%12==0,'Invalid PE function directory')
    start=offset(exception_rva,exception_size)
    functions=[(begin,end) for begin,end,_ in struct.iter_unpack('<III',data[start:start+exception_size])]
    starts=[begin for begin,_ in functions]
    scenario.require(starts==sorted(set(starts)),'Unordered PE function directory')
    def function_at(rva):
        index=bisect_right(starts,rva)-1
        return functions[index] if index>=0 and rva<functions[index][1] else None

    references=defaultdict(set)
    # LEA r64,[RIP+disp32], all destination registers. Only executable sections
    # are searched. Capstone re-decodes every reference used during traversal.
    pattern=rb'[\x48\x4c]\x8d[\x05\x0d\x15\x1d\x25\x2d\x35\x3d][\s\S]{4}'
    for begin,end in executable:
        raw=offset(begin,end-begin)
        for match in re.finditer(pattern,data[raw:raw+end-begin]):
            rva=begin+match.start();target=rva+7+struct.unpack_from('<i',match.group(),3)[0]
            function=function_at(rva)
            if target in classes and function:references[function[0]].add(target)
    factories={}
    for kind in ('condition','effect'):
        ranked=sorted(((sum(classes[v]==kind for v in refs),begin) for begin,refs in references.items()),reverse=True)
        scenario.require(ranked and ranked[0][0]>1 and (len(ranked)==1 or ranked[0][0]>ranked[1][0]),
                         'Cannot uniquely locate the '+kind+' factory')
        factories[kind]=ranked[0][1]

    decoder=capstone.Cs(capstone.CS_ARCH_X86,capstone.CS_MODE_64);decoder.detail=True
    instructions={}
    def instruction(rva):
        if rva not in instructions:
            scenario.require(is_code(rva),'Command branch leaves executable code')
            raw=offset(rva,15)
            item=next(decoder.disasm(data[raw:raw+15],rva,count=1),None)
            scenario.require(item is not None,'Cannot decode command factory instruction')
            instructions[rva]=item
        return instructions[rva]
    def register(item,reg):
        name=item.reg_name(reg)
        aliases={'eax':'rax','ax':'rax','al':'rax','ecx':'rcx','cx':'rcx','cl':'rcx',
                 'edx':'rdx','dx':'rdx','dl':'rdx','ebx':'rbx','bx':'rbx','bl':'rbx',
                 'esi':'rsi','si':'rsi','sil':'rsi','edi':'rdi','di':'rdi','dil':'rdi',
                 'esp':'rsp','ebp':'rbp'}
        return aliases.get(name,re.sub(r'^(r[0-9]+)[dwb]$',r'\1',name))
    def dispatch(factory,opcode):
        bounds=function_at(factory);pc=factory;registers={};comparison=None;loaded=False
        identities=set();upper=65535;comparison_bound=None
        def value(item,operand,address_only=False):
            nonlocal upper
            if operand.type==X86_OP_IMM:return operand.imm
            if operand.type==X86_OP_REG:return registers.get(register(item,operand.reg))
            if operand.type!=X86_OP_MEM:return None
            mem=operand.mem
            if any(register(item,r) in identities for r in (mem.base,mem.index) if r):
                upper=opcode  # An indexed lookup must be checked for each input.
            base=item.address+item.size if mem.base==X86_REG_RIP else registers.get(register(item,mem.base)) if mem.base else 0
            index=registers.get(register(item,mem.index)) if mem.index else 0
            if base is None or index is None:return None
            address=base+index*mem.scale+mem.disp
            if address_only:return address
            raw=offset(address,operand.size)
            return int.from_bytes(data[raw:raw+operand.size],'little')
        for _ in range(160):
            scenario.require(bounds[0]<=pc<bounds[1],'Dispatch leaves the command factory')
            item=instruction(pc);op=item.mnemonic;args=item.operands;next_pc=pc+item.size
            if op=='call':
                scenario.require(loaded,'Factory does not read the command opcode')
                return pc,upper+1
            if op=='ret':return None,upper+1
            if op in ('mov','movzx','movsx','movsxd','lea') and args[0].type==X86_OP_REG:
                # Native command operand is a u16 at [RDX] (Win64 argument 2).
                if (not loaded and op=='movzx' and args[1].type==X86_OP_MEM and args[1].size==2
                        and item.reg_name(args[1].mem.base)=='rdx' and not args[1].mem.index and not args[1].mem.disp):
                    result=opcode;loaded=True;identity=True
                else:
                    result=value(item,args[1],op=='lea')
                    identity=(op!='lea' and args[1].type==X86_OP_REG
                              and register(item,args[1].reg) in identities and args[1].size>=2)
                name=register(item,args[0].reg);registers[name]=result
                identities.discard(name)
                if identity:identities.add(name)
            elif op in ('add','sub','xor') and args[0].type==X86_OP_REG:
                left,right=value(item,args[0]),value(item,args[1]);name=register(item,args[0].reg)
                zero=(op=='xor' and args[0].type==args[1].type==X86_OP_REG and args[0].reg==args[1].reg)
                if not zero and any(a.type==X86_OP_REG and register(item,a.reg) in identities for a in args):upper=opcode
                identities.discard(name)
                if zero:result=0
                elif left is None or right is None:result=None
                else:result={'add':lambda:left+right,'sub':lambda:left-right,'xor':lambda:left^right}[op]()
                registers[name]=None if result is None else result&((1<<(8*args[0].size))-1)
                comparison=None
            elif op in ('cmp','test'):
                left,right=value(item,args[0]),value(item,args[1])
                scenario.require(left is not None and right is not None,'Unresolved command dispatch comparison')
                comparison=(left,right) if op=='cmp' else (left&right,0)
                comparison_bound=(right if op=='cmp' and args[0].type==X86_OP_REG
                    and register(item,args[0].reg) in identities and args[1].type==X86_OP_IMM else None)
            elif op=='jmp':next_pc=value(item,args[0])
            elif op.startswith('j'):
                scenario.require(comparison is not None,'Unresolved command dispatch branch')
                left,right=comparison
                branches={'ja':left>right,'jae':left>=right,'jb':left<right,'jbe':left<=right,
                          'je':left==right,'jne':left!=right}
                scenario.require(op in branches,'Unsupported command dispatch branch: '+op)
                taken=branches[op]
                if comparison_bound is not None:
                    bound=comparison_bound
                    if (op=='ja' and not taken) or (op=='jbe' and taken):upper=min(upper,bound)
                    elif (op=='jae' and not taken) or (op=='jb' and taken):upper=min(upper,bound-1)
                    elif op in ('je','jne'):
                        equal=taken if op=='je' else not taken
                        if equal:upper=min(upper,bound)
                        elif opcode<bound:upper=min(upper,bound-1)
                if taken:next_pc=value(item,args[0])
            elif op not in ('mov','push','pop','nop'):
                raise ValueError('Unsupported command dispatch instruction: '+op)
            scenario.require(next_pc is not None,'Unresolved command dispatch destination')
            pc=next_pc
        raise ValueError('Command factory dispatch did not terminate')

    cases={}
    def case_vtables(entry,kind):
        key=(entry,kind)
        if key in cases:return cases[key]
        pending=[entry];visited=set();found=set()
        while pending:
            pc=pending.pop()
            if pc in visited:continue
            scenario.require(len(visited)<8192,'Command constructor traversal exceeded its limit')
            visited.add(pc);item=instruction(pc);op=item.mnemonic;args=item.operands
            if op=='lea' and args[1].type==X86_OP_MEM and args[1].mem.base==X86_REG_RIP:
                target=pc+item.size+args[1].mem.disp
                if classes.get(target)==kind:found.add(target)
            if op=='ret':continue
            if op=='jmp':
                scenario.require(args[0].type==X86_OP_IMM,'Indirect branch inside a command constructor')
                pending.append(args[0].imm);continue
            if op.startswith('j'):
                scenario.require(args[0].type==X86_OP_IMM,'Invalid constructor branch')
                pending.append(args[0].imm)
            if op=='call' and args[0].type==X86_OP_IMM:
                # Out-of-line constructors reference their own RTTI-validated
                # vtable. Allocation/utility calls without one are not followed.
                target=args[0].imm
                if any(classes[v]==kind for v in references.get(target,())):pending.append(target)
            pending.append(pc+item.size)
        scenario.require(len(found)<=1,'Ambiguous command constructor vtable')
        cases[key]=found
        return found

    result={}
    for kind,factory in factories.items():
        table={}
        # Cover the entire u16 domain. Comparison-only paths prove intervals
        # (e.g. every value above a bound is rejected); indexed table lookups
        # narrow the interval to one value. This avoids re-interpreting the same
        # rejection path 65,000 times without assuming opcode counts or IDs.
        opcode=0
        while opcode<65536:
            entry,next_opcode=dispatch(factory,opcode)
            scenario.require(opcode<next_opcode<=65536,'Invalid dispatch interval')
            if entry is not None:
                found=case_vtables(entry,kind)
                scenario.require(len(found)==1,f'Cannot resolve {kind} opcode {opcode}')
                vtable=next(iter(found))
                for accepted in range(opcode,next_opcode):table[accepted]=vtable
            opcode=next_opcode
        scenario.require(table,'Empty '+kind+' command factory')
        result[kind]=table
    return result


COMMAND_CACHE_PATH = Path(__file__).resolve().parent/'map-extract'/'cache'/'command_catalog.json'
COMMAND_CACHE_FORMAT = 1


def command_catalog_bytes(catalog):
    # Canonical bytes keep JSON's conversion of opcode keys to strings stable.
    return json.dumps(catalog,sort_keys=True,separators=(',',':'),ensure_ascii=True).encode('utf-8')


def read_command_catalog_cache(exe_digest):
    try:
        stored=json.loads(COMMAND_CACHE_PATH.read_text(encoding='utf-8'))
        if stored['format']!=COMMAND_CACHE_FORMAT or stored['exe_sha256']!=exe_digest:return None
        catalog=stored['catalog']
        if hashlib.sha256(command_catalog_bytes(catalog)).hexdigest()!=stored['catalog_sha256']:return None
        if set(catalog)!= {'condition','effect','native_proof'}:return None
        result={}
        for kind,prefix in (('condition','CScCond'),('effect','CScEff')):
            rows=catalog[kind]
            if not isinstance(rows,dict) or not rows:return None
            result[kind]={}
            for key,record in rows.items():
                opcode=int(key)
                if str(opcode)!=key or not 0<=opcode<=65535:return None
                if set(record)!= {'class_name','vtable_rva','initializer_va','callbacks'}:return None
                if not isinstance(record['class_name'],str) or not record['class_name'].startswith(prefix):return None
                if any(type(record[field]) is not int or record[field]<=0 for field in ('vtable_rva','initializer_va')):return None
                roles=({'condition evaluator','per-unit test'} if kind=='condition' else
                       {'effect activation','delayed update','per-unit application'})
                if set(record['callbacks'])!=roles:return None
                if any(type(address) is not int or address<=0 for address in record['callbacks'].values()):return None
                result[kind][opcode]=record
        proof=catalog['native_proof']
        if not isinstance(proof,list) or not proof:return None
        for item in proof:
            if set(item)!= {'address','bytes','description'} or type(item['address']) is not int:return None
            if not isinstance(item['description'],str) or not bytes.fromhex(item['bytes']):return None
        result['native_proof']=proof
        return result
    except (OSError,ValueError,KeyError,TypeError,AttributeError):
        # Missing, interrupted, stale or damaged caches are rebuilt from the EXE.
        return None


def executable_command_names(path):
    """Extract once per EXE/build and cache the full command catalog on disk."""
    data=Path(path).read_bytes();exe_digest=hashlib.sha256(data).hexdigest()
    scenario.require(exe_digest==EXE_SHA256,'Unsupported executable build for scenario command decoding')
    cached=read_command_catalog_cache(exe_digest)
    if cached is not None:return cached
    catalog=extract_executable_command_names(data)
    # JSON uses string opcode keys; normalize before computing its checksum so
    # fresh extraction and later launches hash the same representation.
    serialized=json.loads(json.dumps(catalog))
    stored=dict(format=COMMAND_CACHE_FORMAT,exe_sha256=exe_digest,
                catalog_sha256=hashlib.sha256(command_catalog_bytes(serialized)).hexdigest(),catalog=serialized)
    try:
        COMMAND_CACHE_PATH.parent.mkdir(parents=True,exist_ok=True)
        atomic_map_write(COMMAND_CACHE_PATH,(json.dumps(stored,indent=2)+'\n').encode('utf-8'))
    except (OSError,ValueError):
        # A read-only installation can still run using the verified extraction.
        pass
    return catalog


def extract_executable_command_names(data):
    """Discover factory mappings and verify names/callbacks against EXE bytes."""
    pe = struct.unpack_from("<I", data, 0x3C)[0]
    count = struct.unpack_from("<H", data, pe + 6)[0]
    optional_size = struct.unpack_from("<H", data, pe + 20)[0]
    image_base = struct.unpack_from("<Q", data, pe + 24 + 24)[0]
    directory = pe + 24 + optional_size
    sections = [struct.unpack_from("<4I", data, directory + i * 40 + 8)
                for i in range(count)]

    def offset(rva, size):
        for _, start, length, raw in sections:
            if start <= rva and rva + size <= start + length:
                return raw + rva - start
        raise ValueError("Command metadata outside executable sections")

    tables = discover_command_vtables(data, image_base, sections, offset, pe)
    names = {}
    for kind, table in tables.items():
        names[kind] = {}
        for opcode, vtable in table.items():
            locator = struct.unpack_from("<Q", data, offset(vtable - 8, 8))[0] - image_base
            type_rva = struct.unpack_from("<I", data, offset(locator + 12, 4))[0]
            start = offset(type_rva + 16, 1)
            end = data.find(b"\0", start, start + 160)
            scenario.require(end >= start, "Invalid command RTTI name")
            decorated = data[start:end].decode("ascii")
            prefix = ".?AVCScCond" if kind == "condition" else ".?AVCScEff"
            scenario.require(decorated.startswith(prefix) and decorated.endswith("@@"),
                             "Unexpected scenario command class")
            callbacks = ({"condition evaluator": 0x18, "per-unit test": 0x40}
                         if kind == "condition" else
                         {"effect activation": 0x28, "delayed update": 0x38, "per-unit application": 0x18})
            names[kind][opcode] = dict(class_name=decorated[4:-2], vtable_rva=vtable,
                                      initializer_va=struct.unpack_from("<Q", data, offset(vtable + 8, 8))[0],
                                      callbacks={role: struct.unpack_from("<Q", data, offset(vtable + slot, 8))[0]
                                                 for role, slot in callbacks.items()})
    # Instruction spans checked against the installed EXE, in addition to its
    # whole-file fingerprint. These establish the objective write/read and the
    # scheduler-to-appearance path; no scenario-specific event IDs are assumed.
    checks = (
        (0x140D158DB, "0fb742048941440fb74206894148", "Objective initializer: +04 slot, +06 state"),
        (0x140D1513B, "49635544488b8080000000488b3cd0", "Writer selects objective table +80, indexed by slot"),
        (0x140D1579D, "418b5548488bcfe8e75ffeff", "Requested state passed to FUN_140cfb790"),
        (0x140CFB7E8, "40887908", "Store requested state into objective +08"),
        (0x140D05280, "0fb742028941380fb7420489413c0fb74206894140", "Condition initializer: +02 slot, +04 state, +06 comparison"),
        (0x140D05238, "488b808000000049634838488b14c8", "Reader selects objective table +80, indexed by slot"),
        (0x140D0524E, "0fb64a08418b503c3bca0f94c0", "Read objective +08 and compare with requested state"),
        (0x140D0525B, "4183784000750733c03bca0f95c0", "Comparison operand: nonzero equality, zero inequality"),
        (0x140D01529, "e8b2a1010085c00f84ae050000", "Scheduler evaluates conditions and branches on the result"),
        (0x140D0182E, "488b0d9bbd2601488bd7e8237bffff", "Scheduler submits a queued event to FUN_140cf9360"),
        (0x140CF97BD, "498b8e582f010048893cd949ff86482f0100", "Queue stores event pointer and increments count"),
        (0x140CEA40B, "ff5020", "Queue dispatches event vtable +20"),
        (0x140D1B145, "e8b6f7ffff85c07513", "Queued event rechecks its condition tree before starting"),
        (0x140D1B171, "e92a070000", "Event update tail-calls FUN_140d1b8a0"),
        (0x140D1BA34, "ff5028", "Effect executor calls effect vtable +28"),
        (0x140D0EB6D, "ff5038", "Zero-delay appearance calls update vtable +38"),
        (0x140D0EB12, "ff5318", "Appearance update calls per-unit vtable +18"),
        (0x140D0EACC, "e90ffbd3ff", "Per-unit appearance tail-calls FUN_140a4e5e0"),
        (0x140A4E61C, "488323df", "Clear entity hidden bit 0x20"),
        (0x140D09950, "0fb74202668941400fb7420466894142", "Lighting clock initializer: hours and minutes"),
        (0x140DBFCC8, "440fb68c37c92d0400440fb68437c82d0400", "Mission clock and lighting preset readers"),
    )
    evidence = []
    for address, expected, description in checks:
        expected = bytes.fromhex(expected)
        start = offset(address - image_base, len(expected))
        actual = data[start:start + len(expected)]
        scenario.require(actual == expected, f"Executable proof mismatch at 0x{address:X}: {description}")
        evidence.append(dict(address=address, bytes=actual.hex(" "), description=description))
    paragraph_update = struct.unpack_from("<Q", data, offset(0x1AF7A20, 8))[0]
    scenario.require(paragraph_update == 0x140D1B130, "Unexpected CScParagraph update callback")
    names["native_proof"] = evidence
    return names


COMPARISONS = {0: "<", 1: "<=", 2: "=", 3: ">=", 4: ">"}
# CScEffMission 140d144f0 -> 140cfb790 stores the requested state at +08.
# State 2 activates objective target marking (140d154db); state 3 increments
# completed counters at manager+D00, state 4 failed counters at +D02.
# The counter category is objective slot >=10 (140cfc127), separating side
# objectives from main objectives. These are game slot IDs, consistently zero-based.
OBJECTIVE_STATES = {0: "not started", 1: "in preparation", 2: "active", 3: "completed", 4: "failed"}


def condition_tree(conditions):
    # FUN_140d1a900 / 140d1acb0 dispatch FF to 140d1ab00 (AND), FE to
    # 140d1abe0 (OR). CScCondFolder +02 is the number of DIRECT children;
    # nested groups consume a preorder stream, not a flat list of conditions.
    def take(index, depth=0):
        scenario.require(depth <= 255 and index < len(conditions), "Truncated condition group")
        command = conditions[index]
        node = dict(command=command, children=[])
        index += 1
        if command["opcode"] in (0xFE, 0xFF):
            node["operator"] = "all" if command["opcode"] == 0xFF else "any"
            for _ in range(command["raw_u16"][1]):
                child, index = take(index, depth + 1)
                node["children"].append(child)
        return node, index

    if not conditions:
        return None, []
    root, consumed = take(0)
    # The evaluator starts at the first node. Do not invent an AND for trailing
    # nodes in an edited/malformed stream; retain them explicitly in Debug mode.
    return root, list(range(consumed, len(conditions)))


def enrich_scenario(result):
    names = executable_command_names(Path(result.get("editor_game_root") or scenario.resolve_game_root(result["source"])) / "AOT2_EU.exe")
    events = result["behavior"]["events"]
    counts = dict(named_commands=0, unnamed_commands=0, decoded_conditions=0)
    for event in events:
        header = event["unknown_header"]
        # Constructor 140d1b2e0 copies +00 to object+54. 140d1a900 uses it
        # as a parent paragraph ordinal and recursively checks group flag 4.
        event["decoded_header"] = dict(parent_paragraph=header["u32_+0x00"],
                                       execution_mode=header["u8_+0x08"],
                                       initial_flags=header["u8_+0x09"])
        for kind, key in (("condition", "conditions"), ("effect", "effects")):
            for command in event[key]:
                info = names[kind].get(command["opcode"])
                if info:
                    command["class_name"] = info["class_name"]
                    command["label"] = info["class_name"]
                    command["executable_evidence"] = info
                    counts["named_commands"] += 1
                else:
                    counts["unnamed_commands"] += 1
                decode_command(command)
                if kind == "condition" and command.get("decoded"):
                    counts["decoded_conditions"] += 1
        tree, trailing = condition_tree(event["conditions"])
        event["condition_tree"] = tree
        event["trailing_conditions"] = trailing
    result["decoding"] = counts
    result["native_proof"] = names["native_proof"]
    result["special_target_rules"] = {}
    for event in events:
        for effect in event["effects"]:
            if effect["opcode"] == 0x57 and effect["raw_u16"][2] == 1:
                result["special_target_rules"].setdefault(effect["raw_u16"][1], []).append(event["ordinal"])
    result["script_writers"] = build_script_writers(events)
    result["party_names"] = read_party_names(Path(result.get("editor_game_root") or scenario.resolve_game_root(result["source"])))


def read_party_names(root):
    # English text resource, section 6: the eleven PARTY substitution names.
    # CScEffMission initializer 140d158d0 copies +0C/+0E to +54/+56;
    # 140d14d8a emits formatter type 5 (PARTY), accepting IDs below 11.
    # CScEffMsgSituation uses the same pair at command +08/+0A.
    _, archive = scenario.name_archive_paths(root)
    data, _ = scenario.read_name_resource(archive, 3)
    scenario.require(scenario.u32(data) > 6, "Missing English party-name section")
    start = scenario.u32(data, 4 + 6 * 4)
    end = scenario.u32(data, 4 + 7 * 4)
    scenario.require(0 <= start < end <= len(data) and scenario.u32(data, start) == 11,
                     "Unsupported English party-name table")
    names = []
    for index in range(11):
        offset, size = scenario.unpack("<II", data, start + 4 + index * 8)
        scenario.require(offset >= 92 and size > 0 and start + offset + size <= end,
                         "Invalid English party-name entry")
        raw = data[start + offset:start + offset + size]
        scenario.require(raw[-1] == 0, "Unterminated English party name")
        names.append(raw[:-1].decode("utf8"))
    return names


def command_text(result, command):
    """Return source text and a readable rendering; never invent runtime names."""
    op, words = command["opcode"], command["raw_u16"]
    if command["kind"] != "effect" or op not in (0x2F, 0x42, 0x43):
        return None
    group = "dialogue/ENG" if op == 0x43 else "messages/ENG"
    rows = result["texts"].get(group, [])
    row = next((r for r in rows if r["index"] == words[1]), None)
    if row is None:
        return dict(text=f"Text unavailable ({group}, entry {words[1]})", raw=None,
                    group=group, index=words[1], file_offset=None)
    text = row["text"]
    # The full-width prefix is a message category, not part of its instruction.
    text = re.sub(r"^（[^）]*）", "", text)
    text = re.sub(r"\[(?:r|b|g|y|w|/)\]", "", text)
    party_offset = {0x2F: 6, 0x42: 4}.get(op)
    def substitute(match):
        slot, kind = int(match.group(1)), match.group(2)
        if kind == "PARTY" and party_offset is not None and slot < 2:
            name_id = words[party_offset + slot]
            names = result["party_names"]
            if 0 <= name_id < len(names) and names[name_id] and names[name_id] != "DUMMY_ENG":
                return names[name_id]
        return f"[runtime {kind.lower()} {slot}]"
    text = re.sub(r"\[(\d+):([A-Z_]+)\]", substitute, text)
    return dict(text=text, raw=row["text"], group=group, index=row["index"], file_offset=row["file_offset"])


def objective_label(result, objective):
    events = result["behavior"]["events"]
    sources = result["script_writers"].get(("objective", objective), [])
    active = [(eid, pos) for eid, pos in sources if events[eid]["effects"][pos]["raw_u16"][3] == 2]
    titles = list(dict.fromkeys(command_text(result, events[eid]["effects"][pos])["text"]
                                for eid, pos in (active or sources)))
    return f"Objective {objective}" + (" - “" + "” / “".join(titles) + "”" if titles else " - description unavailable")


def event_objectives(event):
    ids = {c["raw_u16"][1] for c in event["conditions"] if c["opcode"] in (6, 7)}
    ids.update(c["raw_u16"][2] for c in event["effects"] if c["opcode"] == 0x2F)
    return ids


def objective_text_lines(result, objectives, debug=False):
    events, lines = result["behavior"]["events"], []
    for objective in sorted(objectives):
        lines += ["", objective_label(result, objective), "Text configured by objective commands:"]
        sources = result["script_writers"].get(("objective", objective), [])
        for eid, pos in sources:
            command = events[eid]["effects"][pos]
            state = OBJECTIVE_STATES.get(command["raw_u16"][3], "unidentified state")
            text = command_text(result, command)
            lines.append(f"  Event {eid} - {state}: {text['text']}")
            if debug:
                location = f"0x{text['file_offset']:X}" if text["file_offset"] is not None else "unavailable"
                lines += [f"    {text['group']}[{text['index']}], text file {location}; command 0x{command['file_offset']:X}",
                          f"    Stored text: {text['raw']}"]
        if sources:
            lines.append("Objective-command text is listed separately from message and dialogue commands below.")
        related = []
        for event in events:
            if objective not in event_objectives(event):
                continue
            for command in event["effects"]:
                if command["opcode"] not in (0x42, 0x43):
                    continue
                text = command_text(result, command)
                kind = "Dialogue" if command["opcode"] == 0x43 else "Message"
                related.append(f"  Event {event['ordinal']} - {kind}: {text['text']}")
                if debug:
                    related.append(f"    {text['group']}[{text['index']}]; command 0x{command['file_offset']:X}; stored: {text['raw']}")
        if related:
            lines += ["Messages in events checking or changing this objective (each event has its own conditions):"] + related
    return lines


def decode_command(command):
    """Semantic fields verified against initializers AND their consumers.

    Condition: 00=140d05c10/140d059b0, 04/05=140d054d0/140d05460,
    07=140d05280/140d05210, 09=140d05050/140d04ff0,
    0E=140d04a30/140d048a0, 0F=140d046e0/140d04640,
    15=140d04090/140d04040, 19=140d03a20/140d037c0.
    Effect: 00=140d17250/140d171b0, 02=140d16f40/140d16eb0,
    17=140d15a30, 22=140d0ceb0, 24=140d12420,
    57=140d0b910/140d0b8a0. Other parameters remain raw, not guessed.
    """
    w, op = command["raw_u16"], command["opcode"]
    decoded, used = {}, set()

    def field(index, name, value=None):
        decoded[name] = w[index] if value is None else value
        used.add(index)

    if command["kind"] == "condition":
        if op in (0xFE, 0xFF):
            decoded["logic"] = "AND" if op == 0xFF else "OR"
            field(1, "child_count")
        elif op in (4, 5):
            field(1, "paragraph")
            field(2, "required_state", "occurred" if op == 4 else "executed")
            decoded["expected"] = w[2] == 1
        elif op in (0, 0xE, 0xF):
            field(1, "entity" if op == 0 else "timer" if op == 0xE else "counter")
            value = (struct.unpack("<h", struct.pack("<H", w[2]))[0] if op == 0xF
                     else min(w[2], 5400) if op == 0xE else w[2])
            field(2, "threshold", value)
            field(3, "comparison", COMPARISONS.get(w[3], f"comparison {w[3]}"))
            if op == 0:
                field(4, "KO_category")
        elif op == 6:
            # 140d05380 / 140d052b0: objective state must be 1 (prepared),
            # then compare object+154 against +04, with +08 inversion.
            field(1, "objective")
            field(2, "prepared_value_threshold")
            field(3, "comparison", COMPARISONS.get(w[3], f"comparison {w[3]}"))
            field(4, "expected", bool(w[4]))
        elif op == 7:
            field(1, "objective")
            field(2, "state")
            field(3, "comparison", "=" if w[3] else "!=")
        elif op == 8:
            field(1, "result_category", w[1] & 255)
            field(2, "objective_category")
            field(3, "count")
            field(4, "comparison", COMPARISONS.get(w[4], f"comparison {w[4]}"))
        elif op == 9:
            field(1, "special_target_requirement")
            field(2, "succeeded", w[2] == 1)
        elif op == 0x15:
            field(1, "entity")
            field(2, "state_test")
            field(4, "expected", bool(w[4]))
        elif op == 0x19:
            field(1, "entity")
            field(2, "character_selector")
            field(3, "matches", w[3] == 1)
    else:
        if op == 0:
            field(1, "timer")
            field(2, "action", {0: "start", 1: "stop", 2: "reset", 3: "add", 4: "subtract"}.get(w[2], f"operation {w[2]}"))
            if w[2] in (3, 4):
                field(3, "seconds")
        elif op == 98:
            field(1, "lighting_clock_hours");field(2, "lighting_clock_minutes")
            decoded['lighting_fraction']=min(1.0,w[1]/24+w[2]/1440)
        elif op == 2:
            field(1, "counter")
            field(2, "value", struct.unpack("<h", struct.pack("<H", w[2]))[0])
            field(3, "action", {0: "set", 1: "add"}.get(w[3], f"operation {w[3]}"))
        elif op == 0x17:
            field(1, "reactivate_paragraph")
        elif op == 0x22:
            field(1, "entity")
            raw = struct.pack("<16H", *w)
            field(2, "x", struct.unpack_from("<i", raw, 4)[0])
            field(4, "z", struct.unpack_from("<i", raw, 8)[0])
            used.update((3, 5))
            field(7, "delay_seconds", w[7] / 60)
        elif op == 0x24:
            field(1, "entity")
            field(2, "target_entity")
        elif op == 0x2F:
            # 140d158d0 -> 140d144f0 -> 140cfb790. This changes objective
            # state; it does not directly call a dependent appearance event.
            field(1, "message_id")
            field(2, "objective")
            field(3, "state")
            decoded["state_name"] = OBJECTIVE_STATES.get(w[3], "unidentified")
        elif op == 0x30:
            # 140d144c0/140d143d0: mode 0 appends to the objective's target
            # list; other modes remove the unit via 140cfe240.
            field(1, "entity")
            field(2, "objective")
            field(3, "action", "add target" if w[3] == 0 else "remove target")
        elif op == 0x57:
            field(1, "special_target_requirement")
            field(2, "succeeded", w[2] == 1)
        elif op == 0x56:
            field(1, "special_target_condition_type")
            field(2, "parameter_a")
            field(3, "parameter_b")
            field(4, "requirement_slot")
    command["decoded"] = decoded
    command["fields"].update(decoded)
    for index in used:
        command["unresolved_u16"].pop(f"+0x{index * 2:02X}", None)


def unit_name(result, ordinal):
    records = result["behavior"]["entities"]
    if ordinal == len(records):
        return "the players"
    if 0 <= ordinal < len(records):
        record = records[ordinal]
        role = record["runtime_role_low_byte"]
        if role < 8:
            return f"Player {role + 1}"
        names = record["default_name_candidates"]
        return (names[0] if len(names) == 1 else "Soldier" if record["kind"] == "Character" else "Titan") + f" (#{ordinal})"
    return "a runtime-selected unit"


def build_script_writers(events):
    """Reverse index of serialized state writes, not a simulated call graph."""
    index = {}
    for event in events:
        for position, command in enumerate(event["effects"]):
            op, w = command["opcode"], command["raw_u16"]
            keys = []
            if op == 0x2F:
                keys = [("objective", w[2]), ("objective_state", w[2], w[3])]
            elif op == 0x30:
                keys = [("objective_targets", w[2])]
            elif op == 0:
                keys = [("timer", w[1])]
            elif op in (2, 3, 4):
                keys = [("counter", w[1])]
            elif op == 0x57:
                keys = [("special_requirement", w[1], w[2] == 1)]
            elif op == 0x17:
                keys = [("reactivate", w[1])]
            for key in keys:
                index.setdefault(key, []).append((event["ordinal"], position))
    return index


def script_dependencies(result, event):
    """Find the actual records supplying each known prerequisite."""
    writers = result["script_writers"]
    links = []
    parent = event["decoded_header"]["parent_paragraph"]
    events = result["behavior"]["events"]
    if parent != event["ordinal"] and 0 <= parent < len(events):
        if events[parent]["decoded_header"]["initial_flags"] & 4:
            links.append(("Parent condition group", parent, None))
    for condition in evaluated_conditions(event):
        op, w = condition["opcode"], condition["raw_u16"]
        candidates, reason = [], ""
        if op in (4, 5):
            if w[1] < len(events):
                links.append(("Referenced event must " + ("have" if w[2] else "not have") +
                              (" started" if op == 4 else " executed"), w[1], None))
        elif op in (6, 7):
            reason = f"Script writes objective {w[1]}"
            candidates = writers.get(("objective", w[1]), [])
            if op == 7:
                candidates = [(eid, pos) for eid, pos in candidates
                              if (events[eid]["effects"][pos]["raw_u16"][3] == w[2]) == bool(w[3])]
        elif op in (0xE, 0xF):
            kind = "timer" if op == 0xE else "counter"
            reason = f"Script writes {kind} {w[1]}"
            candidates = writers.get((kind, w[1]), [])
        elif op == 9:
            reason = (f"Script satisfies special-target requirement {w[1]}" if w[2] == 1 else
                      f"Script writes a non-success state to special-target requirement {w[1]}")
            candidates = writers.get(("special_requirement", w[1], w[2] == 1), [])
        elif op == 8:
            reason = "Script changes an objective included in the result count"
            for key, sources in writers.items():
                if key[0] != "objective_state":
                    continue
                _, objective, state = key
                scope = w[2]
                if (scope == 0 and objective >= 10) or (scope == 1 and objective < 10):
                    continue
                states = {0: (3,), 1: (4,), 2: (3, 4)}.get(w[1] & 255, ())
                if state in states:
                    candidates.extend(sources)
        links.extend((reason, eid, pos) for eid, pos in candidates)
    links.extend(("Script reactivates this event", eid, pos)
                 for eid, pos in writers.get(("reactivate", event["ordinal"]), []))
    return list(dict.fromkeys(links))


def evaluated_conditions(event):
    """Only nodes consumed by the native condition tree, excluding trailing data."""
    def walk(node):
        if node is None:
            return
        if "operator" in node:
            for child in node["children"]:
                yield from walk(child)
        else:
            yield node["command"]
    return list(walk(event["condition_tree"]))


def verified_state_links(result, event):
    """Join actual objective writes to evaluated reads of the same slot/value.

    This proves the serialized data-flow edge. AND/OR placement remains in the
    full requirement tree; one satisfied leaf is never called the whole trigger.
    """
    events, links = result["behavior"]["events"], []
    for condition in evaluated_conditions(event):
        if condition["opcode"] != 7:
            continue
        words = condition["raw_u16"]
        for eid, position in result["script_writers"].get(("objective", words[1]), []):
            effect = events[eid]["effects"][position]
            state = effect["raw_u16"][3]
            if (state == words[2]) == bool(words[3]):
                links.append(dict(source_event=eid, effect_index=position, writer=effect,
                                  reader=condition, objective=words[1], written_state=state))
    return links


def script_proof_lines(result, event, debug=False):
    links = verified_state_links(result, event)
    lines = []
    if links:
        lines += ["", "VERIFIED OBJECTIVE STATE LINKS"]
        for link in links:
            writer, reader = link["writer"], link["reader"]
            state = OBJECTIVE_STATES.get(link["written_state"], str(link["written_state"]))
            comparison = "==" if reader["raw_u16"][3] else "!="
            lines += [f"Event {link['source_event']} writes objective {link['objective']} = {link['written_state']} ({state}); "
                      f"this satisfies Event {event['ordinal']}'s objective-state check.",
                      f"  BIN write: effect[{link['effect_index']}] at 0x{writer['file_offset']:X}, "
                      f"opcode 0x2F, +04={link['objective']}, +06={link['written_state']}.",
                      f"  BIN read: condition at 0x{reader['file_offset']:X}, opcode 0x07, "
                      f"+02={link['objective']}, +04={reader['raw_u16'][2]}, +06={reader['raw_u16'][3]} "
                      f"(state {comparison} {reader['raw_u16'][2]}).",
                      "  EXE write: FUN_140d144f0 selects objective[slot] at 0x140D1513B; "
                      "FUN_140cfb790 stores state at objective+08 (0x140CFB7E8).",
                      "  EXE read: FUN_140d05210 selects objective[slot] at 0x140D05238, "
                      "reads the same +08 field at 0x140D0524E, and compares at 0x140D05256."]
        lines.append("The full AND/OR trigger is shown under Activation requirements above.")
    lines += ["", "VERIFIED EXECUTION PATH",
              "FUN_140d01450 scans events and calls FUN_140d1b6e0 at 0x140D01529 to evaluate their conditions.",
              "For queued events, the successful branch calls FUN_140cf9360 at 0x140D01838; "
              "the queue stores the event at 0x140CF97C4.",
              "The queue invokes CScParagraph::vtable+20 at 0x140CEA40B, which points to FUN_140d1b130.",
              "Before starting, FUN_140d1b130 rechecks the condition tree via FUN_140d1a900 at 0x140D1B145; "
              "its passing path reaches FUN_140d1b8a0 at 0x140D1B171.",
              "FUN_140d1b8a0 invokes each enabled effect's activation callback through vtable+28 at 0x140D1BA34."]
    flags = event["decoded_header"]["initial_flags"]
    if not flags & (1 | 2 | 4 | 8 | 0xF0):
        lines.append(f"Event {event['ordinal']} starts with flags 0x{flags:02X}: it uses the condition-check / queued-event path.")
    elif flags & 2 and not flags & 4:
        lines.append(f"Event {event['ordinal']} has immediate-execution flag 0x02: "
                     "after its conditions pass, the scheduler calls FUN_140d1b8a0 at 0x140D01808.")
    for pos, effect in enumerate(event["effects"]):
        if effect["opcode"] != 0x19:
            continue
        words = effect["raw_u16"]
        lines.append(f"Event {event['ordinal']} effect[{pos}] at 0x{effect['file_offset']:X}: "
                     f"CScEffCorpsAppear target #{words[1]}, delay {words[2]}/60 seconds.")
    if any(effect["opcode"] == 0x19 for effect in event["effects"]):
        lines += ["Appearance: FUN_140d0eb40 -> FUN_140d0eae0 -> FUN_140d0ea80 -> FUN_140a4e5e0.",
                  "The final instruction at 0x140A4E61C clears hidden bit 0x20 on the resolved entity; "
                  "the per-unit handler checks that the entity exists and is hidden first."]
    if debug:
        lines += ["", "CHECKED EXE INSTRUCTIONS (preferred virtual addresses)"]
        lines += [f"0x{proof['address']:X}: {proof['bytes']} - {proof['description']}"
                  for proof in result["native_proof"]]
    return lines


def callback_lines(command):
    evidence = command.get("executable_evidence")
    if not evidence:
        return ["Executable callback not identified for this command."]
    lines = [evidence["class_name"]]
    roles = (["condition evaluator", "per-unit test"] if command["kind"] == "condition"
             else ["effect activation", "delayed update", "per-unit application"])
    # Shared no-op virtual methods are not meaningful execution callbacks.
    stubs = {0x14018EB90, 0x1401915C0, 0x1401915D0, 0x1401915F0}
    for role in roles:
        address = evidence["callbacks"][role]
        if address not in stubs:
            lines.append(f"  {role}: FUN_{address:x}")
    if command["kind"] == "effect" and command["opcode"] == 0x19:
        # Confirmed static call chain in the fingerprinted executable:
        # 140d1b8a0's call site 140d1ba34 invokes vtable+28; activation
        # 140d0eb40 invokes/enqueues update 140d0eae0; update resolves the unit
        # with 140d17490 then invokes +18 (140d0ea80). That tail-calls
        # 140a4e5e0, which clears hidden bit 0x20 at 140a4e61c.
        lines += ["  Caller: FUN_140d1b8a0 (effect executor), call site 0x140D1BA34",
                  "  Activation path: FUN_140d0eb40 -> FUN_140d0eae0 -> FUN_140d0ea80 -> FUN_140a4e5e0",
                  "  FUN_140a4e5e0 clears the unit's hidden flag; nonzero delays use the update queue."]
    elif command["kind"] == "effect" and command["opcode"] == 0x2F:
        lines.append("  State update: FUN_140d144f0 -> FUN_140cfb790")
    elif command["kind"] == "condition" and command["opcode"] == 8:
        lines.append("  Result counters updated by FUN_140cfb790: completed state 3 / failed state 4; main slots <10 / side slots >=10.")
    return lines


def script_trace_lines(result, event_id, debug=False):
    events = result["behavior"]["events"]
    event = events[event_id]
    lines = [f"Event {event_id} - embedded scenario script",
             f"Script file: {result['source']}",
             f"Script section 6, event record at file 0x{event['file_offset']:X}",
             "", "ACTIVATION REQUIREMENTS"] + requirement_lines(result, event_id)
    lines += script_proof_lines(result, event, debug)
    lines += ["", "SCRIPT REFERENCES - click an Event to inspect it",
              "Objective triggers use shared state: a script writes the objective state, and the scheduler evaluates the receiving event's condition."]
    dependencies = script_dependencies(result, event)
    for reason, other, position in dependencies:
        source = events[other]
        label = f"{reason}: Event {other}, file 0x{source['file_offset']:X}"
        if position is not None:
            effect = source["effects"][position]
            label += f", effect[{position}] at 0x{effect['file_offset']:X} - {command_description(effect, result)}"
        lines.append(label)
    if not dependencies:
        lines.append("No matching serialized state writes or event references in this scenario.")
    objectives = {c["raw_u16"][1] for c in event["conditions"] if c["opcode"] in (6, 7)}
    objectives.update(c["raw_u16"][2] for c in event["effects"] if c["opcode"] in (0x2F, 0x30))
    for objective in sorted(objectives):
        targets = result["script_writers"].get(("objective_targets", objective), [])
        if targets:
            lines += ["", f"MARKED TARGET ASSIGNMENTS - objective {objective}"]
            for other, position in targets:
                command = events[other]["effects"][position]
                lines.append(f"Event {other}, effect[{position}] at 0x{command['file_offset']:X}: {command_description(command, result)}")
    lines += ["", "SCRIPT ACTIONS"]
    for position, command in enumerate(event["effects"]):
        lines.append(f"effect[{position}] at 0x{command['file_offset']:X}: {command_description(command, result)}")
        if debug and command["fields"]:
            lines.append(f"  Decoded: {command['fields']}")
    lines += objective_text_lines(result, objectives, debug)
    lines += ["", "EXECUTABLE CALLBACKS",
              f"Executable: {Path(result.get('editor_game_root') or scenario.resolve_game_root(result['source'])) / 'AOT2_EU.exe'}",
              "Class names come from EXE RTTI. FUN_<address> identifies an address; original method names are unavailable.",
              "Addresses are preferred virtual addresses (image base 0x140000000), not BIN file offsets.",
              "Condition-tree evaluator: FUN_140d1a900; effect executor: FUN_140d1b8a0."]
    seen = set()
    for command in event["conditions"] + event["effects"]:
        key = (command["kind"], command["opcode"])
        if key in seen or command["opcode"] in (0xFE, 0xFF):
            continue
        seen.add(key)
        lines += callback_lines(command)
    lines += ["", f"Verification: loaded scenario records and {len(result['native_proof'])} checked EXE instruction spans.",
              f"EXE SHA-256: {EXE_SHA256}"]
    return lines


def activation_lines(result, entity):
    lines = ["", "ACTIVATION SCRIPT / CALLBACK"]
    for appearance in entity["appearance_events"]:
        event_id = appearance["paragraph"]
        event = result["behavior"]["events"][event_id]
        file_offset = appearance.get("effect_file_offset", appearance.get("raw", {}).get("file_offset"))
        effect = next((c for c in event["effects"] if c["file_offset"] == file_offset), None)
        lines += [f"Event {event_id}: {result['source']}",
                  f"Script record 0x{event['file_offset']:X}; appearance command 0x{file_offset:X}"]
        lines += ["  " + text for text in requirement_lines(result, event_id)]
        for reason, other, position in script_dependencies(result, event):
            if position is not None:
                command = result["behavior"]["events"][other]["effects"][position]
                lines.append(f"  {reason}: Event {other}, effect[{position}] at 0x{command['file_offset']:X} - {command_description(command, result)}")
        if effect:
            lines += callback_lines(effect)
    if not entity["appearance_events"]:
        lines.append("No serialized appearance command found; a native activation callback has not been traced for this unit.")
    else:
        lines.append("Open the Script trace tab to follow linked events and prerequisite scripts.")
    return lines


def command_description(command, result):
    op, w, d = command["opcode"], command["raw_u16"], command["decoded"]
    if command["kind"] == "condition":
        if op in (4, 5):
            verb = "started" if op == 4 else "executed its actions"
            return f"Event {w[1]} has {'not ' if not d['expected'] else ''}{verb}"
        if op in (0xE, 0xF):
            noun = "Timer" if op == 0xE else "Counter"
            return f"{noun} {w[1]} {d['comparison']} {d['threshold']}" + (" seconds" if op == 0xE else "")
        if op == 0:
            category = "KO count" if w[4] == 0 else "category-specific KO count"
            return f"{unit_name(result, w[1])}: {category} {d['comparison']} {d['threshold']}"
        if op == 9:
            return f"Special-target requirement {w[1]} {'succeeded' if d['succeeded'] else 'has not succeeded'}"
        if op == 6:
            return f"{objective_label(result, w[1])}: {'meets' if d['expected'] else 'does not meet'} its preparation check"
        if op == 7:
            state = OBJECTIVE_STATES.get(w[2], f"in state {w[2]} (meaning unverified)")
            return f"{objective_label(result, w[1])} {'is' if w[3] else 'is not'} {state}"
        if op == 8:
            result_name = {0: "Completed", 1: "Failed", 2: "Completed or failed"}.get(d["result_category"], "Unidentified results for")
            scope = {0: "main objectives", 1: "side objectives"}.get(d["objective_category"], "main and side objectives")
            return f"{result_name} {scope}: count {d['comparison']} {d['count']}"
        if op == 0x15:
            if w[2] == 0:
                return f"{unit_name(result, w[1])} must {'not ' if not d['expected'] else ''}be active"
            return f"{unit_name(result, w[1])}: {'meets' if d['expected'] else 'does not meet'} a status check (status meaning not yet identified)"
        if op == 0x19:
            names = sorted({name for record in result["behavior"]["entities"]
                            if record["entity_selector"] == w[2]
                            for name in record["default_name_candidates"]})
            identity = " / ".join(names) if names else f"character selection {w[2]}"
            return f"{unit_name(result, w[1])} {'matches' if d['matches'] else 'does not match'} {identity}"
        if op == 0xA:
            return f"{unit_name(result, w[1])} enters the specified map area"
    else:
        if op == 98:
            return (f'Set the lighting clock to {w[1]:02}:{w[2]:02} within the current environment preset. '
                    'This changes lighting; it does not select a different weather preset.')
        if op == 0:
            return f"{d['action'].capitalize()} timer {w[1]}" + (f" by {d['seconds']} seconds" if "seconds" in d else "")
        if op == 2:
            return (f"Set counter {w[1]} to {d['value']}" if d["action"] == "set"
                    else f"Add {d['value']} to counter {w[1]}" if d["action"] == "add"
                    else f"Counter {w[1]}: {d['action']}")
        if op == 0x17:
            return f"Reactivate event {w[1]}"
        if op in (0x19, 0x1B, 0x1C):
            description="Make " + unit_name(result, w[1]) + " appear on the map"
            if op==0x19:description+=f" after {w[2]/60:g} seconds" if w[2] else " without a delay"
            elif op==0x1B:description+=f" using the placement around {unit_name(result,w[5])}" if w[2]==1 else f" using map cell ({w[3]}, {w[4]})"
            else:description+=f" relative to {unit_name(result,w[2])}, at a distance of {w[3]} cells, after {w[8]/60:g} seconds"
            return description
        if op == 0x1D:
            return "Remove " + unit_name(result, w[1])
        if op == 0x22:
            return f"Move {unit_name(result, w[1])} to ({d['x']}, {d['z']})"
        if op == 0x24:
            return f"Set {unit_name(result, w[1])}'s target to {unit_name(result, w[2])}"
        if op == 0x23:
            return f"Assign behavior preset {w[2]} to {unit_name(result,w[1])}. The actions defined by this preset have not been decoded."
        if op == 0x25:
            x,z=command['fields']['target_cell_center_xz']
            return f"Set {unit_name(result,w[1])}'s destination to map cell ({w[2]}, {w[3]}), world position X={x}, Z={z}. This changes its target, not its stored spawn position."
        if op == 0x2D:
            return f"Configure the route line for {unit_name(result,w[1])}, referencing {unit_name(result,w[3])} and map cell ({w[4]}, {w[5]})."
        if op == 0x38:
            # 140D115A0 reads +02 as an adjusted unit ordinal; 140D114F0
            # places the flare at that unit's cell and updates its HUD marker.
            return f"Request a flare signal at {unit_name(result,w[1])}'s location and update its map indicator."
        if op == 0x52:
            return 'Configure the battle victory or defeat requirements. This sets up a result rule; it is not a declaration that the battle has ended.'
        if op == 0x53:
            return f"Include {unit_name(result,w[2])} in a battle victory or defeat requirement."
        if op == 0x6B:
            return f"Start scripted situation {w[1]}. Its internal sequence is separate from the actions listed in this event."
        if op == 0x2F:
            return f"Set {objective_label(result,w[2])} to {OBJECTIVE_STATES.get(w[3], 'state ' + str(w[3]))}. Objective text: {command_text(result, command)['text']}"
        if op in (0x42, 0x43):
            return ("Dialogue: " if op == 0x43 else "Message: ") + command_text(result, command)["text"]
        if op == 0x30:
            return f"{'Add' if w[3] == 0 else 'Remove'} {unit_name(result, w[1])} {'to' if w[3] == 0 else 'from'} the marked targets for {objective_label(result,w[2])}"
        if op == 0x57:
            return f"Mark special-target requirement {w[1]} as {'successful' if d['succeeded'] else 'failed'}"
        if op == 0x56:
            return f"Configure special-target requirement {w[4]}"
    class_name = command.get("class_name", command["label"])
    title = re.sub(r"^CSc(?:Cond|Eff)", "", class_name)
    title = re.sub(r"([a-z])([A-Z])", r"\1 \2", title)
    title = title.replace("Corps", "Unit").replace("Facility", "Base").replace("Msg", "Message")
    title=COMMAND_TITLES.get(command['kind'],{}).get(op,title)
    references=list(dict.fromkeys(unit_name(result,ref['raw']) for ref in command.get('entity_references',{}).values()))
    return title + ('. Affected units: '+', '.join(references) if references else '') + '. Detailed settings have not been decoded.'


def requirement_lines(result, event_id, expand_special=True):
    events = result["behavior"]["events"]
    lines = []

    def render(node, indent):
        if node is None:
            lines.append(indent + "No serialized conditions")
            return
        command = node["command"]
        if "operator" in node:
            if not node["children"]:
                lines.append(indent + ("No additional condition" if node["operator"] == "all" else "Empty ANY group (false)"))
                return
            lines.append(indent + ("All of:" if node["operator"] == "all" else "Any of:"))
            for child in node["children"]:
                render(child, indent + "  ")
        else:
            lines.append(indent + command_description(command, result))
            if expand_special and command["opcode"] == 9 and command["decoded"]["succeeded"]:
                sources = result["special_target_rules"].get(command["raw_u16"][1], [])
                for source_id in sources:
                    lines.append(indent + "  Success rule:")
                    lines.extend(indent + "    " + line for line in requirement_lines(result, source_id, False))

    # Parent-group gating is additional to the selected event's own conditions.
    # Stop cycles in user-edited scenarios instead of recursively hanging the UI.
    ancestors, seen = [], {event_id}
    parent = events[event_id]["decoded_header"]["parent_paragraph"]
    while parent and parent not in seen and 0 <= parent < len(events):
        seen.add(parent)
        group = events[parent]
        if not group["decoded_header"]["initial_flags"] & 4:
            break
        ancestors.append(group)
        parent = group["decoded_header"]["parent_paragraph"]
    for group in reversed(ancestors):
        lines.append("Parent group requirements:")
        render(group["condition_tree"], "  ")
    render(events[event_id]["condition_tree"], "")
    if events[event_id]["trailing_conditions"]:
        lines.append("Additional condition records lie outside the evaluated group; see Debug mode.")
    return lines


def world_to_image(x, z, anchors, world_anchors):
    (x0, z0), (x1, z1) = world_anchors
    (u0, v0), (u1, v1) = anchors
    return (u0 + (x - x0) * (u1 - u0) / (x1 - x0),
            v0 + (z - z0) * (v1 - v0) / (z1 - z0))


def exe_resource_ids(path, minimap_id):
    """Read texture IDs from PE sections, not fixed IDs or saved extraction data."""
    data = path.read_bytes()
    scenario.require(hashlib.sha256(data).hexdigest() == EXE_SHA256,
                     "Unsupported AOT2_EU.exe build; map-table offsets must be verified for this executable.")
    pe = scenario.u32(data, 0x3C)
    scenario.require(data[:2] == b"MZ" and data[pe:pe + 4] == b"PE\0\0", "Invalid game executable")
    section_count = scenario.unpack("<H", data, pe + 6)[0]
    optional_size = scenario.unpack("<H", data, pe + 20)[0]
    scenario.require(scenario.unpack("<H", data, pe + 24)[0] == 0x20B, "Expected a PE32+ executable")
    directory = pe + 24 + optional_size
    ids = {}
    for kind, table_rva in TEXTURE_TABLE_RVAS.items():
        rva = table_rva + minimap_id * 4
        for i in range(section_count):
            _, section_rva, raw_size, raw_offset = scenario.unpack("<4I", data, directory + i * 40 + 8)
            if section_rva <= rva and rva + 4 <= section_rva + raw_size:
                ids[kind] = scenario.u32(data, raw_offset + rva - section_rva)
                break
        scenario.require(kind in ids, f"{kind} map table is outside executable sections")
    return ids


def read_texture_resource(root, resource_id):
    # Global base resource IDs are concatenated A/B/C directory indices.
    # Sizes and payload offsets come from the archive directory, never sidecars.
    remaining = resource_id
    for letter in ("A", "B", "C"):
        path = root / f"LINKDATA/LINKDATA_{letter}.BIN"
        with path.open("rb") as archive:
            magic, count, unit, _ = scenario.unpack("<4I", archive.read(16))
        scenario.require(magic == 0x77DF9 and unit == 256, f"Unsupported archive: {path}")
        if 0 <= remaining < count:
            return scenario.read_name_resource(path, remaining)
        remaining -= count
    raise ValueError(f"Texture resource {resource_id} is outside the base archive directories")


def decode_g1t(data):
    """Decode this game's single-mip PC BC7 minimaps entirely in memory."""
    scenario.require(data[:8] == b"GT1G0600", "Unsupported minimap G1T signature/version")
    total, table_offset, count, platform = scenario.unpack("<4I", data, 8)
    scenario.require(total == len(data) and count == 1 and platform == 10,
                     "Unsupported minimap G1T size/count/platform")
    scenario.require(28 <= table_offset <= len(data) - 4, "Invalid G1T texture directory")
    texture = table_offset + scenario.u32(data, table_offset)
    scenario.require(table_offset + 4 <= texture <= len(data) - 20, "Invalid G1T texture offset")
    mip_flags, fmt, dimensions, _ = scenario.unpack("<4B", data, texture)
    scenario.require(mip_flags == 0x10 and fmt == 0x5F and data[texture + 7] == 0x10,
                     "Expected a single-mip BC7 minimap with an extended texture header")
    width, height = 1 << (dimensions & 15), 1 << (dimensions >> 4)
    scenario.require(4 <= width <= 8192 and 4 <= height <= 8192, "Invalid minimap dimensions")
    extension_size = scenario.u32(data, texture + 8)
    scenario.require(extension_size == 12, "Unsupported G1T extended header")
    start = texture + 8 + extension_size
    size = ((width + 3) // 4) * ((height + 3) // 4) * 16
    scenario.require(start + size == len(data), "BC7 pixel-block size does not match minimap dimensions")
    # A DDS header lets Pillow decode the original BC7 blocks. BytesIO is RAM;
    # neither the DDS wrapper nor the decoded image is ever written to disk.
    header = struct.pack("<31I", 124, 0x81007, height, width, size, 0, 1,
                         *([0] * 11), 32, 4, 0x30315844, 0, 0, 0, 0, 0,
                         0x1000, 0, 0, 0, 0)
    dx10 = struct.pack("<5I", 98, 3, 0, 1, 0)  # BC7_UNORM, TEXTURE2D, one layer
    with Image.open(BytesIO(b"DDS " + header + dx10 + data[start:])) as image:
        rgba = image.convert("RGBA")
        pixels = rgba.tobytes()
    return QImage(pixels, width, height, width * 4, QImage.Format.Format_RGBA8888).copy()


# Initial side assignment from FUN_140a4fb60 (object byte +0x162):
# definition +06 low byte -> deployment +0E -> role at object +0x164.
# Roles 0..7 (players) and 8 map to team 0; 9 -> 1; 10 -> 2; others -> 3.
# This is independent of human/Titan templates, category and display names.
# Team 0 is the initial player side. Other teams are labelled numerically:
# this static preview does not reconstruct the alliance matrix or script changes.
TEAM_COLORS = {0: "#55a2ff", 1: "#ff525c", 2: "#af82ff", 3: "#bfc5cf"}
TEAM_LABELS = {0: "Player side (blue)", 1: "Red team",
               2: "Purple team", 3: "Gray team"}
BASE_COLOR = "#ff9c36"
TEAM_LEGEND = ("Blue: player side • Red/purple/gray: other teams • Orange circles: bases. "
               "Filled: active at start • Hollow: inactive or dependent on party selection.")


def initial_team(role_u16):
    role = role_u16 & 0xFF
    return 0 if role <= 8 else 1 if role == 9 else 2 if role == 10 else 3


class InstalledNameResolver(scenario.BinaryNameResolver):
    """Use the installed selector catalog, retaining embedded snapshots for Debug.

    EU EXE: call site 0x140B67D3D invokes FUN_140b67910 after loading resource 2
    (DataCharaSet.bin, remapped to PATCH entry 1). The loader stores 1001
    descriptors at data-object +0x1C724. FUN_140a4ff59..140a4ff87 reads
    manager +0x134 +0x1C724 + selector*6 when creating a deployment, then
    FUN_140a500da chooses its human template. The old scenario section 4
    is not a second list of names to union with this installed descriptor.
    Templates: PATCH entry 0; English name strings: REGION entry 3.
    """
    def __init__(self,templates,selectors,text,scenario_selectors):
        super().__init__(templates,selectors,text,scenario_selectors)
        # Human loader 140B675D8 copies disk +4 to template +4.
        # Deployment 140A501B0 reads it; 140A502E2..140A502FB selects
        # equipment mode 2 for combat presets 0x4A..0x4C, otherwise mode 1
        # unless template +0x26 is 9. 140A50590 stores mode at entity +0x146.
        # This branch does not test team (+0x162). These are template defaults,
        # not a new per-scenario weapon field or a simulated player loadout.
        self.human_equipment=[('Guns' if struct.unpack_from('<H',templates,i*36+4)[0] in (0x4A,0x4B,0x4C)
                               else 'Blades' if templates[i*36+34]!=9 else '') for i in range(353)]

    def equipment_label(self,selector):
        mapping=self.resolve(selector)['active_mapping']
        if mapping.get('family')!='human':return ''
        kinds={self.human_equipment[i] for i in mapping['template_ids']}
        return next(iter(kinds)) if len(kinds)==1 else ''

    def resolve(self,selector):
        resolved=super().resolve(selector)
        if 'active_mapping' not in resolved:
            active=resolved['global_mapping'];names=[];unresolved=[]
            for name_id in active['name_ids']:
                if name_id in (0x43,0xFF,0xFFFF) or name_id>=len(self.names) or self.names[name_id] in ('','DUMMY_ENG'):
                    unresolved.append(name_id)
                elif self.names[name_id] not in names:names.append(self.names[name_id])
            resolved.update(active_mapping=active,candidate_name_ids=list(active['name_ids']),candidate_names=names,
                            unresolved_or_runtime_name_ids=unresolved,
                            note='Installed DataCharaSet template selection and binary-derived names. Runtime player/party substitution can change identity.')
        return resolved


def apply_installed_names(result,game_root,snapshot):
    templates,selectors,text,sources=scenario.game_name_resources(str(game_root))
    resolver=InstalledNameResolver(templates,selectors,text,snapshot);resolver.sources=sources
    for entity in result['behavior']['entities']:
        resolution=copy.deepcopy(resolver.resolve(entity['entity_selector']))
        active=resolution['active_mapping'];player=entity['runtime_role_low_byte']<8
        entity['name_resolution']=resolution
        entity['default_name_candidates']=[] if player else list(resolution['candidate_names'])
        entity['kind']='Player slot (runtime identity)' if player else {'human':'Character','titan':'Titan'}.get(active.get('family'),'Unresolved')
        entity['titan_possible']=not player and active.get('family')=='titan'


# V1.8 uses the same parser and binary name provenance as find_v5B.
# Importing the analyzer does not run its CLI or write reports.
def read_entities(result):
    entities = []
    missing = 0
    for record in result["behavior"]["entities"]:
        if not record["placements"]:
            missing += 1
            continue
        placement = record["placements"][0]  # Same first-match join as the loader.
        resolution = record["name_resolution"]
        candidates = record["default_name_candidates"]
        kind = record["kind"]
        runtime = bool(resolution["unresolved_or_runtime_name_ids"])
        mapping = resolution["global_mapping"]
        group = mapping.get("group_id")
        if len(candidates) == 1 and not runtime and (resolution.get("active_mapping") is not None or resolution["mappings_agree"]):
            name = candidates[0]
        elif candidates:
            name = "Soldier" if kind == "Character" else kind
        elif runtime:
            name = "Soldier" if kind == "Character" else kind
        else:
            name = "Soldier" if kind == "Character" else kind
        hidden = record["initial_hidden_bit_0x20"]
        role = record["runtime_role_low_byte"]
        slot_type = None
        note = resolution["note"]
        activation_ids = sorted({a["paragraph"] for a in record["appearance_events"]})
        state_note = ("Initially hidden; activation scripts: " + ", ".join(f"Event {eid}" for eid in activation_ids)
                      if hidden and activation_ids else
                      "Initially hidden; no serialized appearance command found." if hidden else
                      "Initial hidden flag clear; not a live spawn count.")
        if role < 8:
            kind = slot_type = "Player"
            name = f"Player {role + 1}"
            state_note = ("Selected player character is assigned at runtime." if role == 0 else
                          "Occupied only when this slot is below the runtime participant count; otherwise hidden.")
        elif 8 <= record["ordinal"] < 12 and hidden:
            kind = slot_type = "Companion"
            name = f"Companion {record['ordinal'] - 7}"
            note = "Can receive a selected party member from runtime/save state; that identity is not stored here."
        entities.append(dict(index=record["ordinal"], selector=record["entity_selector"],
                             kind=kind, name=name, candidate_names=candidates,
                             initial_team=initial_team(record["role_u16"]),
                             xyz=placement["xyz"], heading=placement["heading_degrees"],
                             role=record["role_u16"], category=record["category_u16"],
                             initial_state=record["initial_state_u16"], initially_hidden=hidden,
                             slot_type=slot_type, state_note=state_note, resolution_note=note,
                             titan_possible=record["titan_possible"],
                             appearance_events=record["appearance_events"],
                             disappearance_events=record["disappearance_events"],
                             record=record))
    bases, missing_bases = read_bases(result)
    entities.extend(bases)
    for entity in entities:
        entity["conditional"] = entity["initially_hidden"] or (
            entity["slot_type"] == "Player" and (entity["role"] & 255) > 0)
        entity["marker_label"] = (entity["name"] if entity["kind"] == "Base"
                                  else f"#{entity['index']} {entity['name']}")
        entity["short_label"] = (f"B{entity['base_ordinal'] + 1}" if entity["kind"] == "Base"
                                 else f"#{entity['index']}")
    return entities, missing + missing_bases, result


def read_bases(result):
    """Keep binary evidence available for Debug mode; normal info stays readable.

    EU executable: FUN_140ce6ec0 pairs group-2 placements and secondary
    definitions by ORDINAL (not by join key). FUN_140ce6ad0 reads placement
    +04/+06 as unsigned x/z * 100; definition +04 is the initial facility type.
    FUN_140a73c20 calls facility activation FUN_140a722b0 only for type < 100.
    Definition +06..+0C are bit INDEXES, not the entity hidden-state field.
    FUN_140a59a30 snaps these positions to the nearest stage facility anchor;
    this preview displays the scenario's stored position, as it does for units.
    """
    placements = result["placements"]["groups"][2]
    bases, missing = [], 0
    for record in result["behavior"]["secondary_definitions"]:
        ordinal = record["ordinal"]
        if ordinal >= len(placements):
            missing += 1
            continue
        placement = placements[ordinal]
        x, z = struct.unpack_from("<HH", bytes.fromhex(placement["raw_hex"]), 4)
        initial_type = record["raw_u16"]["+0x04"]
        bases.append(dict(index=-(ordinal + 1), base_ordinal=ordinal,
                          kind="Base", name=f"Base {ordinal + 1}",
                          xyz=(x * 100, 0, z * 100), initial_team=None,
                          initially_hidden=initial_type >= 100, slot_type=None,
                          role=0, titan_possible=False, candidate_names=[],
                          appearance_events=[], disappearance_events=[],
                          record=record, placement=placement))
    return bases, missing


def preview_events(result, entities):
    # Original events, offsets and operands remain in result and each command.
    events = {e["paragraph"]: dict(e, appearances=list(e["appearances"]))
              for e in result["titan_spawns"]["events"]}
    bases = {e["base_ordinal"]: e for e in entities if e["kind"] == "Base"}
    for source in result["behavior"]["events"]:
        for effect in source["effects"]:
            if effect["opcode"] != 0x1A:
                continue
            # CScEffFacilityAppear: FUN_140d0ea40 reads target +02, type +04,
            # delay +06 / 60. Target is before the runtime base adjustment.
            words = effect["raw_u16"]
            base = bases.get(words[1])
            command = dict(paragraph=source["ordinal"], opcode=0x1A,
                           entity_ordinal=base["index"] if base else None,
                           delay_seconds=words[3] / 60, raw=effect)
            event = events.setdefault(source["ordinal"],
                                      dict(paragraph=source["ordinal"], appearances=[], raw=source))
            event["appearances"].append(command)
            if base:
                base["appearance_events"].append(command)
    by_id = {e["index"]: e for e in entities}
    labels = {}
    for key, event in sorted(events.items()):
        targets = {a["entity_ordinal"] for a in event["appearances"]}
        counts = {}
        for target in targets:
            entity = by_id.get(target)
            category = ("base" if entity and entity["kind"] == "Base" else
                        "Titan" if entity and entity["titan_possible"] else
                        "character" if entity else "unmapped target")
            counts[category] = counts.get(category, 0) + 1
        parts = [f"{n} {kind}{'s' if n != 1 else ''}" for kind, n in counts.items()]
        label = "Appear: " + ", ".join(parts)
        mapped = [by_id[target] for target in sorted(t for t in targets if t is not None)
                  if target in by_id]
        if len(mapped) == 1:
            label += " - " + mapped[0]["name"]
        teams = sorted({e["initial_team"] for e in mapped if e["kind"] != "Base"})
        if teams:
            label += " - " + ", ".join(TEAM_LABELS[team] for team in teams)
        source = result["behavior"]["events"][key]
        if any(c["opcode"] == 9 for c in source["conditions"]):
            label += " - Special-target requirements"
        labels[label] = labels.get(label, 0) + 1
        # Display numbering only disambiguates equal summaries, not script IDs/order.
        event["display_name"] = label + (f" ({labels[label]})" if labels[label] > 1 else "")
    return dict(sorted(events.items()))


class PreviewMapView(QWidget):
    details_requested = Signal(object)
    zoom_changed = Signal(float)

    def __init__(self, entities, backgrounds, parent=None):
        super().__init__(parent)
        self.entities = entities
        self.backgrounds = backgrounds
        self.image_label = next(iter(IMAGE_OPTIONS))
        self.text_mode = "Full"
        self.zoom = 1.0
        self.pan = QPointF()
        self.drag_position = None
        self.hovered = None
        self.hit_regions = []
        self.visible_ids = None
        self.setMouseTracking(True)
        self.setMinimumSize(300, 250)
        self.setAttribute(Qt.WidgetAttribute.WA_OpaquePaintEvent)
        self.label_font = QFont("Segoe UI", 9, QFont.Weight.Bold)
        self.markers = []
        # Cache text layout once. Painting never recreates widgets or resamples
        # a full image through Pillow; Qt draws the original cached QPixmap.
        for entity in entities:
            color = QColor(BASE_COLOR if entity["kind"] == "Base" else TEAM_COLORS[entity["initial_team"]])
            conditional = entity["conditional"]
            texts = {}
            for mode, label in (("Full", entity["marker_label"]),
                                ("Minimal", entity["short_label"])):
                text = QStaticText(label)
                text.setTextFormat(Qt.TextFormat.PlainText)
                text.prepare(font=self.label_font)
                texts[mode] = text
            self.markers.append((entity, color, conditional, texts))
        self.update_positions()

    def set_visible_entities(self, ids):
        self.visible_ids = set(ids)
        self.hit_regions = []
        self.hovered = None
        self.update()

    def update_positions(self):
        anchors = IMAGE_OPTIONS[self.image_label][2]
        world_anchors = IMAGE_OPTIONS[self.image_label][3]
        self.positions = [QPointF(*world_to_image(e["xyz"][0], e["xyz"][2], anchors, world_anchors))
                          for e in self.entities]

    def view_transform(self):
        image = self.backgrounds[self.image_label]
        scale = min(max(self.width() - 40, 1) / image.width(),
                    max(self.height() - 40, 1) / image.height()) * self.zoom
        origin = QPointF((self.width() - image.width() * scale) / 2,
                         (self.height() - image.height() * scale) / 2) + self.pan
        return image, scale, origin

    def set_image(self, label):
        self.image_label = label
        self.update_positions()
        self.fit_image()

    def set_text_mode(self, mode):
        self.text_mode = mode
        self.hit_regions = []
        self.update()

    def fit_image(self):
        self.zoom = 1.0
        self.pan = QPointF()
        self.drag_position = None
        self.hit_regions = []
        self.setCursor(Qt.CursorShape.ArrowCursor)
        self.zoom_changed.emit(self.zoom)
        self.update()

    def zoom_at(self, factor, position=None):
        if position is None:
            position = QPointF(self.width() / 2, self.height() / 2)
        image, scale, origin = self.view_transform()
        new_zoom = min(16.0, max(0.25, self.zoom * factor))
        ratio = new_zoom / self.zoom
        if ratio == 1:
            return
        new_origin = position - (position - origin) * ratio
        self.pan = new_origin - QPointF((self.width() - image.width() * scale * ratio) / 2,
                                        (self.height() - image.height() * scale * ratio) / 2)
        self.zoom = new_zoom
        self.hit_regions = []
        self.zoom_changed.emit(self.zoom)
        self.update()

    def paintEvent(self, event):
        painter = QPainter(self)
        painter.fillRect(self.rect(), QColor("#090a0c"))
        image, scale, origin = self.view_transform()
        painter.setRenderHint(QPainter.RenderHint.SmoothPixmapTransform)
        painter.drawPixmap(QRectF(origin.x(), origin.y(), image.width() * scale,
                                  image.height() * scale), image, QRectF(image.rect()))
        painter.setFont(self.label_font)
        self.hit_regions = []
        visible = QRectF(self.rect())
        # Markers/text remain screen-sized at every zoom; only their positions
        # move. Off-screen items are skipped, and update() coalesces mouse events.
        for position, (entity, color, conditional, texts) in zip(self.positions, self.markers):
            if self.visible_ids is not None and entity["index"] not in self.visible_ids:
                continue
            point = origin + position * scale
            marker = QRectF(point.x() - 5, point.y() - 5, 10, 10)
            text = texts.get(self.text_mode)
            label_rect = (QRectF(point.x() + 7, point.y() - text.size().height() / 2,
                                text.size().width(), text.size().height()) if text else QRectF())
            if not visible.intersects(marker) and not visible.intersects(label_rect):
                continue
            painter.setPen(QPen(color if conditional else QColor("white"), 2))
            painter.setBrush(Qt.BrushStyle.NoBrush if conditional else color)
            if entity["kind"] == "Base":
                painter.drawEllipse(marker)
            else:
                painter.drawRect(marker)
            if text:
                painter.setPen(color)
                painter.drawStaticText(label_rect.topLeft(), text)
            self.hit_regions.append((marker.adjusted(-2, -2, 2, 2), label_rect, entity))
        if not self.entities or self.visible_ids == set():
            painter.setPen(QColor("white"))
            painter.drawText(self.rect(), Qt.AlignmentFlag.AlignCenter, "Nothing matches these filters.")
        painter.end()


    def show_details_at(self, point, force=False):
        # Prioritize marker hits over overlapping labels.
        found = None
        for region_index in (0, 1):
            for region in reversed(self.hit_regions):
                if region[region_index].contains(point):
                    found = region[2]
                    break
            if found is not None:
                break
        index = found["index"] if found is not None else None
        if found is not None and (force or index != self.hovered):
            self.details_requested.emit(found)
        self.hovered = index

    def wheelEvent(self, event):
        delta = event.angleDelta().y() or event.pixelDelta().y()
        if delta:
            self.zoom_at(1.25 if delta > 0 else 1 / 1.25, event.position())
        event.accept()

    def mousePressEvent(self, event):
        if event.button() == Qt.MouseButton.LeftButton:
            self.show_details_at(event.position(), force=True)
            self.drag_position = event.position()
            self.setCursor(Qt.CursorShape.ClosedHandCursor)
            event.accept()

    def mouseMoveEvent(self, event):
        if self.drag_position is not None:
            self.pan += event.position() - self.drag_position
            self.drag_position = event.position()
            self.hit_regions = []
            self.update()
        else:
            self.show_details_at(event.position())
        event.accept()

    def mouseReleaseEvent(self, event):
        if event.button() == Qt.MouseButton.LeftButton:
            self.drag_position = None
            self.setCursor(Qt.CursorShape.ArrowCursor)
            event.accept()

    def leaveEvent(self, event):
        self.hovered = None
        super().leaveEvent(event)


class MapWindow(QMainWindow):
    def __init__(self, entities, missing, backgrounds, result):
        super().__init__()
        self.entities, self.missing, self.result = entities, missing, result
        self.debug_mode = False
        self.selected_entity = None
        self.trace_event = None
        self.trace_history = []
        self.events = preview_events(result, entities)
        self.setWindowTitle(f"AoT2 Scenario Editor 1.17 - {result['mission']['name']}")
        self.resize(1100, 850)
        content = QWidget()
        self.setCentralWidget(content)
        layout = QVBoxLayout(content)
        layout.setContentsMargins(0, 0, 0, 0)
        toolbar = QHBoxLayout()
        toolbar.setContentsMargins(8, 4, 8, 4)
        layout.addLayout(toolbar)
        self.view = MapView(entities, backgrounds)
        toolbar.addWidget(QLabel("Image:"))
        self.image_choice = QComboBox()
        self.image_choice.addItems(list(IMAGE_OPTIONS))
        self.image_choice.currentTextChanged.connect(self.view.set_image)
        toolbar.addWidget(self.image_choice)
        toolbar.addWidget(QLabel("Text:"))
        self.text_choice = QComboBox()
        self.text_choice.addItems(["Full", "Minimal", "Hide"])
        self.text_choice.currentTextChanged.connect(self.view.set_text_mode)
        toolbar.addWidget(self.text_choice)
        for label, action in (("Zoom +", lambda: self.view.zoom_at(1.25)),
                              ("Zoom −", lambda: self.view.zoom_at(1 / 1.25)),
                              ("Fit", self.view.fit_image)):
            button = QPushButton(label)
            button.clicked.connect(action)
            toolbar.addWidget(button)
        self.zoom_label = QLabel("100% of fit")
        self.view.zoom_changed.connect(lambda zoom: self.zoom_label.setText(f"{zoom:.0%} of fit"))
        toolbar.addWidget(self.zoom_label)
        self.debug_button = QPushButton("Debug mode: OFF")
        self.debug_button.setCheckable(True)
        self.debug_button.toggled.connect(self.set_debug_mode)
        toolbar.addWidget(self.debug_button)
        toolbar.addStretch()
        toolbar.addWidget(QLabel("Wheel: zoom • Drag: pan"))
        filters = QHBoxLayout()
        filters.setContentsMargins(8, 0, 8, 0)
        layout.addLayout(filters)
        filters.addWidget(QLabel("Show:"))
        self.scope_choice = QComboBox()
        self.scope_choice.addItems(["Everything", "Characters", "Titans", "Bases"])
        filters.addWidget(self.scope_choice)
        filters.addWidget(QLabel("State:"))
        self.state_choice = QComboBox()
        self.state_choice.addItems(["All", "Active at start", "Inactive / conditional"])
        filters.addWidget(self.state_choice)
        filters.addWidget(QLabel("Appearance event:"))
        self.event_choice = QComboBox()
        self.event_choice.addItem("All events", None)
        for event in self.events.values():
            self.event_choice.addItem(event["display_name"], event["paragraph"])
        filters.addWidget(self.event_choice, 1)
        self.count_label = QLabel()
        filters.addWidget(self.count_label)
        self.team_legend = QLabel(TEAM_LEGEND)
        self.team_legend.setWordWrap(True)
        self.team_legend.setContentsMargins(8, 0, 8, 0)
        layout.addWidget(self.team_legend)
        layout.addWidget(self.view, 1)
        self.info = QPlainTextEdit()
        self.info.setReadOnly(True)
        self.event_info = QPlainTextEdit()
        self.event_info.setReadOnly(True)
        self.trace_info = QTextBrowser()
        self.trace_info.setOpenLinks(False)
        self.trace_info.setOpenExternalLinks(False)
        self.trace_info.anchorClicked.connect(self.follow_trace_link)
        self.trace_info.setPlainText("Select a unit or appearance event to trace its activation script and callbacks.")
        self.details = QTabWidget()
        self.details.setFixedHeight(200)
        self.details.addTab(self.info, "Selected unit / base")
        self.details.addTab(self.event_info, "Event details")
        self.details.addTab(self.trace_info, "Script trace")
        layout.addWidget(self.details)
        self.view.details_requested.connect(self.describe)
        self.scope_choice.currentIndexChanged.connect(self.apply_filters)
        self.state_choice.currentIndexChanged.connect(self.apply_filters)
        self.event_choice.currentIndexChanged.connect(self.select_event)
        self.apply_filters()

    def filtered_entities(self):
        scope = self.scope_choice.currentIndex()
        state = self.state_choice.currentIndex()
        event_id = self.event_choice.currentData()
        targets = None if event_id is None else {
            a["entity_ordinal"] for a in self.events[event_id]["appearances"]}
        return [e for e in self.entities
                if (scope == 0 or (scope == 1 and e["kind"] != "Base" and not e["titan_possible"])
                    or (scope == 2 and e["titan_possible"]) or (scope == 3 and e["kind"] == "Base"))
                and (state == 0 or e["conditional"] == (state == 2))
                and (targets is None or e["index"] in targets)]

    def apply_filters(self, *_):
        self.selected_entity = None
        visible = self.filtered_entities()
        self.view.set_visible_entities(e["index"] for e in visible)
        self.count_label.setText(f"{len(visible)} / {len(self.entities)}")
        bases = sum(e["kind"] == "Base" for e in visible)
        self.info.setPlainText(
            f"Showing {len(visible) - bases} characters / Titans and {bases} bases.\n"
            "Hover or click a marker to see its name, starting state and appearance events.\n"
            "These are starting placements, not everything active at the same time. "
            "Some spawn locations and party members are chosen during play.\n"
            "Colors show starting teams; alliances and team changes during play are not simulated."
            + (f"\n{self.missing} items could not be placed on the map." if self.missing else ""))
        self.update_event_details()
        if self.debug_mode:
            self.show_debug_overview()

    def set_debug_mode(self, enabled):
        self.debug_mode = enabled
        self.debug_button.setText("Debug mode: ON" if enabled else "Debug mode: OFF")
        # Change presentation without changing the selected event or map filters.
        self.event_choice.blockSignals(True)
        for index in range(1, self.event_choice.count()):
            event_id = self.event_choice.itemData(index)
            event = self.events[event_id]
            prefix = f"Paragraph {event_id} - " if enabled else ""
            self.event_choice.setItemText(index, prefix + event["display_name"])
        self.event_choice.blockSignals(False)
        if self.selected_entity is not None:
            self.describe(self.selected_entity)
            self.update_event_details()
        else:
            self.apply_filters()
        self.render_script_trace()

    def render_script_trace(self):
        if self.trace_event is None:
            self.trace_info.setPlainText("No appearance script selected. Select a unit or appearance event to trace its activation.")
            return
        lines = []
        if self.selected_entity is not None:
            appearances = sorted({a["paragraph"] for a in self.selected_entity["appearance_events"]})
            lines = [self.selected_entity["marker_label"] + " - appearance scripts: " +
                     ", ".join(f"Event {eid}" for eid in appearances), ""]
        if self.debug_mode and self.result.get('archive_offset_note'):lines.insert(0,self.result['archive_offset_note']+'\n')
        content = html.escape("\n".join(lines + script_trace_lines(self.result, self.trace_event, self.debug_mode)))
        event_count = len(self.result["behavior"]["events"])
        def event_link(match):
            eid = int(match.group(1))
            return f'<a href="event:{eid}">{match.group(0)}</a>' if eid < event_count else match.group(0)
        content = re.sub(r"\bEvent (\d+)\b", event_link, content)
        back = '<a href="trace:back">Back to previous script</a><br><br>' if self.trace_history else ""
        self.trace_info.setHtml(back + '<pre style="white-space: pre-wrap">' + content + '</pre>')

    def show_script_event(self, event_id, navigate=False):
        if event_id is not None and not 0 <= event_id < len(self.result["behavior"]["events"]):
            return
        if navigate:
            if self.trace_event is not None and self.trace_event != event_id:
                self.trace_history.append(self.trace_event)
        else:
            self.trace_history.clear()
        self.trace_event = event_id
        self.render_script_trace()
        if navigate:
            self.details.setCurrentWidget(self.trace_info)

    def follow_trace_link(self, url):
        target = url.toString()
        if target == "trace:back" and self.trace_history:
            self.trace_event = self.trace_history.pop()
            self.render_script_trace()
        elif re.fullmatch(r"event:\d+", target):
            self.show_script_event(int(target.split(":")[1]), navigate=True)

    def show_debug_overview(self):
        self.info.setPlainText(
            f"{len(self.filtered_entities())} shown / {len(self.entities)} mapped static records | {self.missing} without coordinates. Not simultaneous spawns.\n"
            f"{TEAM_LEGEND}\n"
            "Colors use the stored initial team, not character type. Runtime team changes are not simulated.\n"
            "Hover/click markers for names, spawn events and offsets.\n"
            "Markers show stored placements. 0x1B/0x1C can choose different positions relative to entities at runtime.")
    def update_debug_event_details(self):
        event_id = self.event_choice.currentData()
        if event_id is None:
            summary = self.result["titan_spawns"]["summary"]
            self.event_info.setPlainText(
                f"{len(self.events)} appearance paragraphs across all teams and entity types.\n"
                f"{summary['titan_records']} Titan records; {summary['initially_hidden_titans']} initially hidden.\n"
                f"{summary['hidden_titans_with_appearance']} hidden Titans have appearance commands; "
                f"{summary['hidden_titans_without_known_appearance']} have no known appearance command.\n"
                "Select a paragraph above to show all its appearance targets and inspect its conditions/effects.\n"
                f"{self.result['decoding']['named_commands']} command records named from executable RTTI; "
                f"{self.result['decoding']['unnamed_commands']} without a known executable class.\n"
                "AND/OR groups, event dependencies, counters, timers and EX-boss requirement checks are decoded; runtime scheduling is not simulated.")
            return
        source = next(e for e in self.result["behavior"]["events"] if e["ordinal"] == event_id)
        event = dict(source, **{k: v for k, v in self.events[event_id].items()
                                if k not in source})
        visible = {e["index"] for e in self.filtered_entities()}
        targets = event["appearances"]
        resolved_targets = {a["entity_ordinal"] for a in targets if a["entity_ordinal"] is not None}
        missing = sorted(resolved_targets - {e["index"] for e in self.entities})
        lines = [f"Paragraph {event_id} | file 0x{event['file_offset']:X}",
                 f"Appearance targets: {sorted(resolved_targets)}; shown with current filters: {sorted(visible)}",
                 "Stored placements are shown; relative spawn positions are resolved during gameplay.",
                 "Commands are static requests; trigger reachability/order is not simulated."]
        if missing:
            lines.append(f"Targets without mapped coordinates: {missing}")
        lines += [f"Raw paragraph header: {event['unknown_header']}", "", "CONDITIONS (file order; AND/OR groups decoded)"]
        lines += [f"Decoded header: {source['decoded_header']}", "Evaluated requirement tree:"]
        lines += ["  " + line for line in requirement_lines(self.result, event_id)]
        if not event["conditions"]:
            lines.append("No serialized conditions; header/scheduler gating may still apply.")
        for i, c in enumerate(event["conditions"]):
            lines.append(f"[{i}] {c['label']} | file 0x{c['file_offset']:X} | uint16={c['raw_u16']}")
            if c["fields"]:
                lines.append(f"  Decoded: {c['fields']}")
        lines += ["", "ENTITY APPEARANCES (ALL TEAMS)"]
        for a in targets:
            if a["opcode"] == 0x1A:
                raw = a["raw"]
                words = raw["raw_u16"]
                lines += [f"Base {words[1] + 1} | initial facility target {words[1]}",
                          f"  CScEffFacilityAppear | type {words[2]} | delay {a['delay_seconds']:g}s | effect file 0x{raw['file_offset']:X}",
                          f"  Raw uint16: {words}"]
                continue
            names = " / ".join(a["candidate_names"]) or "Runtime/unresolved name"
            target_label = (f"#{a['entity_ordinal']}" if a["entity_ordinal"] is not None else
                            f"Unresolved reference {a['raw_target']} ({a['target_interpretation']})")
            lines += [f"{target_label} {names} | selector {a['selector']} | initially hidden={a['initially_hidden']}",
                      f"  {a['appearance_type']} | delay {a['delay_seconds']:g}s | effect file 0x{a['effect_file_offset']:X}",
                      f"  Target operand file 0x{a['target_operand_file_offset']:X} | parameters={a['decoded_parameters']}",
                      f"  Entity references: {a['entity_references']}",
                      f"  Raw uint16: {a['raw_u16']}"]
        lines += ["", "ALL EFFECTS (file order)"]
        for i, e in enumerate(event["effects"]):
            lines.append(f"[{i}] {e['label']} | file 0x{e['file_offset']:X} | uint16={e['raw_u16']}")
            if e["fields"]:
                lines.append(f"  Decoded: {e['fields']}")
        self.event_info.setPlainText("\n".join(lines))

    def describe_debug_entity(self, entity):
        if entity["kind"] == "Base":
            self.describe_debug_base(entity)
            return
        x, y, z = entity["xyz"]
        candidates = " / ".join(entity["candidate_names"]) or "No fixed name; assigned at runtime or unresolved."
        if entity["slot_type"]:
            candidates = "Runtime selection required (selector default deliberately not used as the slot's identity)."
        record = entity["record"]
        resolution = record["name_resolution"]
        lines = [f"#{entity['index']}  {entity['kind']} - {entity['name']}",
                 f"Selector {entity['selector']} | stored XYZ=({x}, {y}, {z}) | heading {entity['heading']}° | role {entity['role']} | category {entity['category']}",
                 f"Initial team: {TEAM_LABELS[entity['initial_team']]} | role low byte={entity['role'] & 255} | role operand file 0x{record['file_offset'] + 6:X}",
                 "Color represents the initial team. Runtime team changes and alliances are not simulated.",
                 f"Names: {candidates}", entity["state_note"], entity["resolution_note"],
                 f"Binary name IDs: {resolution['candidate_name_ids']}; runtime/unresolved IDs: {resolution['unresolved_or_runtime_name_ids']}",
                 f"Definition file 0x{record['file_offset']:X}; selector operand 0x{record['edit_offsets']['selector_u16']:X}; initial-state operand 0x{record['edit_offsets']['initial_state_u16']:X}",
                 "", "APPEARANCE COMMANDS"]
        for a in entity["appearance_events"]:
            lines += [f"Paragraph {a['paragraph']}, effect[{a['effect_index']}]: {a['appearance_type']}; delay {a['delay_seconds']:g}s; file 0x{a['effect_file_offset']:X}",
                      f"  {a['decoded_parameters']}", f"  Entity references: {a['entity_references']}"]
        if not entity["appearance_events"]:
            lines.append("No known appearance command. This does not prove the record is unused.")
        lines.append(f"Disappearance paragraphs: {sorted({a['paragraph'] for a in entity['disappearance_events']})}")
        lines.append("Markers show stored placements, not a simulation of runtime spawn positions.")
        lines += activation_lines(self.result, entity)
        objectives = {c["raw_u16"][1] for a in entity["appearance_events"]
                      for c in self.result["behavior"]["events"][a["paragraph"]]["conditions"]
                      if c["opcode"] in (6, 7)}
        lines += objective_text_lines(self.result, objectives, True)
        self.info.setPlainText("\n".join(lines))


    def describe_debug_base(self, entity):
        record, placement = entity["record"], entity["placement"]
        words = record["raw_u16"]
        lines = [f"{entity['name']} | facility ordinal {entity['base_ordinal']}",
                 f"Stored XYZ={entity['xyz']} | initial facility type {words['+0x04']} | initially inactive={entity['initially_hidden']}",
                 f"Definition file 0x{record['file_offset']:X}; initial-type operand 0x{record['file_offset'] + 4:X}",
                 f"Placement file 0x{placement['file_offset']:X}; X operand 0x{placement['file_offset'] + 4:X}; Z operand 0x{placement['file_offset'] + 6:X}",
                 f"Definition uint16: {list(words.values())}",
                 f"Placement bytes: {placement['raw_hex']}",
                 "", "APPEARANCE COMMANDS"]
        for command in entity["appearance_events"]:
            raw = command["raw"]
            lines += [f"Paragraph {command['paragraph']}: CScEffFacilityAppear; delay {command['delay_seconds']:g}s; file 0x{raw['file_offset']:X}",
                      f"  Raw uint16: {raw['raw_u16']}"]
        if not entity["appearance_events"]:
            lines.append("No known appearance command. Gameplay may still activate the base.")
        lines.append("Markers show stored placements; the game aligns bases to nearby stage sites.")
        lines += activation_lines(self.result, entity)
        self.info.setPlainText("\n".join(lines))

    def select_event(self, *_):
        # Show every event target, including allied units and bases.
        for choice in (self.scope_choice, self.state_choice):
            choice.blockSignals(True)
            choice.setCurrentIndex(0)
            choice.blockSignals(False)
        self.apply_filters()
        self.show_script_event(self.event_choice.currentData())
        self.details.setCurrentWidget(self.event_info)

    def appearance_description(self, command):
        delay = command.get("delay_seconds")
        words = (f"after {delay:g} seconds" if delay else "when the event runs")
        if command["opcode"] in (0x1B, 0x1C):
            words += "; location chosen during play"
        return words

    def update_event_details(self):
        event_id = self.event_choice.currentData()
        if self.debug_mode:
            self.update_debug_event_details()
            return
        if event_id is None:
            titans = [e for e in self.entities if e["titan_possible"]]
            hidden = [e for e in titans if e["initially_hidden"]]
            self.event_info.setPlainText(
                f"{len(self.events)} appearance events across all teams.\n"
                f"{len(titans)} Titans, including {len(hidden)} initially inactive.\n"
                "Choose an event to see who appears and where their starting placements are.\n"
                "Inactive does not automatically mean a Dire Elimination Target. "
                "Requirements are decoded from the scenario and executable. Actual gameplay timing is not simulated.")
            return
        event = self.events[event_id]
        by_id = {e["index"]: e for e in self.entities}
        lines = [event["display_name"],
                 "Timing below is relative to the event starting, not the mission starting.", ""]
        for command in event["appearances"]:
            entity = by_id.get(command["entity_ordinal"])
            label = entity["marker_label"] if entity else "Target not available on the map"
            lines.append(f"{label} - {self.appearance_description(command)}")
        lines += ["", "REQUIREMENTS"]
        lines += requirement_lines(self.result, event_id)
        source = self.result["behavior"]["events"][event_id]
        actions = [command_description(effect, self.result) for effect in source["effects"]
                   if effect["opcode"] not in (0x19, 0x1A, 0x1B, 0x1C, 0xFF)]
        if actions:
            lines += ["", "OTHER ACTIONS"] + actions
        lines += objective_text_lines(self.result, event_objectives(source))
        lines += ["", "Markers show stored placements. Requirements do not simulate scheduling or guarantee an event will run."]
        self.event_info.setPlainText("\n".join(lines))

    def describe(self, entity):
        changed = self.selected_entity is not entity
        self.selected_entity = entity
        if changed:
            appearances = entity["appearance_events"]
            self.show_script_event(appearances[0]["paragraph"] if appearances else None)
        if self.debug_mode:
            self.describe_debug_entity(entity)
            return
        lines = [entity["marker_label"],
                 "Starting state: " + ("Inactive / conditional" if entity["conditional"] else "Active")]
        if entity["kind"] == "Base":
            lines.append("Orange base marker. Inactive bases may be built or activated during play.")
            lines.append("Position shown is the scenario placement; the game aligns it to a nearby base site.")
        else:
            lines.append("Starting team: " + TEAM_LABELS[entity["initial_team"]])
            if entity["slot_type"]:
                lines.append("Character chosen from the player or party selection during play.")
                if entity["slot_type"] == "Player" and (entity["role"] & 255) > 0:
                    lines.append("Only used when enough players participate.")
            elif len(entity["candidate_names"]) > 1:
                lines.append("Possible names: " + " / ".join(entity["candidate_names"]))
            elif not entity["candidate_names"]:
                lines.append("Name assigned during play or unavailable in the game name data.")
        lines += ["", "Appearance events:"]
        for command in entity["appearance_events"]:
            event = self.events.get(command["paragraph"])
            if event:
                lines.append(f"Event {command['paragraph']}: {event['display_name']} - {self.appearance_description(command)}")
                lines.extend("  " + line for line in requirement_lines(self.result, command["paragraph"]))
        if not entity["appearance_events"]:
            lines.append("No scripted appearance found; gameplay may still activate this location.")
        if entity["disappearance_events"]:
            lines.append("Can leave the map during scripted events.")
        if entity["appearance_events"]:
            objectives = {c["raw_u16"][1] for a in entity["appearance_events"]
                          for c in self.result["behavior"]["events"][a["paragraph"]]["conditions"]
                          if c["opcode"] in (6, 7)}
            lines += objective_text_lines(self.result, objectives)
        self.info.setPlainText("\n".join(lines))



def load_backgrounds(result):
    root = Path(result.get("editor_game_root") or scenario.resolve_game_root(result["source"]))
    patch = root / "LINKDATA/PATCH/LINKDATA_PATCH_000.BIN"
    mission_id = result["mission"]["mission_id"]
    scenario.require(mission_id is not None and 0 <= mission_id < 512,
                     "Cannot identify the mission row; keep the original SCENARIO_DLC_NNN_NNN.bin filename")
    # Scenario section 0 has legacy 80-byte mission records, with stage at +02.
    # The current patched resource uses 88-byte records. Refuse ambiguous stages
    # rather than silently displaying another map when an edited snapshot differs.
    missions, _ = scenario.read_name_resource(patch, 4)
    scenario.require(mission_id * 88 + 2 < len(missions), "Mission row outside current configuration")
    if (result.get('archive_binding') or {}).get('kind') == 'split':
        stage_id = missions[mission_id * 88 + 2]
    else:
        row_offset = mission_id * 80 + 2
        section = result['sections'][0]
        scenario.require(row_offset < section['length'], 'Mission row outside scenario section 0')
        stage_id = result['editor_data'][section['file_offset'] + row_offset]
        scenario.require(missions[mission_id * 88 + 2] == stage_id,
                         'Scenario and current game configuration select different stages')
    stages, _ = scenario.read_name_resource(patch, 12)  # DataStage.bin, FUN_140b72d80
    scenario.require(len(stages) == 14992 and stage_id < 30, "Unsupported DataStage layout/stage ID")
    minimap_id = stages[stage_id * 100 + 0x50]
    scenario.require(minimap_id < 30, "Unsupported minimap ID")
    resource_ids = exe_resource_ids(root / "AOT2_EU.exe", minimap_id)
    ui, _ = scenario.read_name_resource(patch, 5)  # DataUI.bin, current serialized layout
    scenario.require(len(ui) == 27232, "Unsupported DataUI layout")
    ui_offset = 201 * 28 + 101 * 92 + 30 * 8 + minimap_id * 84
    row = ui[ui_offset:ui_offset + 84]
    scenario.require(len(row) == 84 and scenario.unpack("<H", row)[0] == minimap_id,
                     "DataUI minimap row does not match the selected map")
    backgrounds, options = {}, {}
    # Default to the larger pause-table texture as before. Both sizes and both
    # coordinate registrations are loaded from bytes, not constants for ST23.
    for kind, pixel_offsets, world_offsets in (
            ("Pause", (0x2C, 0x38), (0x30, 0x3C)),
            ("HUD", (0x02, 0x10), (0x08, 0x14))):
        data, provenance = read_texture_resource(root, resource_ids[kind])
        image = decode_g1t(data)
        anchors = tuple(scenario.unpack("<HH", row, offset) for offset in pixel_offsets)
        world_anchors = tuple(scenario.unpack("<ii", row, offset) for offset in world_offsets)
        scenario.require(world_anchors[0][0] != world_anchors[1][0]
                         and world_anchors[0][1] != world_anchors[1][1], "Degenerate world/map anchors")
        label = f"{kind} texture ({image.width()} x {image.height()})"
        backgrounds[label] = QPixmap.fromImage(image)
        options[label] = (provenance, (image.width(), image.height()), anchors, world_anchors)
    IMAGE_OPTIONS.clear()
    IMAGE_OPTIONS.update(options)
    return backgrounds


# Entity operand word indices: initializer loads plus runtime entity-base additions.
# Condition base object+11; effect base object+18. Guarded by EXE_SHA256.
ENTITY_OPERANDS = {'condition': {0: [1], 1: [1, 2], 2: [], 3: [], 4: [], 5: [], 6: [], 7: [], 8: [], 9: [], 10: [1], 11: [], 12: [1, 2], 13: [1], 14: [], 15: [], 16: [], 17: [], 18: [1], 19: [], 20: [], 21: [1], 22: [], 23: [1, 2], 24: [1], 25: [1], 26: [], 27: [], 28: [], 29: [], 30: [], 31: [], 32: [], 33: [], 34: [], 35: [], 36: [], 37: [], 38: [], 39: [], 40: [], 41: [], 42: [], 43: [], 44: [], 45: [], 46: [], 47: [], 48: [], 49: [], 50: [], 254: [], 255: []}, 'effect': {0: [], 1: [], 2: [], 3: [], 4: [], 5: [], 6: [], 7: [1], 8: [], 9: [], 10: [], 11: [], 12: [], 13: [], 14: [], 15: [], 16: [], 17: [1], 18: [], 19: [1, 5], 20: [1], 21: [1], 22: [1], 23: [], 24: [], 25: [1], 26: [], 27: [1, 5], 28: [1, 2], 29: [1], 30: [], 31: [], 32: [], 33: [1], 34: [1], 35: [1], 36: [1, 2], 37: [1], 38: [1], 39: [1], 40: [1, 2], 41: [1], 42: [1], 43: [1], 44: [1], 45: [1, 3], 46: [1], 47: [4, 5, 11, 12], 48: [1], 49: [], 50: [], 51: [1], 52: [], 53: [], 54: [4, 5, 11, 12], 55: [], 56: [1], 57: [], 58: [], 59: [], 60: [], 61: [], 62: [], 63: [], 64: [], 65: [], 66: [2, 3, 8, 9], 67: [2], 68: [1], 69: [1], 70: [1], 71: [], 72: [1], 73: [], 74: [], 75: [], 76: [], 77: [1], 78: [1], 79: [], 80: [], 81: [], 82: [3, 4, 9, 10], 83: [2], 84: [], 85: [], 86: [], 87: [], 88: [], 89: [], 90: [], 91: [], 92: [], 93: [], 94: [], 95: [1], 96: [], 97: [1], 98: [], 99: [], 100: [], 101: [], 102: [], 103: [], 104: [], 105: [], 106: [], 107: [], 108: [], 109: [], 110: [], 111: [], 112: [], 113: [], 114: [], 115: [], 116: [], 117: [1], 255: []}}


# --------------------------- 1.9 editor ---------------------------
import copy
import os
from functools import lru_cache
from PySide6.QtCore import QEvent, QTimer, QSignalBlocker, QUrl, QSaveFile, QIODevice, QSize, QRect, QThread
from PySide6.QtGui import QAction, QKeySequence, QValidator
from PySide6.QtWidgets import (
    QAbstractItemView, QCheckBox, QDialog, QDialogButtonBox, QDockWidget,
    QDoubleSpinBox, QFileDialog, QFormLayout, QFrame, QInputDialog, QLineEdit,
    QListWidget, QListWidgetItem, QMenu, QScrollArea, QSpinBox, QSplitter, QTreeWidget,
    QTreeWidgetItem, QToolBar, QToolButton, QStyle, QSizePolicy, QStyledItemDelegate, QHeaderView,
)

# Decode metadata once per EXE build; never create caches on disk.
executable_command_names = lru_cache(maxsize=2)(executable_command_names)
read_party_names = lru_cache(maxsize=2)(read_party_names)


def flatten_nodes(nodes):
    words = []
    for node in nodes:
        row = list(node['words'])
        if row[0] in (0xFE, 0xFF):
            row[1] = len(node['children'])
        words.append(row)
        words.extend(flatten_nodes(node['children']))
    return words


def nodes_from_rows(rows):
    def take(index):
        row = list(rows[index]); index += 1
        node = dict(words=row, children=[])
        if row[0] in (0xFE, 0xFF):
            for _ in range(row[1]):
                scenario.require(index < len(rows), 'Condition group is truncated')
                child, index = take(index); node['children'].append(child)
        return node, index
    nodes, index = [], 0
    while index < len(rows):
        node, index = take(index); nodes.append(node)
    return nodes


def new_group(op=0xFF):
    return dict(words=[op] + [0] * 15, children=[])


# Environment evidence, AOT2_EU.exe fingerprint checked by MapStore:
# FUN_140dbfae0, 140dbfc73..140dbfd6e reads DataScenarioBase rows (88 bytes):
# +02 stage, +04 lighting, +05 clock, +06 snow, +07 rain. Snow/rain 2 is
# randomized by FUN_140dbeef0; 0/1 are off/on. Forced snow selects stage*10+6
# only when DataStage[stage*100+96]==2, at clock 0. Rain selects stage*10+4
# at clock 24. Snow and rain are mutually exclusive after native resolution.
# FUN_140d3a3c0 maps environment IDs to installed stNN_00_LNN.bin resources.
# CScEffChangeClockTime initializer 140d09950 reads u16 +02/+04; activation
# 140d098d0 clamps hours/24 + minutes/1440 to [0,1] and writes scene+CA0.
# This clock interpolates the lighting resource. It is NOT a universal solar
# clock: 00:00 in the Night Training preset is already night.
ENVIRONMENT_WEATHER = [('Normal',0,0),('Rain',0,1),('Snow',1,0),
                       ('Random rain',0,2),('Random snow',2,0),('Random rain or snow',2,2)]


def environment_values(document):
    mission=document.result['mission']['mission_id'];offset=mission*80+4
    # Bundled/saved maps carry their row. Unedited split maps read the original
    # patched mission table through their registered archive binding.
    if len(document.sections[0])>=offset+4:return tuple(document.sections[0][offset:offset+4])
    store=getattr(document,'map_store',None)
    scenario.require(store is not None,'Open an extracted map to edit its environment')
    raw=store.environment_original();return tuple(raw[mission*88+4:mission*88+8])


def environment_startup_clocks(document):
    """Only standalone, enabled, unconditional clock actions; no inferred gates."""
    found=[]
    for i,event in enumerate(document.events):
        if event['header'][9]&0x0C:continue
        parent=struct.unpack_from('<I',event['header'])[0]
        if parent not in (0,i):continue
        if event['conditions']!=[new_group()]:continue
        for j,w in enumerate(event['effects']):
            if w[0]==98 and 0<=w[1]*60+w[2]<=1440:
                found.append((i,j,w[1]*60+w[2]))
    return found


def environment_starting_values(document,snow_supported=True):
    lighting,hour,snow,rain=environment_values(document)
    # Mirror the loader, including its forced weather presets and clock values.
    # Random weather is unresolved until the game rolls it; show its fallback.
    if snow==1 and snow_supported:lighting,minutes=6,0
    elif rain==1:lighting,minutes=4,1440
    else:minutes=hour*60
    clocks=environment_startup_clocks(document)
    if clocks:minutes=clocks[-1][2]
    return lighting,minutes,snow,rain


def set_environment_start(document,values,minutes,snow_supported=True):
    scenario.require(0<=minutes<=1440,'Lighting progression must be between 0% and 100%')
    previous=environment_starting_values(document,snow_supported)
    set_environment_values(document,values)
    lighting,hour,snow,rain=values
    native_minutes=0 if snow==1 and snow_supported else 1440 if rain==1 else hour*60
    clocks=environment_startup_clocks(document)
    # Do not add an action merely by opening or applying unchanged settings.
    # Clock actions are native scenario commands, including under rain/snow;
    # unlike the startup mission hour, their handler is not weather-gated.
    if minutes==previous[1] and clocks:return
    if minutes==native_minutes and not clocks:return
    # Reuse a final standalone clock-only event. Never renumber/delete events or
    # rewrite an existing event that also performs unrelated actions.
    index=len(document.events)-1
    if not (clocks and clocks[-1][:2]==(index,0) and len(document.events[index]['effects'])==1):
        index=document.append_event()
    document.events[index]['effects']=[[98,minutes//60,minutes%60]+[0]*13]


def set_environment_values(document,values):
    lighting,hour,snow,rain=values
    scenario.require(0<=lighting<10 and 0<=hour<=24 and snow in (0,1,2) and rain in (0,1,2),
                     'Invalid environment settings')
    mission=document.result['mission']['mission_id'];offset=mission*80
    block=bytearray(document.sections[0])
    if len(block)<offset+80:
        # Split maps have no mission table in their editable container. Store
        # this row using the same legacy stride as bundled maps; injection
        # merges only its four environment bytes into the current shared table.
        block.extend(bytes(offset+80-len(block)))
        raw=document.map_store.environment_original()
        block[offset:offset+80]=raw[mission*88:mission*88+80]
    block[offset+4:offset+8]=bytes(values);document.sections[0]=bytes(block)


@lru_cache(maxsize=32)
def environment_options(root,stage):
    library=ArchiveLibrary(Path(root),[]);options=[]
    # Descriptive UI labels, not strings exported by the engine. The daylight
    # samples progress from warm to neutral (0), neutral to warm (1), warm (2),
    # orange low-angle illumination (3/7). Night is native remainder==5.
    # The exact RGB/direction samples are supplied by the selected map's BIN.
    labels={0:'Morning / daylight',1:'Day / noon',2:'Afternoon',3:'Evening',
            4:'Overcast / rain',5:'Night',6:'Snow',7:'Evening (alternate)',8:'Overcast / rain (alternate)',9:'Special lighting'}
    for index in range(10):
        name=f'File/Scene/EnvironmentData/st{stage:02}_00_L{index+1:02}.bin'
        if name.lower() not in library.resources:continue
        data=library.read_named(name)
        if len(data)<16:continue
        count=scenario.u32(data)
        if not (0<count<=64 and len(data)==16+count*0x978):continue
        # Unused installed variants have zero RGBA for every lighting sample.
        if not any(any(data[16+n*0x978:32+n*0x978]) for n in range(count)):continue
        options.append((index,labels.get(index,f'Lighting preset {index+1}'),name))
    stages=library.read_named('File/Data/DataStage.bin')
    scenario.require(len(stages)==14992 and 0<=stage<30,'Unsupported stage environment table')
    return tuple(options),stages[stage*100+96]==2


class ScenarioDocument:
    """Lossless container writer. Unedited sections/record bytes are preserved.

    Sections use independent length/offset tables and 16-byte alignment. Nested
    behavior tables and event directories use relative offsets. Full rebuilding
    is necessary when adding records; overwriting offsets in place is unsafe.
    """
    def __init__(self, data, source, game_root=None, mission_id=None):
        self.source = str(source)
        self.game_root = scenario.resolve_game_root(str(source), game_root)
        self.mission_override = mission_id
        self.saved_bytes = bytes(data)
        self.undo_stack, self.redo_stack = [], []
        self.load_bytes(data)
        self.saved_path = str(source)
        self.archive_binding = None

    def load_bytes(self, data):
        self._edit_group = None
        if hasattr(self,'result'):
            try:current=self.serialize()
            except Exception:current=None
            if current==self.result['editor_data'] and self.refresh_placements(data,restore=True):return
        self.header = bytearray(data[:0x410])
        _, metadata = scenario.parse_sections(data)
        self.sections = [bytes(data[x['file_offset']:x['file_offset'] + x['length']]) for x in metadata]
        placements = scenario.parse_placements(self.sections[5], 0)
        self.placement_header = placements['unknown_header_u32']
        self.placements = [[bytearray.fromhex(p['raw_hex']) for p in group] for group in placements['groups']]
        section = self.sections[6]
        tables = [section[o:o+n] for o,n in [struct.unpack_from('<II', section, 4+8*i) for i in range(4)]]
        self.units = [bytearray(tables[0][4+i*64:68+i*64]) for i in range(scenario.u32(tables[0]))]
        self.bases = [bytearray(tables[1][4+i*64:68+i*64]) for i in range(scenario.u32(tables[1]))]
        self.unknown_table = tables[2]
        self.events = []
        for event in scenario.parse_events(tables[3], 0, len(self.units)):
            start = event['file_offset']
            self.events.append(dict(header=bytearray(tables[3][start:start+12]),
                                    conditions=nodes_from_rows([c['raw_u16'] for c in event['conditions']]),
                                    effects=[list(c['raw_u16']) for c in event['effects']]))
        self.refresh_result(bytes(data))

    def refresh_result(self, data=None):
        data = self.serialize() if data is None else data
        if self.refresh_placements(data):return
        self.refresh_kind = "full"
        self.result = scenario.analyze(data, self.source, game_root=self.game_root)
        apply_installed_names(self.result,self.game_root,self.sections[4])
        if self.mission_override is not None:
            self.result['mission']['mission_id'] = self.mission_override
        self.result['editor_data'] = data
        self.update_archive_context()
        enrich_scenario(self.result)

    def update_archive_context(self):
        self.result['editor_game_root'] = self.game_root
        self.result['archive_binding'] = getattr(self, 'archive_binding', None)
        if self.result['archive_binding'] and self.result['archive_binding']['kind']=='split':
            self.result['archive_offset_note']='BIN offsets below refer to the assembled in-memory scenario; '+', '.join(
                f'section {k}: {Path(p).name} entry {i}' for k,(p,i) in self.result['archive_binding']['parts'].items())

    def refresh_placements(self,data,restore=False):
        result=getattr(self,'result',None)
        if result is None:return False
        before=result['editor_data'];section=result['sections'][5]
        start=section['file_offset'];end=start+section['length']
        # Header, all definitions, scripts, text and section lengths must match.
        # Any structural/other edit takes the full validated parsing path.
        if len(data)!=len(before) or data[:start]!=before[:start] or data[end:]!=before[end:]:return False
        parsed=scenario.parse_placements(data[start:end],start)
        old=result['placements']
        if any(len(a)!=len(b) or any(x['join_key']!=y['join_key'] for x,y in zip(a,b))
               for a,b in zip(old['groups'],parsed['groups'])):return False
        for old_group,new_group in zip(old['groups'],parsed['groups']):
            for old_record,new_record in zip(old_group,new_group):
                old_record.clear();old_record.update(new_record)
        old['unknown_header_u32']=parsed['unknown_header_u32']
        if restore:
            self.placement_header=parsed['unknown_header_u32']
            self.placements=[[bytearray.fromhex(p['raw_hex']) for p in group] for group in parsed['groups']]
            self.sections[5]=bytes(data[start:end])
        result['sha256']=hashlib.sha256(data).hexdigest();result['editor_data']=bytes(data)
        self.refresh_kind='placements'
        return True

    def serialize(self):
        scenario.require(len(self.units) <= 255, 'Maximum 255 units: runtime entity count is an unsigned byte')
        scenario.require(len(self.bases) <= 64, 'Maximum 64 bases')
        blocks = []
        for group, cap in zip(self.placements, (256,64,64)):
            scenario.require(len(group) <= cap and all(len(x)==64 for x in group), 'Invalid placement count/stride')
            blocks.append(struct.pack('<I',len(group)) + b''.join(group))
        placement = struct.pack('<I',self.placement_header) + b''.join(blocks)
        event_payloads = []
        for index,event in enumerate(self.events):
            conditions = flatten_nodes(event['conditions'])
            scenario.require(len(conditions)<=255 and len(event['effects'])<=255, f'Event {index}: maximum 255 conditions/actions')
            h = bytearray(event['header']);h[10:12]=bytes((len(conditions),len(event['effects'])))
            event_payloads.append(bytes(h)+b''.join(struct.pack('<16H',*row) for row in conditions+event['effects']))
        cursor=4+4*len(event_payloads);offsets=[]
        for block in event_payloads:offsets.append(cursor);cursor+=len(block)
        event_table=struct.pack('<I',len(offsets))+struct.pack(f'<{len(offsets)}I',*offsets)+b''.join(event_payloads)
        tables=[struct.pack('<I',len(self.units))+b''.join(self.units),
                struct.pack('<I',len(self.bases))+b''.join(self.bases),self.unknown_table,event_table]
        cursor=36;directory=[]
        for block in tables:directory.extend((cursor,len(block)));cursor+=len(block)
        # Exactly four offset/length pairs, not an aligned nested header.
        behavior=struct.pack('<I8I',4,*directory)+b''.join(tables)
        sections=list(self.sections);sections[5]=placement;sections[6]=behavior
        header=bytearray(self.header);payload=bytearray();cursor=0x410
        for i,block in enumerate(sections):
            struct.pack_into('<I',header,0x10+4*i,cursor)
            struct.pack_into('<I',header,0x210+4*i,len(block))
            payload.extend(block);padding=(-len(block))%16
            payload.extend(bytes(padding));cursor+=len(block)+padding
        return bytes(header+payload)

    @property
    def dirty(self):
        return self.serialize()!=self.saved_bytes

    def change(self,label,operation,merge_key=None):
        before=self.serialize()
        try:
            operation()
            after=self.serialize()
            if after==before:
                if merge_key is None:self.finish_edit()
                return False
            self.refresh_result(after)
        except Exception:
            self.load_bytes(before)
            raise

        if merge_key is None or merge_key!=self._edit_group or not self.undo_stack:
            self.undo_stack.append((label,before));self.undo_stack=self.undo_stack[-60:]
        self._edit_group=merge_key
        self.redo_stack.clear()
        return True

    def finish_edit(self):
        self._edit_group=None

    def undo(self):
        if not self.undo_stack:return
        label,data=self.undo_stack.pop();self.redo_stack.append((label,self.serialize()));self.load_bytes(data)

    def redo(self):
        if not self.redo_stack:return
        label,data=self.redo_stack.pop();self.undo_stack.append((label,self.serialize()));self.load_bytes(data)

    def placement_for(self,index):
        key=bytes(self.units[index][:4])
        return next((p for p in self.placements[0] if bytes(p[:4])==key),None)

    def move(self,index,x,y,z):
        if index<0:
            i=-index-1
            scenario.require(0<=x<=6553500 and 0<=z<=6553500,'Base positions must be 0–6,553,500')
            struct.pack_into('<HH',self.placements[2][i],4,round(x/100),round(z/100))
        else:
            p=self.placement_for(index);scenario.require(p is not None,'Unit has no stored placement')
            struct.pack_into('<iii',p,8,round(x),round(y),round(z))

    def append_unit(self,source_index,selector,template=None):
        count=len(self.units)
        scenario.require(count<255,'Maximum 255 units')
        scenario.require(len(self.placements[0])<256,'Primary placement table is full')
        # FUN_140d17490 treats reference == deployment count as the player
        # placeholder. Preserve that meaning when the table grows; leave every
        # existing entity ordinal untouched. Operand positions come from EXE
        # initializers, not a search-and-replace of all numeric values.
        for event in self.events:
            for kind,rows in [('condition',flatten_nodes(event['conditions'])),('effect',event['effects'])]:
                for row in rows:
                    scenario.require(row[0] in ENTITY_OPERANDS[kind], 'Cannot add units with an unsupported command opcode')
                    for position in ENTITY_OPERANDS[kind][row[0]]:
                        if row[position]==count:row[position]=count+1
                if kind=='condition':event['conditions']=nodes_from_rows(rows)
        original,placement=template if template is not None else (self.units[source_index],self.placement_for(source_index))
        scenario.require(placement is not None,'Choose a source unit with a placement')
        record=bytearray(original);newpos=bytearray(placement)
        used={bytes(p[:4]) for p in self.placements[0]}|{bytes(u[:4]) for u in self.units}
        group=struct.unpack_from('<H',original)[0]
        key=next((struct.pack('<HH',group,i) for i in range(65536) if struct.pack('<HH',group,i) not in used),None)
        scenario.require(key is not None,'No free placement join key')
        record[:4]=key;newpos[:4]=key;struct.pack_into('<H',record,4,selector)
        # A copy is a normal deployment, never another runtime player slot.
        if record[6]<8:record[6]=8
        self.units.append(record);self.placements[0].append(newpos)
        return count

    def append_base(self,source_index=0,template=None):
        scenario.require(len(self.bases)<64 and len(self.placements[2])<64,'Maximum 64 base placements')
        scenario.require(self.bases and len(self.bases)==len(self.placements[2]),'Base definitions and placements must pair by ordinal')
        record,placement=template if template is not None else (self.bases[source_index],self.placements[2][source_index])
        self.bases.append(bytearray(record));self.placements[2].append(bytearray(placement))
        return -len(self.bases)

    def append_event(self,source=None):
        index=len(self.events)
        if source is None:
            event=dict(header=bytearray(struct.pack('<IIBBBB',index,0,5,0,1,0)),conditions=[new_group()],effects=[])
        else:
            event=copy.deepcopy(self.events[source])
            scenario.require(not event['header'][9]&4,'Duplicate individual events, not parent groups')
            struct.pack_into('<II',event['header'],0,index,0)
            event['header'][9]&=~(0x10|0x20|0x40|0x80)
        # Self-parented standalone events are checked normally by the native
        # evaluator; existing parent ranges, IDs and event references stay valid.
        self.events.append(event)
        return index

    def save_as(self,path):
        data=self.serialize()
        # Parse the rebuilt container before touching the selected output.
        scenario.analyze(data,self.source,game_root=self.game_root)
        path=Path(path)
        scenario.require(path.suffix.lower()=='.bin','Save a .bin scenario')
        output=QSaveFile(str(path))
        scenario.require(output.open(QIODevice.OpenModeFlag.WriteOnly),output.errorString())
        if output.write(data)!=len(data):
            output.cancelWriting();raise ValueError(output.errorString())
        scenario.require(output.commit(),output.errorString())
        scenario.require(path.read_bytes()==data,'Saved BIN verification failed')
        self.saved_bytes=data;self.saved_path=str(path)


class MapView(PreviewMapView):
    moved_many=Signal(object)
    selection_changed=Signal(object)

    def __init__(self,*args,**kwargs):
        self.selection=None;self.selected_ids=set();self.cut_ids=set()
        self.gesture=None;self.start_point=None;self.rectangle=None;self.original_positions={}
        self.last_pointer=None
        self.snap_enabled=False;self.snap_pixels=16;self.snap_offset=0;self.drag_anchor=None
        super().__init__(*args,**kwargs)
        self.text_mode='Minimal';self.setFocusPolicy(Qt.FocusPolicy.StrongFocus)

    def hit(self,point):
        hits=[entity for marker,_,entity in reversed(self.hit_regions)
              if entity['index'] not in self.cut_ids and marker.contains(point)]
        return next((e for e in hits if e['index'] in self.selected_ids),hits[0] if hits else None)

    def world_point(self,point):
        _,scale,origin=self.view_transform();p=(QPointF(point)-origin)/scale
        return self.image_to_world(p)

    def image_to_world(self,p):
        anchors=IMAGE_OPTIONS[self.image_label][2];world=IMAGE_OPTIONS[self.image_label][3]
        return (world[0][0]+(p.x()-anchors[0][0])*(world[1][0]-world[0][0])/(anchors[1][0]-anchors[0][0]),
                world[0][1]+(p.y()-anchors[0][1])*(world[1][1]-world[0][1])/(anchors[1][1]-anchors[0][1]))

    def snap_world(self,x,z):
        if not self.snap_enabled:return x,z
        anchors=IMAGE_OPTIONS[self.image_label][2];world=IMAGE_OPTIONS[self.image_label][3]
        px,py=world_to_image(x,z,anchors,world)
        step=self.snap_pixels;offset=self.snap_offset
        return self.image_to_world(QPointF(offset+round((px-offset)/step)*step,
                                          offset+round((py-offset)/step)*step))

    def set_selection(self,ids,notify=True):
        self.selected_ids=set(ids);self.selection=next(iter(sorted(self.selected_ids)),None)
        self.update()
        if notify:self.selection_changed.emit(self.selected_ids.copy())

    def mousePressEvent(self,event):
        self.setFocus();self.last_pointer=event.position();self.start_point=event.position()
        if event.button()==Qt.MouseButton.MiddleButton:
            self.gesture='pan';self.drag_position=event.position();self.setCursor(Qt.CursorShape.ClosedHandCursor)
        elif event.button()==Qt.MouseButton.LeftButton:
            entity=self.hit(event.position());add=bool(event.modifiers() & Qt.KeyboardModifier.ControlModifier)
            if entity:
                index=entity['index']
                if add and index in self.selected_ids:
                    self.gesture=None;self.original_positions={};self.drag_anchor=None
                    self.set_selection(self.selected_ids-{index})
                    event.accept();return
                if add:self.set_selection(self.selected_ids|{index})
                elif index not in self.selected_ids:self.set_selection({index})
                self.gesture='move';self.drag_anchor=index
                self.original_positions={e['index']:tuple(e['xyz']) for e in self.entities if e['index'] in self.selected_ids and e['index'] not in self.cut_ids}
            else:
                self.gesture='select';self.selection_before=self.selected_ids.copy() if add else set()
                self.rectangle=QRectF(event.position(),event.position())
                self.set_selection(self.selection_before,False)
        event.accept()

    def mouseMoveEvent(self,event):
        self.last_pointer=event.position()
        if self.gesture=='pan':
            self.pan+=event.position()-self.drag_position;self.drag_position=event.position();self.update()
        elif self.gesture=='select':
            self.rectangle=QRectF(self.start_point,event.position()).normalized()
            _,scale,origin=self.view_transform()
            ids={e['index'] for e,p in zip(self.entities,self.positions)
                 if (self.visible_ids is None or e['index'] in self.visible_ids) and e['index'] not in self.cut_ids
                 and self.rectangle.contains(origin+p*scale)}
            self.set_selection(self.selection_before|ids,False)
        elif self.gesture=='move' and (event.position()-self.start_point).manhattanLength()>=QApplication.startDragDistance():
            x,z=self.world_point(event.position());sx,sz=self.world_point(self.start_point)
            dx,dz=x-sx,z-sz
            if self.snap_enabled and self.drag_anchor in self.original_positions:
                ax,_,az=self.original_positions[self.drag_anchor]
                tx,tz=self.snap_world(ax+dx,az+dz);dx,dz=tx-ax,tz-az
            for e in self.entities:
                if e['index'] in self.original_positions:
                    ox,oy,oz=self.original_positions[e['index']];e['xyz']=(round(ox+dx),oy,round(oz+dz))
            self.update_positions();self.update()
        else:
            entity=self.hit(event.position());self.setToolTip(entity['marker_label'] if entity else '')
        event.accept()

    def mouseReleaseEvent(self,event):
        if self.gesture=='pan' and event.button()!=Qt.MouseButton.MiddleButton:return
        if self.gesture in ('move','select') and event.button()!=Qt.MouseButton.LeftButton:return
        gesture=self.gesture;self.gesture=None
        if gesture=='move':
            changes=[]
            for e in self.entities:
                if e['index'] in self.original_positions:
                    old=self.original_positions[e['index']]
                    if tuple(e['xyz'])!=old:changes.append((e['index'],*e['xyz']))
                    e['xyz']=old
            self.original_positions={};self.update_positions()
            if changes:self.moved_many.emit(changes)
        elif gesture=='select':self.selection_changed.emit(self.selected_ids.copy())
        self.rectangle=None;self.drag_position=None;self.setCursor(Qt.CursorShape.ArrowCursor);self.update();event.accept()

    def keyPressEvent(self,event):
        delta={Qt.Key.Key_Left:QPointF(50,0),Qt.Key.Key_Right:QPointF(-50,0),
               Qt.Key.Key_Up:QPointF(0,50),Qt.Key.Key_Down:QPointF(0,-50)}.get(event.key())
        if delta is not None:self.pan+=delta;self.update();event.accept();return
        if event.key()==Qt.Key.Key_Escape:
            for e in self.entities:
                if e['index'] in self.original_positions:e['xyz']=self.original_positions[e['index']]
            self.original_positions={};self.gesture=None;self.rectangle=None;self.cut_ids.clear()
            self.update_positions();self.set_selection(set());event.accept();return
        super().keyPressEvent(event)

    def paintEvent(self,event):
        hidden=self.visible_ids
        if self.cut_ids:self.visible_ids=(set(e['index'] for e in self.entities) if hidden is None else hidden)-self.cut_ids
        super().paintEvent(event);self.visible_ids=hidden
        painter=QPainter(self);painter.setPen(QPen(QColor('#ffffff'),2));painter.setBrush(Qt.BrushStyle.NoBrush)
        for marker,_,entity in self.hit_regions:
            if entity['index'] in self.selected_ids:painter.drawRect(marker.adjusted(-4,-4,4,4))
        if self.rectangle is not None:
            painter.setPen(QPen(QColor('#75baff'),1));painter.setBrush(QColor(70,150,255,45));painter.drawRect(self.rectangle)
        painter.end()


# Only operands whose consumers have been decoded get semantic controls.
# The remaining words are preserved and available under Advanced binary fields.
EDIT_FIELDS = {
 'condition': {
  0: [(1,'Unit','unit'),(2,'KO count','number'),(3,'Comparison','comparison'),(4,'KO category','number')],
  4: [(1,'Event','event'),(2,'Has started','bool')],
  5: [(1,'Event','event'),(2,'Has executed actions','bool')],
  6: [(1,'Objective','objective'),(2,'Preparation threshold','number'),(3,'Comparison','comparison'),(4,'Expected','bool')],
  7: [(1,'Objective','objective'),(2,'State','objective_state'),(3,'Matches','bool')],
  8: [(1,'Result','result'),(2,'Objective category','objective_category'),(3,'Count','number'),(4,'Comparison','comparison')],
  9: [(1,'Special-target requirement','number'),(2,'Succeeded','bool')],
  10: [(1,'Unit','unit'),(2,'Minimum X cell','number'),(3,'Minimum Z cell','number'),(4,'Maximum X cell','number'),(5,'Maximum Z cell','number')],
  14: [(1,'Timer','number'),(2,'Seconds','number'),(3,'Comparison','comparison')],
  15: [(1,'Counter','number'),(2,'Value','signed'),(3,'Comparison','comparison')],
  21: [(1,'Unit','unit'),(2,'Status test (0 = active)','number'),(4,'Expected','bool')],
  25: [(1,'Unit','unit'),(2,'Character / Titan ID','selector'),(3,'Matches','bool')],
 },
 'effect': {
  0: [(1,'Timer','number'),(2,'Operation','timer_operation'),(3,'Seconds to add / subtract','number')],
  2: [(1,'Counter','number'),(2,'Value','signed'),(3,'Operation','counter_operation')],
  23: [(1,'Event to reactivate','event')],
  25: [(1,'Unit to appear','unit'),(2,'Delay (60 ticks = 1 second)','number')],
  26: [(1,'Base to activate','base'),(2,'Base type','number'),(3,'Delay (60 ticks = 1 second)','number')],
  27: [(1,'Unit to appear','unit'),(2,'Position mode (1 = around unit)','number'),(3,'X cell','number'),(4,'Z cell','number'),(5,'Reference unit','unit'),(6,'Search radius mode','number')],
  28: [(1,'Unit to appear','unit'),(2,'Reference unit','unit'),(3,'Distance in cells','number'),(4,'Placement mode','number'),(5,'Direction','number'),(6,'Randomize direction','bool'),(7,'Appearance flags','number'),(8,'Delay (60 ticks = 1 second)','number')],
  33: [(1,'Unit','unit'),(2,'X cell','number'),(3,'Z cell','number'),(4,'Orientation parameter','number')],
  34: [(1,'Unit','unit'),(2,'X','int32'),(4,'Z','int32'),(7,'Delay (60 ticks = 1 second)','number')],
  35: [(1,'Unit','unit'),(2,'Behavior preset (preset actions not decoded)','number')],
  36: [(1,'Unit','unit'),(2,'Target unit','unit')],
  37: [(1,'Unit','unit'),(2,'Destination X cell','number'),(3,'Destination Z cell','number')],
  45: [(1,'Unit whose route is configured','unit'),(3,'Reference unit','unit'),(4,'Route X cell','number'),(5,'Route Z cell','number')],
  47: [(1,'Objective text','message'),(2,'Objective','objective'),(3,'State','objective_state'),(6,'Party name 1','party'),(7,'Party name 2','party')],
  48: [(1,'Unit','unit'),(2,'Objective','objective'),(3,'Operation','target_operation')],
  56: [(1,'Unit sending the flare','unit')],
  66: [(1,'Message','message'),(4,'Party name 1','party'),(5,'Party name 2','party')],
  67: [(1,'Dialogue','dialogue')],
  87: [(1,'Special-target requirement','number'),(2,'Succeeded','bool')],
  98: [(1,'Lighting clock hours (0 to 24)','clock_hour'),(2,'Lighting clock minutes (0 to 59)','clock_minute')],
 }
}


COMMAND_TITLES = {
 'condition':{0:'Check a unit\'s defeat count',4:'Check whether an event has started',5:'Check whether an event has performed its actions',
  6:'Check objective preparation',7:'Check objective progress',8:'Count completed or failed objectives',9:'Check a special-target requirement',
  10:'Check whether a unit entered an area',14:'Check elapsed time',15:'Check a counter',21:'Check a unit\'s status',25:'Check a unit\'s character'},
 'effect':{0:'Control a timer',1:'Control the countdown',2:'Change a counter',3:'Update a counter from player defeats',4:'Choose a random counter value',
  5:'Calculate a counter value',6:'Update a counter from unit health',7:'Change unit flags',8:'Change base flags',9:'Change scenario flags',
  11:'Control automatic system messages',12:'Restore automatic system messages',13:'Operate a map object',14:'Operate a specific map object',
  15:'Create a visual effect',16:'Change the endurance gauge',17:'Change a unit\'s party membership',18:'Change party membership for multiple units',
  19:'Start long-range fire',20:'Stop long-range fire',22:'Revive a unit',23:'Allow an event to run again',24:'Control the battle clock',
  25:'Make a unit appear',26:'Activate a base',27:'Make a unit appear at a specified location',28:'Make a unit appear near another unit',
  29:'Remove a unit from the map',30:'Remove a base from the map',31:'Remove units in an area',32:'Remove bases in an area',
  33:'Set a unit\'s position using map cells',34:'Set a unit\'s world position',35:'Assign a behavior preset',36:'Set another unit as a target',
  37:'Set a map destination',38:'Set a target position',39:'Set a base as a target',40:'Set a special unit target',41:'Set a special map destination',
  42:'Set a special target position',43:'Set a special base target',44:'Stop special movement',45:'Configure a route line',46:'Change movement speed',
  47:'Change an objective and its displayed text',48:'Add or remove a marked objective target',49:'Configure an objective area',50:'Configure an objective base',
  51:'Set objective-related unit invincibility',52:'Set objective-related base invincibility',53:'Configure a side-mission reward',54:'Update an objective',
  55:'Force an objective to end',56:'Control a unit\'s flare signal',57:'Control a repeating unit flare',58:'Control a flare at a map location',
  59:'Control a repeating map flare',60:'Control a base\'s flare signal',61:'Control a repeating base flare',64:'Control a beacon',
  66:'Display a battle message',67:'Play dialogue',68:'Play a voiced system message',69:'Change unit health',70:'Change unit stamina',71:'Change base health',
  72:'Power up a unit',73:'Change a unit\'s gas supply',74:'Change a unit\'s blade supply',75:'Restore damaged Titan body parts',76:'Control Titan regeneration',
  77:'Add an item',78:'Spawn an item',79:'Play a movie',80:'Start a camera sequence',81:'End a camera sequence',82:'Configure victory and defeat requirements',
  83:'Add a unit to a victory or defeat requirement',84:'Set an area for a victory or defeat requirement',85:'Set a base for a victory or defeat requirement',
  86:'Configure a special-target requirement',87:'Set a special-target result',88:'Change background music',89:'Play a sound effect',90:'Show a tutorial',
  91:'Control a tutorial effect',93:'Start an action tutorial',94:'End an action tutorial',96:'Trigger Titan transformation',97:'Set the main goal',
  98:'Change the clock time',99:'Change a unit\'s displayed name',100:'Control unit movement',101:'Create a save point',102:'Display a title',
  103:'Force target lock-on',105:'Start a scripted action sequence',106:'Review an action tutorial',107:'Start a scripted situation',108:'Set an objective position',
  110:'Change buddy-action cooldown',111:'Change a unit\'s portrait',112:'Set the speaker for dialogue',113:'Set the speaker for a system message',
  114:'Change rewards',115:'Change weak-point health',116:'Control the reinforcement timer',117:'Assign a behavior preset with a reserve action'}
}


def friendly_class(name):
    name = re.sub(r'^CSc(?:Cond|Eff)', '', str(name))
    return re.sub(r'(?<=[a-z])(?=[A-Z])', ' ', name)


def choice_widget(options, value=0):
    box=QComboBox();box.setEditable(True)
    box.setInsertPolicy(QComboBox.InsertPolicy.NoInsert)
    box.setMinimumContentsLength(12)
    box.setSizeAdjustPolicy(QComboBox.SizeAdjustPolicy.AdjustToMinimumContentsLengthWithIcon)
    for number,label in options:box.addItem(f'{number} - {label}',number)
    index=box.findData(value)
    if index<0:box.addItem(str(value),value);index=box.count()-1
    box.setCurrentIndex(index)
    box.completer().setFilterMode(Qt.MatchFlag.MatchContains)
    box.completer().setCompletionMode(box.completer().CompletionMode.PopupCompletion)
    return box


def choice_value(box):
    text=box.currentText().strip()
    index=box.findText(text)
    if index>=0:return box.itemData(index)
    matches=[box.itemData(i) for i in range(box.count())
             if box.itemText(i).split(' - ',1)[0].casefold()==text.casefold()]
    if len(matches)==1:return matches[0]
    if len(matches)>1:raise ValueError('Several units have this name. Choose the character or Titan from the list.')
    return int(text.split('-',1)[0].strip(),0)


class UnitPicker(QComboBox):
    """Clickable selection field with search inside the popup, not the value."""
    def __init__(self):
        super().__init__();self.hidden_aliases=set()
        self.panel=QFrame(self,Qt.WindowType.Popup)
        layout=QVBoxLayout(self.panel);layout.setContentsMargins(6,6,6,6)
        self.search=QLineEdit();self.search.setPlaceholderText('Search by name or ID...')
        self.results=QListWidget();layout.addWidget(self.search);layout.addWidget(self.results)
        self.search.textChanged.connect(self.filter_choices)
        self.results.itemClicked.connect(self.choose)
        self.results.itemActivated.connect(self.choose)
        self.search.returnPressed.connect(lambda:self.choose(self.results.currentItem()))
        self.search.installEventFilter(self)
        self.setMinimumContentsLength(12)
        self.setSizeAdjustPolicy(QComboBox.SizeAdjustPolicy.AdjustToMinimumContentsLengthWithIcon)

    def filter_choices(self,text):
        signature=tuple((self.itemText(i),self.itemData(i),self.itemData(i) in self.hidden_aliases) for i in range(self.count()))
        if signature!=getattr(self,'_choice_signature',None):
            self._choice_signature=signature;self.results.clear()
            for i,(label,_,hidden) in enumerate(signature):
                if hidden:continue
                item=QListWidgetItem(label,self.results);item.setData(Qt.ItemDataRole.UserRole,i)
                item.setData(Qt.ItemDataRole.UserRole+1,label.casefold())
        query=text.strip().casefold();selected=None;first=None
        for row in range(self.results.count()):
            item=self.results.item(row);visible=query in item.data(Qt.ItemDataRole.UserRole+1)
            item.setHidden(not visible)
            if visible and first is None:first=item
            if visible and item.data(Qt.ItemDataRole.UserRole)==self.currentIndex():selected=item
        self.results.setCurrentItem(selected or first)

    def showPopup(self):
        with QSignalBlocker(self.search):self.search.clear()
        self.filter_choices('')
        area=self.screen().availableGeometry();width=min(max(self.width(),380),area.width())
        height=min(360,80+max(1,sum(not self.results.item(i).isHidden() for i in range(self.results.count())))*24,area.height());point=self.mapToGlobal(self.rect().bottomLeft())
        x=max(area.left(),min(point.x(),area.right()-width+1))
        y=point.y() if point.y()+height<=area.bottom()+1 else max(area.top(),self.mapToGlobal(self.rect().topLeft()).y()-height)
        self.panel.setGeometry(x,y,width,height);self.panel.show();self.search.setFocus()
        if self.results.currentItem():self.results.scrollToItem(self.results.currentItem())

    def hidePopup(self):
        self.panel.hide();super().hidePopup()

    def choose(self,item):
        if item is None:return
        index=item.data(Qt.ItemDataRole.UserRole)
        self.hidePopup();self.setCurrentIndex(index);self.activated.emit(index)

    def eventFilter(self,watched,event):
        if watched is self.search and event.type()==QEvent.Type.KeyPress:
            if event.key() in (Qt.Key.Key_Down,Qt.Key.Key_Up):
                step=1 if event.key()==Qt.Key.Key_Down else -1
                self.results.setCurrentRow(max(0,min(self.results.count()-1,self.results.currentRow()+step)));return True
            if event.key()==Qt.Key.Key_Escape:self.hidePopup();return True
        return super().eventFilter(watched,event)

    def keyPressEvent(self,event):
        if event.text().isprintable() and event.text().strip() and not event.modifiers() & (Qt.KeyboardModifier.ControlModifier|Qt.KeyboardModifier.AltModifier):
            self.showPopup();self.search.setText(event.text());return
        super().keyPressEvent(event)


def unit_choice(options,value=0):
    """Name-first identity picker; teams never restrict the unit catalog."""
    box=UnitPicker()
    for number,label in options:box.addItem(label,number)
    box.hidden_aliases=set(getattr(options,'hidden_aliases',()))
    index=box.findData(value)
    if index<0:box.addItem(str(value),value);index=box.count()-1
    for i in range(box.count()):
        number=box.itemData(i)
        label=next((label for key,label in options if key==number),None)
        if label is not None:
            family,_,name=label.partition(' · ')
            box.setItemText(i,f'{name} - {family} · ID {number}')
    box.setCurrentIndex(index)
    box.setToolTip('Click to choose or search. Any character or Titan can use any team.')
    return box


class UnitCatalog(list):
    def __init__(self,resolver):
        super().__init__();self.hidden_aliases=set()
        # Unassigned human selector slots repeat descriptor 0 byte-for-byte.
        # Keep their IDs available for displaying existing maps, but offer Eren
        # once in the picker. Different templates and Titan selectors stay intact.
        default=resolver.selectors[:6]
        for selector in range(1001):
            resolved=resolver.resolve(selector);mapping=resolved['active_mapping']
            if not mapping['template_ids']:continue
            names=' / '.join(resolved['candidate_names']) or 'Runtime-selected name'
            equipment=resolver.equipment_label(selector)
            if equipment:names+=f' ({equipment})'
            family={'human':'Character','titan':'Titan'}.get(mapping.get('family'),'Group')
            self.append((selector,f'{family} · {names}'))
            if selector and mapping.get('family')=='human' and resolver.selectors[selector*8:selector*8+6]==default:
                self.hidden_aliases.add(selector)


class CommandDialog(QDialog):
    def __init__(self,editor,kind,words=None):
        super().__init__(editor);self.editor=editor;self.kind=kind
        self.original=list(words or [0]*16);self.widgets={};self.words=None
        self.setWindowTitle('Edit condition' if kind=='condition' else 'Edit action');self.resize(650,640)
        layout=QVBoxLayout(self)
        names=editor.command_catalog[kind]
        self.command=choice_widget([(op,COMMAND_TITLES.get(kind,{}).get(op,friendly_class(meta['class_name']))) for op,meta in names.items()
                                   if op not in (0xFE,0xFF)],self.original[0])
        layout.addWidget(QLabel('What must be true?' if kind=='condition' else 'What should happen?'))
        layout.addWidget(self.command)
        self.explanation=QLabel();self.explanation.setWordWrap(True);layout.addWidget(self.explanation)
        scroll=QScrollArea();scroll.setWidgetResizable(True);layout.addWidget(scroll,1)
        self.form_widget=QWidget();self.form=QFormLayout(self.form_widget);scroll.setWidget(self.form_widget)
        self.advanced=QCheckBox('Advanced binary fields');self.advanced.setChecked(editor.debug_mode)
        layout.addWidget(self.advanced);self.advanced.setVisible(editor.debug_mode);self.advanced.toggled.connect(self.rebuild)
        buttons=QDialogButtonBox(QDialogButtonBox.StandardButton.Ok|QDialogButtonBox.StandardButton.Cancel)
        buttons.accepted.connect(self.accept_words);buttons.rejected.connect(self.reject);layout.addWidget(buttons)
        self.command.currentIndexChanged.connect(self.change_command);self.rebuild()

    def capture(self):
        words=list(self.original)
        for index,(widget,kind) in self.widgets.items():
            value=choice_value(widget) if isinstance(widget,QComboBox) else widget.value()
            if kind=='int32':words[index:index+2]=struct.unpack('<2H',struct.pack('<i',value))
            else:
                scenario.require(-32768<=value<=32767 if kind=='signed' else 0<=value<=65535,'Parameter is outside its stored range')
                words[index]=value&65535
        return words

    def change_command(self):
        try:op=choice_value(self.command)
        except ValueError:return
        self.original=[op]+[0]*15;self.widgets={};self.rebuild()

    def rebuild(self,*_):
        if self.widgets:self.original=self.capture()
        while self.form.rowCount():self.form.removeRow(0)
        self.widgets={};op=self.original[0]
        fields=list(EDIT_FIELDS[self.kind].get(op,[]));used={0}
        for index in ENTITY_OPERANDS[self.kind].get(op,[]):
            if not any(field[0]==index for field in fields):fields.append((index,'Unit reference','unit'))
        for index,label,kind in fields:
            used.add(index)
            if kind=='int32':used.add(index+1)
            self.add_field(index,label,kind)
        if self.advanced.isChecked():
            for index in range(1,16):
                if index not in used:self.add_field(index,f'Word +0x{index*2:02X} (meaning not decoded)','number')
        self.explanation.setText(self.editor.row_label(self.kind,self.original)
            + ('\nNo decoded parameter names for this command. Copy an existing action or enable Debug for binary fields.' if not fields else ''))

    def add_field(self,index,label,kind):
        value=self.original[index]
        options=self.editor.operand_options(kind)
        if options:widget=choice_widget(options,value)
        else:
            widget=QSpinBox()
            widget.setRange(-2147483648,2147483647) if kind=='int32' else widget.setRange(-32768,32767) if kind=='signed' else widget.setRange(0,65535)
            if kind in ('clock_hour','clock_minute'):widget.setRange(0,max(value,24 if kind=='clock_hour' else 59))
            if kind=='int32':value=struct.unpack('<i',struct.pack('<2H',*self.original[index:index+2]))[0]
            elif kind=='signed' and value>=32768:value-=65536
            widget.setValue(value)
        self.widgets[index]=(widget,kind);self.form.addRow(label,widget)

    def accept_words(self):
        try:
            scenario.require(choice_value(self.command)==self.original[0],'Choose the command from the searchable list')
            self.words=self.capture()
            scenario.require(self.words[0] in self.editor.command_catalog[self.kind],'Select a command from the executable catalog')
            self.editor.validate_references(self.kind,self.words)
        except Exception as error:QMessageBox.warning(self,'Invalid command',str(error));return
        self.accept()


DARK_STYLE = '''
QWidget { background: #101114; color: #e6e7eb; font-family: "Segoe UI"; font-size: 12px; }
QMainWindow, QDialog { background: #090a0c; }
QToolBar { background: #14161b; border: 0; spacing: 4px; padding: 3px; }
QToolButton, QPushButton { background: #24272f; border: 1px solid #363a46; border-radius: 5px; padding: 4px 8px; }
QToolButton:hover, QPushButton:hover { background: #353b49; }
QToolButton:checked, QPushButton:checked { background: #24466b; border-color: #5da7f4; }
QPushButton:disabled, QToolButton:disabled { color: #696e7a; }
QLineEdit, QSpinBox, QDoubleSpinBox, QComboBox { background: #191c22; border: 1px solid #343945; border-radius: 4px; padding: 5px; }
QComboBox QAbstractItemView { background: #191c22; selection-background-color: #294a71; }
QListWidget, QTreeWidget, QPlainTextEdit, QTextBrowser { background: #0d0f13; border: 1px solid #292d36; border-radius: 4px; }
QListWidget::item, QTreeWidget::item { padding: 2px 3px; }
QListWidget::item:selected, QTreeWidget::item:selected { background: #264466; }
QTabWidget::pane { border: 1px solid #292d36; }
QTabBar::tab { background: #16191f; padding: 5px 9px; border-bottom: 2px solid transparent; }
QTabBar::tab:selected { background: #242a34; border-bottom-color: #74b7ff; }
QDockWidget::title { background: #191c22; padding: 8px; font-weight: bold; }
QSplitter::handle { background: #292e38; }
QScrollBar:vertical { background: #14161a; width: 10px; }
QScrollBar::handle:vertical { background: #434a58; min-height: 30px; border-radius: 4px; }
QScrollBar::add-line:vertical, QScrollBar::sub-line:vertical { height: 0; }
QToolTip { background: #252c37; color: #fff; border: 1px solid #566073; padding: 5px; }
QStatusBar { color: #aeb6c4; background: #12151a; }
'''


class TeamRows(QStyledItemDelegate):
    def initStyleOption(self,option,index):
        super().initStyleOption(option,index)
        brush=index.data(Qt.ItemDataRole.ForegroundRole)
        if brush is not None:
            # Selection changes the background, never the unit's team color.
            option.palette.setBrush(QPalette.ColorRole.HighlightedText,brush)


class WrappedRows(QStyledItemDelegate):
    def sizeHint(self,option,index):
        view=self.parent();width=view.viewport().width()-20
        if isinstance(view,QTreeWidget):
            depth=1;parent=index.parent()
            while parent.isValid():depth+=1;parent=parent.parent()
            width-=depth*view.indentation()
        text=str(index.data() or '')
        box=option.fontMetrics.boundingRect(QRect(0,0,max(40,width),10000),Qt.TextFlag.TextWordWrap,text)
        return QSize(max(40,width),max(28,box.height()+14))


class EditorWindow(MapWindow):
    clipboard=None
    def __init__(self,document):
        self.document=document;self.entity_id=None;self.edit_event_id=0;self.loading=False;self.entity_loading=False
        self.command_catalog=executable_command_names(document.game_root/'AoT2_EU.exe')
        self.resolver=InstalledNameResolver.from_game(document.game_root,document.sections[4])
        self.catalog=UnitCatalog(self.resolver)
        entities,missing,result=read_entities(document.result)
        backgrounds=load_backgrounds(result)
        super().__init__(entities,missing,backgrounds,result)
        self.setStyleSheet(DARK_STYLE);self.resize(1500,980)
        self.text_choice.setCurrentText('Minimal')
        self.event_choice.setSizeAdjustPolicy(QComboBox.SizeAdjustPolicy.AdjustToMinimumContentsLengthWithIcon)
        self.event_choice.setMinimumContentsLength(20)
        self.team_legend.setText('Blue / red / purple / gray: starting team • Orange: bases • Hollow: inactive / conditional')
        layout=self.centralWidget().layout();layout.removeWidget(self.view);layout.removeWidget(self.details)
        # Keep view options accessible without permanently occupying map space.
        self.view_options=QDialog(self);self.view_options.setWindowTitle('Map view');options=QVBoxLayout(self.view_options)
        while layout.count():
            item=layout.takeAt(0)
            if item.layout():options.addLayout(item.layout())
            elif item.widget():options.addWidget(item.widget())
        self.debug_button.hide()
        for label in self.view_options.findChildren(QLabel):
            if label.text()=='Wheel: zoom • Drag: pan':label.hide()
        self.count_label.hide();self.zoom_label.hide()
        layout.setSpacing(0);layout.addWidget(self.view,1)
        self.details.setMinimumHeight(0);self.details.setMaximumHeight(16777215)
        self.details.setTabVisible(2,False)
        self.create_toolbar();self.create_sidebar()
        self.create_environment_page()
        self.editor_tabs.addTab(self.details,'Info')
        self.view.selection_changed.connect(self.map_selection_changed);self.view.moved_many.connect(self.move_entities)
        self.refresh_lists();self.select_editor_event(0);self.update_title()
        self.statusBar().hide()
        self.resizeDocks([self.dock],[350],Qt.Orientation.Horizontal)
        self.setAttribute(Qt.WidgetAttribute.WA_DeleteOnClose)
        app=QApplication.instance()
        if not hasattr(app,'editor_windows'):app.editor_windows={}
        app.editor_windows[id(self)]=self
        self.destroyed.connect(lambda _=None,key=id(self),windows=app.editor_windows:windows.pop(key,None))


    def create_environment_page(self):
        page=QWidget();layout=QVBoxLayout(page);self.editor_tabs.addTab(page,'Environment')
        title=QLabel('Weather and lighting');title.setStyleSheet('font-size: 16px; font-weight: bold;')
        layout.addWidget(title)
        self.environment_preset=QComboBox();layout.addWidget(self.environment_preset)
        self.environment_preset.setAccessibleName('Weather and lighting')
        self.environment_preset.currentIndexChanged.connect(self.environment_preset_changed)
        self.environment_note=QLabel();self.environment_note.setWordWrap(True)
        self.environment_note.hide();layout.addWidget(self.environment_note)
        self.environment_debug=QLabel();self.environment_debug.setWordWrap(True)
        self.environment_debug.setTextInteractionFlags(Qt.TextInteractionFlag.TextSelectableByMouse)
        layout.addWidget(self.environment_debug);layout.addStretch(1)
        self.refresh_environment()

    def refresh_environment(self):
        if not hasattr(self,'environment_preset'):return
        try:
            store=self.document.map_store;mission=self.document.result['mission']['mission_id']
            original=store.environment_original();stage=original[mission*88+2]
            options,snow_supported=environment_options(str(self.document.game_root),stage)
            values=environment_values(self.document)
            lighting,minutes,snow,rain=environment_starting_values(self.document,snow_supported)
            available={i for i,_,_ in options}
            selected=f'random:{snow}:{rain}' if 2 in (snow,rain) else f'lighting:{lighting}'
            with QSignalBlocker(self.environment_preset):
                self.environment_preset.clear()
                for i,label,_ in options:
                    if i==6 and not snow_supported:continue
                    if i==4:label='Rain'
                    self.environment_preset.addItem(label,f'lighting:{i}')
                for label,s,r in ENVIRONMENT_WEATHER:
                    if 2 not in (s,r):continue
                    if s and not (snow_supported and 6 in available):continue
                    if r and 4 not in available:continue
                    self.environment_preset.addItem(label,f'random:{s}:{r}')
                index=self.environment_preset.findData(selected)
                if index<0:
                    self.environment_preset.addItem('Current map environment',None)
                    index=self.environment_preset.count()-1
                    self.environment_preset.model().item(index).setEnabled(False)
                self.environment_preset.setCurrentIndex(index)
            self.environment_preset.setEnabled(True);self.environment_note.hide()
            clocks=[str(i) for i,e in enumerate(self.document.events) if any(w[0]==98 for w in e['effects'])]
            self.environment_debug.setText(f'DataScenarioBase mission {mission}, row +04/+05/+06/+07: {values}\n'
                f'Stage {stage}, DataStage +60 snow support: {snow_supported}\n'
                f'Starting lighting: {lighting}; clock: {minutes//60:02}:{minutes%60:02}\n'
                f'Clock events: {", ".join(clocks) or "None"}\n'
                'Readers: FUN_140dbfae0, FUN_140dbeef0; environment loader: FUN_140d3a3c0\n'
                'Clock action: CScEffChangeClockTime, FUN_140d09950 / FUN_140d098d0')
            self.environment_debug.setVisible(self.debug_mode)
        except Exception as error:
            self.environment_note.setText(str(error));self.environment_note.show()
            self.environment_preset.setEnabled(False);self.environment_debug.hide()

    def environment_preset_changed(self,*_):
        selection=self.environment_preset.currentData()
        if selection is None:return
        lighting,hour,snow,rain=environment_values(self.document)
        parts=selection.split(':')
        if parts[0]=='lighting':
            lighting=int(parts[1]);snow=1 if lighting==6 else 0;rain=1 if lighting==4 else 0
            if snow:hour=0
            elif rain:hour=24
        else:snow,rain=map(int,parts[1:])
        values=(lighting,hour,snow,rain)
        self.mutate('Changed weather and lighting',lambda:set_environment_values(self.document,values))

    def create_toolbar(self):
        toolbar=QToolBar('Editor');toolbar.setMovable(False);self.addToolBar(toolbar)
        def action(label,callback,shortcut=None,checkable=False,visible=True):
            item=QAction(label,self);item.setCheckable(checkable)
            if shortcut:item.setShortcut(QKeySequence(shortcut))
            item.triggered.connect(callback)
            if visible:toolbar.addAction(item)
            else:self.addAction(item)
            return item
        action('Maps',self.open_archives,'Ctrl+L')
        files=QToolButton();files.setText('File');files.setPopupMode(QToolButton.ToolButtonPopupMode.InstantPopup)
        menu=QMenu(files);files.setMenu(menu);toolbar.addWidget(files)
        menu.addAction(action('Open .binmap...',self.open_binmap,'Ctrl+O',visible=False))
        menu.addAction(action('Revert maps...',self.revert_maps,visible=False))
        action('Save',self.save_current,'Ctrl+S');self.archive_save_action=action('Inject',self.save_archive)
        toolbar.addSeparator()
        self.undo_action=action('Undo',lambda:self.history(False),'Ctrl+Z')
        self.redo_action=action('Redo',lambda:self.history(True),'Ctrl+Y')
        edits=QToolButton();edits.setText('Edit');edits.setPopupMode(QToolButton.ToolButtonPopupMode.InstantPopup)
        menu=QMenu(edits);edits.setMenu(menu);toolbar.addWidget(edits)
        for name,key,callback in [('Copy','Ctrl+C',self.copy_selection),('Cut','Ctrl+X',self.cut_selection),
                                  ('Paste','Ctrl+V',self.paste_selection),('Duplicate','Ctrl+D',self.duplicate_unit)]:
            menu.addAction(action(name,callback,key,visible=False))
        self.snap_group=QWidget();self.snap_group.setObjectName('snap_group')
        self.snap_group.setStyleSheet('''
            QWidget#snap_group { background: #292e36; border-radius: 6px; }
            QWidget#snap_group QLabel { background: transparent; }
        ''')
        snap_layout=QHBoxLayout(self.snap_group);snap_layout.setContentsMargins(7,4,7,4);snap_layout.setSpacing(7)
        toolbar.addWidget(self.snap_group)
        self.snap_toggle=QPushButton('Snap to grid');self.snap_toggle.setCheckable(True)
        self.snap_toggle.setMinimumWidth(64)
        self.snap_toggle.setStyleSheet('''
            QPushButton { background: #555b65; color: #ffffff; border: 1px solid #777f8c; font-weight: bold; padding: 5px 12px; }
            QPushButton:hover { background: #666e79; }
            QPushButton:checked { background: #008000; color: #ffffff; border: 1px solid #20a020; }
            QPushButton:checked:hover { background: #009000; }
        ''')
        snap_layout.addWidget(self.snap_toggle)
        snap_layout.addWidget(QLabel('Pixels'))
        self.snap_pixels=QSpinBox();self.snap_pixels.setRange(1,4096);self.snap_pixels.setValue(16)
        self.snap_pixels.setFixedWidth(76);snap_layout.addWidget(self.snap_pixels)
        snap_layout.addWidget(QLabel('Offset'))
        self.snap_offset=QSpinBox();self.snap_offset.setRange(-4096,4096)
        self.snap_offset.setFixedWidth(82);snap_layout.addWidget(self.snap_offset)
        for field in (self.snap_pixels,self.snap_offset):
            field.setButtonSymbols(QSpinBox.ButtonSymbols.NoButtons)
            field.setStyleSheet('''
                QSpinBox { background: #454d59; color: #ffffff; border: 1px solid #788495; border-radius: 4px; padding: 5px 8px; }
                QSpinBox:disabled { background: #343a44; color: #aab2be; border-color: #555e6c; }
            ''')
        self.snap_pixels.setToolTip('Grid spacing in pixels of the selected map image; independent of zoom.')
        self.snap_offset.setToolTip('Shift the grid origin by this many image pixels on both axes.')
        self.snap_toggle.setToolTip('Snap dragged markers and pasted selections to the grid. Groups keep their spacing.')
        self.snap_toggle.toggled.connect(self.update_snap)
        self.snap_pixels.valueChanged.connect(self.update_snap);self.snap_offset.valueChanged.connect(self.update_snap)
        self.update_snap()
        spacer=QWidget();spacer.setSizePolicy(QSizePolicy.Policy.Expanding,QSizePolicy.Policy.Preferred);toolbar.addWidget(spacer)
        action('View',self.view_options.show)
        self.sidebar_action=action('Sidebar',lambda checked:self.dock.setVisible(checked),'F9',True)
        self.sidebar_action.setChecked(True)
        self.debug_action=action('Debug',self.set_debug_mode,None,True)
        action('Help',self.show_help,'F1')

    def update_snap(self,*_):
        enabled=self.snap_toggle.isChecked()
        self.snap_pixels.setEnabled(enabled);self.snap_offset.setEnabled(enabled)
        self.view.snap_enabled=enabled;self.view.snap_pixels=self.snap_pixels.value();self.view.snap_offset=self.snap_offset.value()

    def show_help(self):
        QMessageBox.information(self,'Editor help',
            'MAP CONTROLS\n'
            'Left-click a marker to select it. Drag empty space to select a rectangle.\n'
            'Ctrl+click toggles one marker without clearing the others. Ctrl+drag adds another rectangle.\n'
            'Drag a selected marker to move the selection together.\n'
            'Snap: Pixels sets the grid spacing; Offset shifts its origin on both axes.\n'
            'Grid values use the selected image pixels, independent of zoom. Groups keep their spacing.\n'
            'Middle-drag or arrow keys: pan. Mouse wheel: zoom. View: filters, labels, image and Fit.\n\n'
            'SHORTCUTS\n'
            'Ctrl+C: copy selected units and bases. Ctrl+D: duplicate them nearby.\n'
            'Ctrl+X: pick up the selection. Ctrl+V: place it at the pointer (or map center).\n'
            'Cut keeps existing IDs and event links; it commits on paste. Escape cancels it.\n'
            'Ctrl+Z / Ctrl+Y: undo / redo. A group move or paste is one undo step.\n'
            'Ctrl+S: save. Ctrl+O: open a saved map. Ctrl+L: map library. F9: sidebar.\n\n'
            'SIDEBAR\n'
            'Click Unit or Team anywhere to open its list; search inside the popup.\n'
            'Unit entries show their template equipment: Guns or Blades. Pick that variant, then choose any team.\n'
            'Equipment comes from the character template, independently of team. This does not override player loadouts.\n'
            'Only equipment variants present in the installed catalog are offered; there is no separate weapon override.\n'
            'Units and Bases have separate tabs. A single selection opens its matching tab.\n'
            'Multiple selection keeps your current tab. Fields apply to selected items of that tab\'s type.\n'
            'Only the changed field is applied. Mixed means selected items have different values.\n'
            'Coordinate fields set that axis for the selected type; dragging moves the whole selection together.\n'
            'Info shows descriptions and appearance requirements.\n'
            'Debug reveals script traces, binary information and image references.\n'
            'Save creates a modified map. Inject applies it to the game.\n\n'+TEAM_LEGEND)


    def create_sidebar(self):
        self.dock=QDockWidget('Editor',self);self.dock.setObjectName('scenario_editor')
        self.dock.setTitleBarWidget(QWidget())
        self.dock.setAllowedAreas(Qt.DockWidgetArea.LeftDockWidgetArea|Qt.DockWidgetArea.RightDockWidgetArea)
        self.dock.visibilityChanged.connect(self.sidebar_action.setChecked)
        self.addDockWidget(Qt.DockWidgetArea.RightDockWidgetArea,self.dock)
        tabs=QTabWidget();tabs.setMinimumWidth(310);self.dock.setWidget(tabs);self.editor_tabs=tabs
        unit_page=QWidget();units=QVBoxLayout(unit_page);tabs.addTab(unit_page,'Units')
        base_page=QWidget();bases=QVBoxLayout(base_page);tabs.addTab(base_page,'Bases')
        self.entity_panes=(units,bases)
        self.base_search=QLineEdit();self.base_search.setPlaceholderText('Search bases or ID...')
        self.base_search.textChanged.connect(self.filter_lists);bases.addWidget(self.base_search)
        self.base_list=QListWidget();self.base_list.setMaximumHeight(150)
        self.base_list.setSelectionMode(QAbstractItemView.SelectionMode.ExtendedSelection)
        self.base_list.setItemDelegate(TeamRows(self.base_list));bases.addWidget(self.base_list)
        self.base_list.itemSelectionChanged.connect(lambda:self.list_selection_changed(self.base_list))
        self.add_buttons(bases,[('Add base',self.add_base),('Duplicate',self.duplicate_unit)])
        self.entity_search=QLineEdit();self.entity_search.setPlaceholderText('Search units, Titans or ID...')
        self.entity_search.textChanged.connect(self.filter_lists);units.addWidget(self.entity_search)
        self.entity_list=QListWidget();self.entity_list.setMaximumHeight(150);self.entity_list.setSelectionMode(QAbstractItemView.SelectionMode.ExtendedSelection);units.addWidget(self.entity_list)
        self.entity_list.setItemDelegate(TeamRows(self.entity_list))
        self.entity_list.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.entity_list.itemSelectionChanged.connect(self.list_selection_changed)
        self.add_buttons(units,[('Add unit',self.add_unit),('Duplicate',self.duplicate_unit)])
        scroll=QScrollArea();scroll.setWidgetResizable(True);units.addWidget(scroll,1);self.entity_scroll=scroll
        body=QWidget();scroll.setWidget(body);body_layout=QVBoxLayout(body)
        self.entity_heading=QLabel('Select a unit or base');self.entity_heading.setWordWrap(True)
        self.entity_heading.setStyleSheet('font-size: 16px; font-weight: bold;');body_layout.addWidget(self.entity_heading)
        self.portrait=QLabel('');self.portrait.setAlignment(Qt.AlignmentFlag.AlignCenter);self.portrait.setFixedHeight(110)
        body_layout.addWidget(self.portrait)
        self.image_candidates=QComboBox();self.image_candidates.currentIndexChanged.connect(self.show_portrait);body_layout.addWidget(self.image_candidates)
        self.portrait_style=QComboBox();self.portrait_style.addItems(['Titan Log image','Thumbnail / portrait'])
        self.portrait_style.currentIndexChanged.connect(self.show_portrait);body_layout.addWidget(self.portrait_style)
        self.image_source=QLabel();self.image_source.setWordWrap(True);self.image_source.setStyleSheet('color:#9ba7b8;');body_layout.addWidget(self.image_source);self.image_source.hide()
        self.entity_form=QFormLayout();self.entity_form.setFieldGrowthPolicy(QFormLayout.FieldGrowthPolicy.AllNonFixedFieldsGrow);body_layout.addLayout(self.entity_form)
        self.selector_edit=unit_choice(self.catalog);self.entity_form.addRow('Unit',self.selector_edit)
        self.team_edit=UnitPicker();self.team_edit.search.setPlaceholderText('Search teams...')
        for team,label in TEAM_LABELS.items():self.team_edit.addItem(label,team)
        self.entity_form.addRow('Team',self.team_edit)
        self.selector_edit.activated.connect(self.apply_entity)
        self.team_edit.activated.connect(self.apply_entity)
        self.hidden_edit=QCheckBox('Visible');self.entity_form.addRow('Starting state',self.hidden_edit)
        self.hidden_edit.toggled.connect(self.apply_entity)
        self.coordinates=[]
        for label in ('X','Y','Z'):
            spin=QSpinBox();spin.setRange(-2147483648,2147483647);spin.setSingleStep(100)
            self.coordinates.append(spin);self.entity_form.addRow(label,spin)
            spin.valueChanged.connect(self.position_changed)
            spin.editingFinished.connect(self.finish_position_edit)
        self.heading_edit=QSpinBox();self.heading_edit.setRange(0,315);self.heading_edit.setSingleStep(45);self.heading_edit.setSuffix('°')
        self.heading_edit.setKeyboardTracking(False);self.heading_edit.valueChanged.connect(self.apply_entity)
        self.entity_form.addRow('Heading',self.heading_edit)
        self.base_type=QSpinBox();self.base_type.setRange(0,65535);self.entity_form.addRow('Base type',self.base_type)
        self.base_type.setKeyboardTracking(False);self.base_type.valueChanged.connect(self.apply_entity)
        self.appearance_button=QPushButton('Appearance...');self.appearance_button.clicked.connect(self.add_appearance);units.addWidget(self.appearance_button)
        self.entity_note=QLabel('Drag markers to move them.');self.entity_note.setWordWrap(True);body_layout.addWidget(self.entity_note);self.entity_note.hide()
        body_layout.addStretch()
        event_page=QWidget();events=QVBoxLayout(event_page);tabs.addTab(event_page,'Events')
        self.event_search=QLineEdit();self.event_search.setPlaceholderText('Search all events or action names…')
        self.event_search.textChanged.connect(self.filter_lists);events.addWidget(self.event_search)
        self.event_list=QListWidget();self.event_list.setMaximumHeight(160);events.addWidget(self.event_list)
        self.event_list.setWordWrap(True);self.event_list.setTextElideMode(Qt.TextElideMode.ElideNone)
        self.event_list.setItemDelegate(WrappedRows(self.event_list))
        self.event_list.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.event_list.currentItemChanged.connect(self.event_list_selected)
        self.add_buttons(events,[('New event',self.add_event),('Duplicate event',self.duplicate_event)])
        self.event_heading=QLabel();self.event_heading.setWordWrap(True);events.addWidget(self.event_heading)
        self.parent_event_button=QPushButton();self.parent_event_button.clicked.connect(self.open_parent_event);events.addWidget(self.parent_event_button)
        self.disabled_event=QCheckBox('Disabled');self.disabled_event.toggled.connect(self.toggle_event);events.addWidget(self.disabled_event)
        self.disabled_event.setText('Disable this event')
        self.event_pages=QTabWidget();events.addWidget(self.event_pages,1)
        when_page=QWidget();when=QVBoxLayout(when_page);when.setContentsMargins(4,6,4,4)
        self.event_pages.addTab(when_page,'Conditions')
        self.when_explanation=QLabel();self.when_explanation.setWordWrap(True);when.addWidget(self.when_explanation)
        self.conditions=QTreeWidget();self.conditions.setHeaderLabel('Requirements');when.addWidget(self.conditions,1)
        self.conditions.setTextElideMode(Qt.TextElideMode.ElideNone)
        self.conditions.setWordWrap(True)
        self.conditions.setItemDelegate(WrappedRows(self.conditions));self.conditions.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.conditions.header().setSectionResizeMode(QHeaderView.ResizeMode.Stretch)
        self.conditions.itemDoubleClicked.connect(lambda *_:self.edit_condition())
        self.add_buttons(when,[('Add condition',self.add_condition),('Require all',lambda:self.add_condition(0xFF)),('Allow any',lambda:self.add_condition(0xFE))])
        self.add_buttons(when,[('Edit',self.edit_condition),('Duplicate',self.copy_condition),('Remove',self.remove_condition),('↑',lambda:self.move_condition(-1)),('↓',lambda:self.move_condition(1))])
        then_page=QWidget();then=QVBoxLayout(then_page);then.setContentsMargins(4,6,4,4)
        self.event_pages.insertTab(0,then_page,'Actions');self.event_pages.setCurrentIndex(0)
        self.then_explanation=QLabel();self.then_explanation.setWordWrap(True);then.addWidget(self.then_explanation)
        self.event_group_links=QLabel();self.event_group_links.setWordWrap(True)
        self.event_group_links.setOpenExternalLinks(False)
        self.event_group_links.linkActivated.connect(lambda link:self.select_editor_event(int(link.split(':')[-1])))
        then.addWidget(self.event_group_links)
        self.actions=QListWidget();then.addWidget(self.actions,1);self.actions.itemDoubleClicked.connect(lambda *_:self.edit_effect())
        self.actions.setTextElideMode(Qt.TextElideMode.ElideNone)
        self.actions.setWordWrap(True)
        self.actions.setItemDelegate(WrappedRows(self.actions));self.actions.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.add_buttons(then,[('Add action',self.add_effect),('Edit',self.edit_effect),('Duplicate',self.copy_effect),('Remove',self.remove_effect)])
        self.add_buttons(then,[('Move up',lambda:self.move_effect(-1)),('Move down',lambda:self.move_effect(1)),('Script trace',self.trace_selected_event)])
        self.entity_scroll.widget().setEnabled(False);self.appearance_button.setEnabled(False)
        tabs.currentChanged.connect(self.entity_tab_changed)

    @staticmethod
    def add_buttons(layout,entries):
        row=QHBoxLayout();row.setSpacing(4)
        for label,callback in entries:
            button=QPushButton(label);button.clicked.connect(lambda checked=False,cb=callback:cb());row.addWidget(button)
            if label=='Script trace':button.setObjectName('debug_trace_button');button.hide()
        layout.addLayout(row)

    def operand_options(self,kind):
        if kind=='unit':return [(i,unit_name(self.result,i)) for i in range(len(self.document.units)+1)]
        if kind=='base':return [(i,f'Base {i+1}') for i in range(len(self.document.bases))]
        if kind=='party':return list(enumerate(self.result['party_names']))
        if kind in ('message','dialogue'):
            return [(row['index'],row['text']) for row in self.result['texts'].get('messages/ENG' if kind=='message' else 'dialogue/ENG',[])]
        if kind=='selector':return self.catalog
        if kind=='event':return [(i,self.event_label(i)) for i in range(len(self.document.events))]
        if kind=='objective':
            ids={c['raw_u16'][1] for e in self.result['behavior']['events'] for c in e['conditions'] if c['opcode'] in (6,7)}
            ids.update(c['raw_u16'][2] for e in self.result['behavior']['events'] for c in e['effects'] if c['opcode'] in (0x2F,0x30))
            return [(i,objective_label(self.result,i)) for i in sorted(ids)]
        return {'comparison':list(COMPARISONS.items()),'objective_state':list(OBJECTIVE_STATES.items()),
            'bool':[(0,'No'),(1,'Yes')],'result':[(0,'Completed'),(1,'Failed'),(2,'Completed or failed')],
            'objective_category':[(0,'Main'),(1,'Side'),(2,'Main and side')],
            'timer_operation':[(0,'Start'),(1,'Stop'),(2,'Reset'),(3,'Add'),(4,'Subtract')],
            'counter_operation':[(0,'Set'),(1,'Add')],'target_operation':[(0,'Add target'),(1,'Remove target')]}.get(kind,[])

    def validate_references(self,kind,words):
        if kind=='effect' and words[0]==98:
            scenario.require(0<=words[1]<=24 and 0<=words[2]<=59 and (words[1]<24 or words[2]==0),
                             'Lighting clock must be between 00:00 and 24:00')
        for index in ENTITY_OPERANDS[kind].get(words[0],[]):
            scenario.require(words[index]<=len(self.document.units) or words[index]==65535,'Unit ID is outside this scenario')
        for index,_,field in EDIT_FIELDS[kind].get(words[0],[]):
            if field=='unit':scenario.require(words[index]<=len(self.document.units) or words[index]==65535,'Unit ID is outside this scenario')
            if field=='base':scenario.require(words[index]<len(self.document.bases),'Base ID is outside this scenario')
            if field=='event':scenario.require(words[index]<len(self.document.events),'Event ID is outside this scenario')

    def row_label(self,kind,words):
        if kind=='condition' and words[0] in (0xFE,0xFF):return 'Every condition below must pass' if words[0]==0xFF else 'At least one condition below must pass'
        if kind=='effect' and words[0]==0x1A:return f'Activate base {words[1]+1}, type {words[2]}, after {words[3]/60:g}s'
        command=scenario.parse_child(struct.pack('<16H',*words),kind,0,len(self.document.units))
        command.update(self.command_catalog[kind].get(words[0],{}));decode_command(command)
        return command_description(command,self.result).replace(' (additional parameters available in Debug mode)','')

    def event_label(self,index):
        event=self.document.events[index]
        if event['header'][9]&4:
            count=len(self.event_children(index))
            return f'Event {index}: Shared requirements for {count} other events'
        if not event['effects']:return f'Event {index}: No actions configured'
        first=event['effects'][0]
        title=COMMAND_TITLES['effect'].get(first[0],self.row_label('effect',first))
        return f'Event {index}: {title}\n{len(event["effects"])} action'+('s' if len(event['effects'])!=1 else '')

    def event_children(self,index):
        if not self.document.events[index]['header'][9]&4:return []
        # Event 0 is the top-level sentinel, not an additional parent gate.
        return [i for i,e in enumerate(self.document.events) if i!=index and struct.unpack_from('<I',e['header'])[0]==index]

    def update_title(self):
        self.setWindowTitle(f"{'* ' if self.document.dirty else ''}AoT2 1.17 - {self.result['mission']['name']}")
        self.undo_action.setEnabled(bool(self.document.undo_stack));self.redo_action.setEnabled(bool(self.document.redo_stack))

    def refresh_lists(self):
        self.loading=True;self.entity_list.clear();self.base_list.clear();self.event_list.clear()
        for entity in self.entities:
            item=QListWidgetItem(entity['marker_label']);item.setData(Qt.ItemDataRole.UserRole,entity['index'])
            item.setToolTip(entity['marker_label'])
            item.setForeground(QColor(BASE_COLOR if entity['index']<0 else TEAM_COLORS[entity['initial_team']]))
            listing=self.base_list if entity['index']<0 else self.entity_list;listing.addItem(item)
            if entity['index']==self.entity_id:listing.setCurrentItem(item,QItemSelectionModel.SelectionFlag.NoUpdate)
            item.setSelected(entity['index'] in self.view.selected_ids)
        for index in range(len(self.document.events)):
            item=QListWidgetItem(self.event_label(index));item.setData(Qt.ItemDataRole.UserRole,index);self.event_list.addItem(item)
            item.setToolTip(item.text())
            event=self.document.events[index]
            searchable=[item.text()]+[self.row_label('effect',w) for w in event['effects']]+requirement_lines(self.result,index)
            item.setData(Qt.ItemDataRole.UserRole+1,'\n'.join(searchable).casefold())
            if index==self.edit_event_id:self.event_list.setCurrentItem(item)
        self.loading=False;self.filter_lists()

    def filter_lists(self,*_):
        for widget,search in ((self.entity_list,self.entity_search),(self.base_list,self.base_search),(self.event_list,self.event_search)):
            query=search.text().casefold()
            for index in range(widget.count()):
                item=widget.item(index);text=item.data(Qt.ItemDataRole.UserRole+1) if widget is self.event_list else None
                item.setHidden(query not in (text or item.text().casefold()))

    def mutate(self,label,operation):
        try:
            if not self.document.change(label,operation):return False
        except Exception as error:
            self.document.refresh_kind='full'
            QMessageBox.warning(self,'Cannot apply change',str(error));self.refresh_editor();return False
        self.refresh_editor();self.statusBar().showMessage(label,5000);return True

    def refresh_editor(self):
        if self.document.refresh_kind=='placements':
            updated,_,self.result=read_entities(self.document.result)
            by_id={e['index']:e for e in updated}
            for entity in self.entities:entity.update(by_id[entity['index']])
            self.view.update_positions();self.view.hit_regions=[];self.view.update()
            selected=next((e for e in self.entities if e['index']==self.entity_id),None)
            if selected:
                for widget,value in zip(self.coordinates,selected['xyz']):
                    with QSignalBlocker(widget):widget.setValue(round(value))
                if selected['index']>=0:
                    with QSignalBlocker(self.heading_edit):self.heading_edit.setValue(int(selected['heading'])%360)
                self.mark_mixed_fields();self.describe(selected)
            self.update_title()
            return
        self.refresh_environment()
        selected_path=self.condition_path();selected_action=self.actions.currentRow()
        self.entities,self.missing,self.result=read_entities(self.document.result)
        self.events=preview_events(self.result,self.entities)
        # Rebuild the cheap marker/text cache in place; toolbar callbacks retain
        # the same widget, and cached map pixmaps are never decoded on edits.
        text_cache={(e['marker_label'],e['short_label']):texts for e,_,_,texts in self.view.markers}
        self.view.entities=self.entities;self.view.markers=[]
        self.view.selected_ids.intersection_update(e['index'] for e in self.entities)
        for entity in self.entities:
            texts=text_cache.get((entity['marker_label'],entity['short_label']))
            if texts is None:
                texts={}
                for mode,label in [('Full',entity['marker_label']),('Minimal',entity['short_label'])]:
                    text=QStaticText(label);text.setTextFormat(Qt.TextFormat.PlainText);text.prepare(font=self.view.label_font);texts[mode]=text
            self.view.markers.append((entity,QColor(BASE_COLOR if entity['kind']=='Base' else TEAM_COLORS[entity['initial_team']]),entity['conditional'],texts))
        self.view.update_positions();self.view.hit_regions=[]
        current=self.event_choice.currentData();self.event_choice.blockSignals(True);self.event_choice.clear();self.event_choice.addItem('All events',None)
        for event in self.events.values():self.event_choice.addItem(event['display_name'],event['paragraph'])
        self.event_choice.setCurrentIndex(max(0,self.event_choice.findData(current)));self.event_choice.blockSignals(False)
        self.trace_history=[];self.trace_event=None;self.apply_filters();self.refresh_lists()
        selected=next((e for e in self.entities if e['index']==self.entity_id),None)
        if selected:self.select_entity(selected,switch_tab=selected['index'] not in self.view.selected_ids)
        else:self.entity_id=None;self.view.selection=None;self.entity_heading.setText('Select a unit or base');self.portrait.clear();self.image_candidates.clear();self.image_source.clear()
        self.select_editor_event(min(self.edit_event_id,len(self.document.events)-1));self.update_title();self.view.update()
        if selected_path:
            item=self.conditions.invisibleRootItem()
            for index in selected_path:
                item=item.child(index) if item and index<item.childCount() else None
            if item:self.conditions.setCurrentItem(item)
        if 0<=selected_action<self.actions.count():self.actions.setCurrentRow(selected_action)

    def history(self,redo):
        if self.text_command('redo' if redo else 'undo'):return
        self.view.cut_ids.clear()
        try:self.document.redo() if redo else self.document.undo();self.refresh_editor()
        except Exception as error:QMessageBox.warning(self,'History',str(error))

    def sync_selection_lists(self):
        for listing in (self.entity_list,self.base_list):
            with QSignalBlocker(listing):
                for row in range(listing.count()):
                    item=listing.item(row);index=item.data(Qt.ItemDataRole.UserRole)
                    item.setSelected(index in self.view.selected_ids)
                    if index==self.entity_id:
                        listing.setCurrentItem(item,QItemSelectionModel.SelectionFlag.NoUpdate)

    def place_inspector(self,index):
        pane=self.entity_panes[index]
        pane.addWidget(self.entity_scroll,1);pane.addWidget(self.appearance_button)
        self.entity_scroll.show();self.appearance_button.show()

    def clear_inspector(self):
        self.entity_id=None
        noun='base' if self.editor_tabs.currentIndex()==1 else 'unit'
        self.entity_heading.setText(f'Select a {noun} to edit')
        self.entity_scroll.widget().setEnabled(False);self.appearance_button.setEnabled(False)
        self.portrait.clear();self.image_candidates.clear();self.image_source.clear()
        self.sync_selection_lists()

    def entity_tab_changed(self,index):
        if index not in (0,1) or self.entity_loading:return
        self.place_inspector(index)
        candidates=[e for e in self.entities if e['index'] in self.view.selected_ids and (e['index']<0)==(index==1)]
        selected=next((e for e in candidates if e['index']==self.entity_id),candidates[0] if candidates else None)
        if selected:self.select_entity(selected)
        else:self.clear_inspector()

    def map_selection_changed(self,ids):
        candidates=[e for e in self.entities if e['index'] in ids]
        if len(ids)>1 and self.editor_tabs.currentIndex() in (0,1):
            candidates=[e for e in candidates if (e['index']<0)==(self.editor_tabs.currentIndex()==1)]
        selected=next((e for e in candidates if e['index']==self.entity_id),candidates[0] if candidates else None)
        if selected:self.select_entity(selected)
        else:self.clear_inspector()

    def list_selection_changed(self,listing=None):
        if self.loading or self.entity_loading:return
        listing=self.entity_list if listing is None else listing
        ids={item.data(Qt.ItemDataRole.UserRole) for item in listing.selectedItems()}
        if QApplication.keyboardModifiers() & (Qt.KeyboardModifier.ControlModifier|Qt.KeyboardModifier.ShiftModifier):
            ids|={i for i in self.view.selected_ids if (i<0)!=(listing is self.base_list)}
        self.view.set_selection(ids)

    def move_entities(self,changes):
        def move():
            for index,x,y,z in changes:self.document.move(index,x,y,z)
        self.mutate('Move selection',move)

    def text_command(self,name):
        widget=QApplication.focusWidget()
        if isinstance(widget,(QLineEdit,QPlainTextEdit,QTextBrowser)) and hasattr(widget,name):
            getattr(widget,name)();return True
        return False

    def capture_selection(self):
        records=[]
        for entity in self.entities:
            index=entity['index']
            if index not in self.view.selected_ids:continue
            record=self.document.bases[-index-1] if index<0 else self.document.units[index]
            placement=self.document.placements[2][-index-1] if index<0 else self.document.placement_for(index)
            scenario.require(placement is not None,'Selected unit has no stored placement')
            records.append(dict(index=index,record=bytes(record),placement=bytes(placement),xyz=tuple(entity['xyz'])))
        return records

    def copy_selection(self):
        if self.text_command('copy'):return
        try:records=self.capture_selection()
        except Exception as error:QMessageBox.warning(self,'Copy',str(error));return
        if records:
            EditorWindow.clipboard=dict(records=records,cut=False,document=self.document)
            self.view.cut_ids.clear();self.view.update()

    def cut_selection(self):
        if self.text_command('cut'):return
        try:records=self.capture_selection()
        except Exception as error:QMessageBox.warning(self,'Cut',str(error));return
        if records:
            EditorWindow.clipboard=dict(records=records,cut=True,document=self.document,before=self.document.serialize())
            self.view.cut_ids={r['index'] for r in records};self.view.update()
            self.entity_heading.setText(f'{len(records)} picked up - Ctrl+V to place, Esc to cancel')

    def paste_records(self,clipboard,duplicate=False):
        records=clipboard['records']
        cx=sum(r['xyz'][0] for r in records)/len(records);cz=sum(r['xyz'][2] for r in records)/len(records)
        if duplicate:
            a=self.view.world_point(QPointF());b=self.view.world_point(QPointF(24,24));dx,dz=b[0]-a[0],b[1]-a[1]
        else:
            point=self.view.last_pointer
            if point is None or not QRectF(self.view.rect()).contains(point):point=QPointF(self.view.width()/2,self.view.height()/2)
            x,z=self.view.world_point(point);dx,dz=x-cx,z-cz
        if self.view.snap_enabled:
            x,z=self.view.snap_world(cx+dx,cz+dz);dx,dz=x-cx,z-cz
        cut=clipboard.get('cut',False)
        if cut:
            scenario.require(clipboard['document'] is self.document,'Paste a cut selection into its source map; use Copy for another map')
            scenario.require(bool(self.view.cut_ids),'Cut was cancelled. Copy or cut a selection again')
            scenario.require(self.document.serialize()==clipboard['before'],'Map changed after Cut. Cancel with Esc and cut the selection again')
        new_ids=[]
        def paste():
            for item in records:
                index=item['index'];template=(item['record'],item['placement'])
                if not cut:
                    index=(self.document.append_base(template=template) if index<0 else
                           self.document.append_unit(0,struct.unpack_from('<H',item['record'],4)[0],template=template))
                x,y,z=item['xyz'];self.document.move(index,round(x+dx),y,round(z+dz));new_ids.append(index)
        if self.mutate('Move cut selection' if cut else 'Duplicate selection' if duplicate else 'Paste selection',paste):
            self.view.cut_ids.clear();self.view.set_selection(new_ids)
            if cut:EditorWindow.clipboard=None

    def paste_selection(self):
        if self.text_command('paste'):return
        if not EditorWindow.clipboard:return
        try:self.paste_records(EditorWindow.clipboard)
        except Exception as error:QMessageBox.warning(self,'Paste',str(error))

    def entity_list_selected(self,item,*_):
        if item and not self.loading:
            entity=next(e for e in self.entities if e['index']==item.data(Qt.ItemDataRole.UserRole));self.select_entity(entity)

    def select_entity(self,entity,switch_tab=True):
        self.document.finish_edit();self.entity_loading=True
        self.entity_id=entity['index'];self.view.selection=self.entity_id
        if self.entity_id not in self.view.selected_ids:self.view.set_selection({self.entity_id},False)
        self.view.update();self.describe(entity)
        base=self.entity_id<0
        if switch_tab and len(self.view.selected_ids)==1:
            with QSignalBlocker(self.editor_tabs):self.editor_tabs.setCurrentIndex(1 if base else 0)
        if self.editor_tabs.currentIndex() in (0,1):self.place_inspector(self.editor_tabs.currentIndex())
        self.entity_scroll.widget().setEnabled(True);self.appearance_button.setEnabled(True)
        self.sync_selection_lists()
        listing=self.base_list if base else self.entity_list
        if listing.currentItem():listing.scrollToItem(listing.currentItem())
        count=len(self.view.selected_ids)
        targets=self.entity_targets()
        self.entity_heading.setText((f"Editing {len(targets)} selected {'bases' if base else 'units'}\nValues shown from {entity['short_label']}" if len(targets)>1 else entity['marker_label'])
            +(f'\n{count-len(targets)} selected '+('units' if base else 'bases')+' excluded from these fields' if count>len(targets) else ''))
        for field in (self.selector_edit,self.team_edit,self.heading_edit,self.coordinates[1]):self.entity_form.setRowVisible(field,not base)
        self.entity_form.setRowVisible(self.base_type,base)
        self.selector_edit.setEnabled(not base);self.team_edit.setEnabled(not base);self.heading_edit.setEnabled(not base);self.base_type.setEnabled(base)
        self.coordinates[1].setEnabled(not base)
        for widget in (self.coordinates[0],self.coordinates[2]):widget.setRange(0 if base else -2147483648,6553500 if base else 2147483647)
        for widget,value in zip(self.coordinates,entity['xyz']):widget.setValue(round(value))
        if base:
            record=self.document.bases[-self.entity_id-1];typ=struct.unpack_from('<H',record,4)[0]
            self.base_type.setValue(typ%100);self.hidden_edit.setChecked(typ<100)
            self.entity_note.setText('Base coordinates use 100-unit cells. The game can align a base to a stage anchor at runtime.')
        else:
            record=self.document.units[self.entity_id];selector,role=struct.unpack_from('<HH',record,4)
            self.selector_edit.setCurrentIndex(self.selector_edit.findData(selector));self.team_edit.setCurrentIndex(self.team_edit.findData(initial_team(role)))
            self.hidden_edit.setChecked(not bool(record[16]));placement=self.document.placement_for(self.entity_id)
            self.heading_edit.setValue((placement[20]%8)*45 if placement else 0)
            self.entity_note.setText('Any character or Titan can use any team. Save keeps a timestamped map revision. Inject applies the saved map to the game.')
        self.populate_portraits(entity)
        self.mark_mixed_fields()
        self.entity_loading=False

    def entity_targets(self):
        if self.entity_id is None:return []
        return sorted(i for i in self.view.selected_ids if (i<0)==(self.entity_id<0))

    def entity_values(self,index):
        if index<0:
            typ=struct.unpack_from('<H',self.document.bases[-index-1],4)[0]
            return dict(base_type=typ%100,hidden=typ>=100)
        record=self.document.units[index];selector,role=struct.unpack_from('<HH',record,4)
        placement=self.document.placement_for(index)
        return dict(selector=selector,team=initial_team(role),hidden=bool(record[16]),
                    heading=(placement[20]%8)*45 if placement else 0)

    def mark_mixed_fields(self):
        values=[self.entity_values(i) for i in self.entity_targets()]
        for name,widget,label in [('selector',self.selector_edit,'Unit'),('team',self.team_edit,'Team'),
                                   ('heading',self.heading_edit,'Heading'),('base_type',self.base_type,'Base type')]:
            mixed=len({v[name] for v in values if name in v})>1
            self.entity_form.labelForField(widget).setText(label+(' (mixed)' if mixed else ''))
        mixed=len({v['hidden'] for v in values})>1
        self.hidden_edit.setText('Visible')
        self.entity_form.labelForField(self.hidden_edit).setText('Starting state'+(' (mixed)' if mixed else ''))
        positions={e['index']:e['xyz'] for e in self.entities}
        for axis,widget in enumerate(self.coordinates):
            mixed=len({positions[i][axis] for i in self.entity_targets() if i in positions})>1
            self.entity_form.labelForField(widget).setText('XYZ'[axis]+(' (mixed)' if mixed else ''))

    def position_changed(self,*_):
        if self.entity_loading or self.entity_id is None:return
        index=self.entity_id;targets=self.entity_targets();sender=self.sender()
        primary=next(e for e in self.entities if e['index']==index)
        axes=([self.coordinates.index(sender)] if sender in self.coordinates else
              [axis for axis,widget in enumerate(self.coordinates) if widget.value()!=round(primary['xyz'][axis])])
        if not axes:return
        positions={e['index']:list(e['xyz']) for e in self.entities if e['index'] in targets}
        for xyz in positions.values():
            for axis in axes:xyz[axis]=self.coordinates[axis].value()
        try:
            def move():
                for target,xyz in positions.items():self.document.move(target,*xyz)
            changed=self.document.change('Set selected positions',move,merge_key=('positions',tuple(targets),tuple(axes)))
        except Exception as error:
            QMessageBox.warning(self,'Cannot move',str(error));self.refresh_editor();return
        if not changed:return
        updated,_,self.result=read_entities(self.document.result);by_id={e['index']:e for e in updated}
        for entity in self.entities:
            if entity['index'] in targets:entity.update(by_id[entity['index']])
        self.view.update_positions();self.view.hit_regions=[];self.view.update()
        self.mark_mixed_fields();self.describe(primary);self.update_title()

    def finish_position_edit(self):
        if self.entity_loading or self.entity_id is None:return
        self.document.finish_edit()
        entity=next(e for e in self.entities if e['index']==self.entity_id)
        # Bases are serialized on 100-unit cells; show their actual saved
        # coordinates when editing ends, without interrupting typed digits.
        for widget,value in zip(self.coordinates,entity['xyz']):
            with QSignalBlocker(widget):widget.setValue(round(value))

    def apply_entity(self,*_):
        if self.entity_loading or self.entity_id is None:return
        primary=self.entity_values(self.entity_id);sender=self.sender()
        fields={self.selector_edit:'selector',self.team_edit:'team',
                self.hidden_edit:'hidden',self.heading_edit:'heading',self.base_type:'base_type'}
        field=fields.get(sender)
        try:
            def value(name):
                if name=='selector':return choice_value(self.selector_edit)
                if name=='team':return self.team_edit.currentData()
                if name=='hidden':return not self.hidden_edit.isChecked()
                return (self.heading_edit if name=='heading' else self.base_type).value()
            # Explicit controls may apply the primary's current value to a mixed
            # selection; focus-out commits only values the user actually changed.
            changes={field:value(field)} if field in primary else {k:value(k) for k,v in primary.items() if value(k)!=v}
            if not changes:return
            if 'selector' in changes:scenario.require(0<=changes['selector']<1001,'Select an ID from the binary catalog')
            if 'team' in changes:scenario.require(changes['team'] in TEAM_LABELS,'Select a starting team')
        except Exception as error:QMessageBox.warning(self,'Invalid fields',str(error));return
        targets=self.entity_targets()
        def change():
            for index in targets:
                if index<0:
                    record=self.document.bases[-index-1];typ=struct.unpack_from('<H',record,4)[0]
                    struct.pack_into('<H',record,4,changes.get('base_type',typ%100)%100+(100 if changes.get('hidden',typ>=100) else 0))
                    continue
                record=self.document.units[index];old_selector,role=struct.unpack_from('<HH',record,4)
                if 'selector' in changes and changes['selector']!=old_selector:
                    struct.pack_into('<H',record,4,changes['selector']);record[8]=11
                    if role&255<8:role=(role&0xFF00)|8;struct.pack_into('<H',record,6,role)
                if 'team' in changes and initial_team(role)!=changes['team']:
                    struct.pack_into('<H',record,6,(role&0xFF00)|(8+changes['team']))
                if 'hidden' in changes:record[16]=int(changes['hidden'])
                if 'heading' in changes:
                    placement=self.document.placement_for(index)
                    scenario.require(placement is not None,'Selected unit has no stored placement')
                    placement[20]=round(changes['heading']/45)%8
        self.mutate('Update selected '+('bases' if self.entity_id<0 else 'units'),change)

    def fresh_unit_template(self,selector):
        # Keep the game's native record structure for the chosen family. Clear
        # placement, activation and scenario flag settings rather than assigning
        # a new unit another deployment's script flags or starting location.
        resolved=self.resolver.resolve(selector)
        family=resolved['active_mapping'].get('family')
        candidates=[]
        for index,record in enumerate(self.document.units):
            placement=self.document.placement_for(index)
            if placement is None:continue
            mapping=self.resolver.resolve(struct.unpack_from('<H',record,4)[0])
            source_family=mapping['active_mapping'].get('family')
            if source_family==family:candidates.append(index)
        scenario.require(candidates,'This map has no native starting record for that unit type')
        source=min(candidates,key=lambda i:(sum(bool(x) for x in self.document.units[i][22:60]),i))
        record=bytearray(self.document.units[source]);placement=bytearray(self.document.placement_for(source))
        record[:4]=bytes(4);record[6:8]=bytes(2);struct.pack_into('<H',record,8,11)
        record[16:18]=bytes(2);record[22:60]=bytes(38)
        placement[:4]=bytes(4);placement[8:24]=bytes(16)
        return record,placement

    def add_unit(self):
        dialog=QDialog(self);dialog.setWindowTitle('Add a character / Titan');dialog.resize(620,220);layout=QVBoxLayout(dialog)
        source_id=self.entity_id if self.entity_id is not None and self.entity_id>=0 else 0
        initial_selector=struct.unpack_from('<H',self.document.units[source_id],4)[0] if self.document.units else self.catalog[0][0]
        selector=unit_choice(self.catalog,initial_selector);source=choice_widget([(i,unit_name(self.result,i)) for i in range(len(self.document.units))],source_id)
        team=UnitPicker();team.search.setPlaceholderText('Search teams...')
        for number,label in TEAM_LABELS.items():team.addItem(label,number)
        team.setCurrentIndex(team.findData(1))
        copy_settings=QCheckBox('Copy placement and starting settings from an existing unit')
        copy_settings.setObjectName('copy_unit_settings');source.setObjectName('copy_unit_source')
        note=QLabel('New placement at the center of the current map view. Visible.')
        def match_source():
            if not copy_settings.isChecked():return
            try:chosen=choice_value(selector)
            except ValueError:return
            family=self.resolver.resolve(chosen)['active_mapping'].get('family')
            candidates=[i for i,u in enumerate(self.document.units) if self.resolver.resolve(struct.unpack_from('<H',u,4)[0])['active_mapping'].get('family')==family]
            exact=[i for i in candidates if struct.unpack_from('<H',self.document.units[i],4)[0]==chosen]
            if exact or candidates:source.setCurrentIndex(source.findData((exact or candidates)[0]))
        def toggle_copy(enabled):
            source.setEnabled(enabled);source.setVisible(enabled);note.setVisible(not enabled)
            if enabled:match_source()
        selector.currentIndexChanged.connect(match_source);copy_settings.toggled.connect(toggle_copy)
        layout.addWidget(QLabel('Unit'));layout.addWidget(selector)
        layout.addWidget(QLabel('Team'));layout.addWidget(team)
        layout.addWidget(note);layout.addWidget(copy_settings);layout.addWidget(source);toggle_copy(False)
        buttons=QDialogButtonBox(QDialogButtonBox.StandardButton.Ok|QDialogButtonBox.StandardButton.Cancel);layout.addWidget(buttons)
        buttons.accepted.connect(dialog.accept);buttons.rejected.connect(dialog.reject)
        if dialog.exec()!=QDialog.DialogCode.Accepted:return
        try:
            chosen=choice_value(selector);scenario.require(0<=chosen<1001,'Select a valid unit ID')
            if copy_settings.isChecked():
                source_id=choice_value(source);scenario.require(0<=source_id<len(self.document.units),'Select a valid source unit')
                template=None
            else:template=self.fresh_unit_template(chosen)
        except Exception as error:QMessageBox.warning(self,'Add unit',str(error));return
        def add():
            self.entity_id=self.document.append_unit(source_id,chosen,template=template)
            record=self.document.units[self.entity_id];record[8]=11;record[6]=8+team.currentData()
            record[16]=0  # New units are visible, including when copying settings.
            if template is not None:
                placement=self.document.placement_for(self.entity_id)
                struct.pack_into('<HH',placement,4,8+team.currentData(),11)
                x,z=self.view.snap_world(*self.view.world_point(QPointF(self.view.width()/2,self.view.height()/2)))
                self.document.move(self.entity_id,round(x),0,round(z))
        self.mutate('Add unit',add)

    def duplicate_unit(self):
        try:
            records=self.capture_selection()
            if records:self.paste_records(dict(records=records,cut=False),duplicate=True)
        except Exception as error:QMessageBox.warning(self,'Duplicate',str(error))

    def add_base(self):
        source=-self.entity_id-1 if self.entity_id is not None and self.entity_id<0 else 0
        def add():self.entity_id=self.document.append_base(source)
        self.mutate('Add base',add)

    def add_appearance(self):
        if self.entity_id is None:return
        options=[self.event_label(i) for i in range(len(self.document.events))]
        selected,ok=QInputDialog.getItem(self,'Appearance event','Add an appearance action to:',options,self.edit_event_id,False)
        if not ok:return
        index=options.index(selected);unit=self.entity_id
        row=([0x19,unit]+[0]*14) if unit>=0 else ([0x1A,-unit-1,self.base_type.value()%100]+[0]*13)
        self.mutate('Add appearance action',lambda:self.document.events[index]['effects'].append(row))
        self.edit_event_id=index;self.select_editor_event(index)

    def event_list_selected(self,item,*_):
        if item and not self.loading:self.select_editor_event(item.data(Qt.ItemDataRole.UserRole))

    def select_editor_event(self,index):
        if not 0<=index<len(self.document.events):return
        self.edit_event_id=index;event=self.document.events[index]
        self.event_list.blockSignals(True);self.event_list.setCurrentRow(index)
        self.event_list.scrollToItem(self.event_list.item(index));self.event_list.blockSignals(False)
        self.event_heading.setText(f'Editing event {index}')
        children=self.event_children(index)
        self.event_group_links.setVisible(bool(event['header'][9]&4))
        self.event_group_links.setText(', '.join(f'<a href="event:{i}">Event {i}</a>' for i in children) or 'No events are assigned to this group.')
        parent=struct.unpack_from('<I',event['header'])[0]
        has_parent=0<parent<len(self.document.events) and parent!=index and bool(self.document.events[parent]['header'][9]&4)
        self.parent_event_button.setVisible(has_parent)
        self.parent_event_button.setText(f'Also requires event group {parent}. Open group')
        self.disabled_event.blockSignals(True);self.disabled_event.setChecked(bool(event['header'][9]&8));self.disabled_event.blockSignals(False)
        self.conditions.clear()
        self.when_explanation.setText('Every condition in a Require all group must pass. An Allow any group needs only one to pass. Select a group to add conditions inside it.'
            + (f' Event group {parent} must also pass.' if has_parent else ''))
        def add(nodes,parent,path=()):
            for i,node in enumerate(nodes):
                label=self.row_label('condition',node['words'])
                if node['words'][0] in (0xFE,0xFF) and not node['children']:
                    label='No requirements in this group. It does not block execution.' if node['words'][0]==0xFF else 'No conditions to satisfy. This group cannot pass until a condition is added.'
                item=QTreeWidgetItem([label]);item.setData(0,Qt.ItemDataRole.UserRole,path+(i,))
                item.setToolTip(0,item.text(0))
                parent.addChild(item);add(node['children'],item,path+(i,))
        add(event['conditions'],self.conditions.invisibleRootItem());self.conditions.expandAll()
        self.actions.clear()
        self.then_explanation.setText('These actions are issued in the order below when the event runs. A delay belongs to that action; it does not mean earlier actions have finished.' if event['effects'] else
            'This group has no actions. Select a linked event below to read and edit its actions.' if event['header'][9]&4 else 'Nothing happens yet. Add an action to define what this event does.')
        for number,words in enumerate(event['effects'],1):self.actions.addItem(f'{number}. {self.row_label("effect",words)}')

    def open_parent_event(self):
        parent=struct.unpack_from('<I',self.document.events[self.edit_event_id]['header'])[0]
        self.select_editor_event(parent)
        if parent<self.event_list.count():self.event_list.setCurrentRow(parent)

    def toggle_event(self,disabled):
        if self.loading:return
        def change():
            h=self.document.events[self.edit_event_id]['header'];h[9]=(h[9]|8) if disabled else (h[9]&~8)
        self.mutate('Change event enabled state',change)

    def add_event(self):
        def change():self.edit_event_id=self.document.append_event()
        self.mutate('Add event',change)

    def duplicate_event(self):
        source=self.edit_event_id
        def change():self.edit_event_id=self.document.append_event(source)
        self.mutate('Duplicate event',change)

    def condition_path(self):
        item=self.conditions.currentItem()
        return item.data(0,Qt.ItemDataRole.UserRole) if item else None

    def condition_location(self,path):
        nodes=self.document.events[self.edit_event_id]['conditions']
        for index in path[:-1]:nodes=nodes[index]['children']
        return nodes,path[-1]

    def insert_condition(self,node,path):
        roots=self.document.events[self.edit_event_id]['conditions']
        if path:
            siblings,index=self.condition_location(path);selected=siblings[index]
            if selected['words'][0] in (0xFE,0xFF):selected['children'].append(node);return
            if len(path)>1:siblings.insert(index+1,node);return
        # A condition stream has one root expression. Never append a second
        # root leaf that the native evaluator would silently ignore.
        if not roots:roots.append(new_group())
        if len(roots)==1 and roots[0]['words'][0] in (0xFE,0xFF):roots[0]['children'].append(node)
        else:
            group=new_group();group['children']=list(roots)+[node];roots[:]=[group]

    def add_condition(self,group=None):
        path=self.condition_path()
        if group in (0xFE,0xFF):node=new_group(group)
        else:
            dialog=CommandDialog(self,'condition')
            if dialog.exec()!=QDialog.DialogCode.Accepted:return
            node=dict(words=dialog.words,children=[])
        self.mutate('Add condition',lambda:self.insert_condition(node,path))

    def edit_condition(self):
        path=self.condition_path()
        if not path:return
        nodes,index=self.condition_location(path);node=nodes[index]
        if node['words'][0] in (0xFE,0xFF):
            value,ok=QInputDialog.getItem(self,'Condition group','Match:', ['ALL conditions','ANY condition'],0 if node['words'][0]==0xFF else 1,False)
            if ok:self.mutate('Change condition group',lambda:node['words'].__setitem__(0,0xFF if value.startswith('ALL') else 0xFE))
            return
        dialog=CommandDialog(self,'condition',node['words'])
        if dialog.exec()==QDialog.DialogCode.Accepted:self.mutate('Edit condition',lambda:node.__setitem__('words',dialog.words))

    def copy_condition(self):
        path=self.condition_path()
        if not path:return
        nodes,index=self.condition_location(path);node=copy.deepcopy(nodes[index])
        # Duplicate alongside the original, including groups, not inside it.
        def change():
            if len(path)>1:nodes.insert(index+1,node)
            else:
                roots=self.document.events[self.edit_event_id]['conditions'];group=new_group();group['children']=list(roots)+[node];roots[:]=[group]
        self.mutate('Duplicate condition',change)

    def remove_condition(self):
        path=self.condition_path()
        if not path:return
        def change():
            nodes,index=self.condition_location(path);nodes.pop(index)
            if not self.document.events[self.edit_event_id]['conditions']:self.document.events[self.edit_event_id]['conditions']=[new_group()]
        self.mutate('Remove condition',change)

    def move_condition(self,direction):
        path=self.condition_path()
        if not path:return
        nodes,index=self.condition_location(path);target=index+direction
        if 0<=target<len(nodes):self.mutate('Reorder condition',lambda:nodes.insert(target,nodes.pop(index)))

    def add_effect(self):
        dialog=CommandDialog(self,'effect',[0x19,max(0,self.entity_id or 0)]+[0]*14)
        if dialog.exec()==QDialog.DialogCode.Accepted:self.mutate('Add action',lambda:self.document.events[self.edit_event_id]['effects'].append(dialog.words))

    def edit_effect(self):
        index=self.actions.currentRow()
        if index<0:return
        effects=self.document.events[self.edit_event_id]['effects'];dialog=CommandDialog(self,'effect',effects[index])
        if dialog.exec()==QDialog.DialogCode.Accepted:self.mutate('Edit action',lambda:effects.__setitem__(index,dialog.words))

    def copy_effect(self):
        index=self.actions.currentRow()
        if index<0:return
        effects=self.document.events[self.edit_event_id]['effects']
        self.mutate('Duplicate action',lambda:effects.insert(index+1,list(effects[index])))

    def remove_effect(self):
        index=self.actions.currentRow()
        if index>=0:self.mutate('Remove action',lambda:self.document.events[self.edit_event_id]['effects'].pop(index))

    def move_effect(self,direction):
        index=self.actions.currentRow();effects=self.document.events[self.edit_event_id]['effects'];target=index+direction
        if index>=0 and 0<=target<len(effects):
            self.mutate('Reorder action',lambda:effects.insert(target,effects.pop(index)));self.actions.setCurrentRow(target)

    def trace_selected_event(self):
        self.trace_event=self.edit_event_id;self.render_script_trace();self.details.setCurrentWidget(self.trace_info)

    def save_current(self):
        self.document.finish_edit()
        try:path=self.document.map_store.save(self.document)
        except Exception as error:
            QMessageBox.critical(self,'Save failed',str(error));return False
        self.update_title();self.statusBar().showMessage(f'Saved {path.name} • Not injected',10000)
        return True

    def save_archive(self):
        if self.document.dirty and not self.save_current():return False
        try:
            store=self.document.map_store
            updates=store.updates(self.document.map_id,Path(self.document.saved_path))
            if not updates:
                self.statusBar().showMessage('This saved map is already injected',8000)
                QMessageBox.information(self,'Already injected','The game already contains this saved map.')
                return True
            store.apply(updates,{self.document.map_id:'Injected '+Path(self.document.saved_path).name})
        except Exception as error:
            QMessageBox.critical(self,'Injection failed',str(error));return False
        self.statusBar().showMessage('Injected saved map and verified archive contents',10000)
        QMessageBox.information(self,'Map injected',
            f'{store.data["maps"][self.document.map_id]["name"]}\n\nInjection completed and archive contents verified.')
        return True

    def revert_maps(self):
        dialog=RevertMaps(self.document.map_store,self)
        if dialog.exec()==QDialog.DialogCode.Accepted and self.document.map_id in dialog.reverted_keys:
            try:document=self.document.map_store.open(self.document.map_id)
            except Exception as error:
                QMessageBox.critical(self,'Cannot open restored map',str(error));return
            self.replace_document(document)

    def open_archives(self):
        if not self.can_close():return
        browser=MapBrowser(self.document.map_store,self)
        if browser.exec()!=QDialog.DialogCode.Accepted:
            if browser.cleared_game_root==self.document.game_root:
                try:document=self.document.map_store.open(self.document.map_id)
                except Exception as error:
                    QMessageBox.critical(self,'Cannot open restored map',str(error));return
                self.replace_document(document)
            return
        try:document=browser.open_selected()
        except Exception as error:
            QMessageBox.critical(self,'Cannot open map',str(error));return
        self.replace_document(document)

    def open_binmap(self):
        path,_=QFileDialog.getOpenFileName(self,'Open saved map',
            str(self.document.map_store.folder/'modified'),'Extracted maps (*.binmap)')
        if not path or not self.can_close():return
        try:
            # Refresh the index so revisions saved by another editor session
            # are available without restarting this window.
            store=MapStore(self.document.map_store.exe)
            document=store.open_file(path)
        except Exception as error:
            QMessageBox.critical(self,'Cannot open map',str(error));return
        self.replace_document(document)

    def open_maximized(self,screen=None):
        screen=screen or QApplication.primaryScreen()
        if screen is not None:
            self.winId()
            self.windowHandle().setScreen(screen)
            self.setGeometry(screen.availableGeometry().adjusted(20,20,-20,-20))
        self.showMaximized()

    def replace_document(self,document):
        try:replacement=EditorWindow(document)
        except Exception as error:
            QMessageBox.critical(self,'Cannot open map',str(error));return
        replacement.open_maximized(self.screen())
        self.document.saved_bytes=self.document.serialize();self.close()

    def can_close(self):
        if not self.document.dirty:return True
        answer=QMessageBox.question(self,'Unsaved scenario','Save your changes before closing this map?',
            QMessageBox.StandardButton.Save|QMessageBox.StandardButton.Discard|QMessageBox.StandardButton.Cancel)
        return self.save_current() if answer==QMessageBox.StandardButton.Save else answer==QMessageBox.StandardButton.Discard

    def closeEvent(self,event):
        if self.can_close():
            self.document.undo_stack.clear();self.document.redo_stack.clear()
            self.view.backgrounds.clear();self.view.markers.clear()
            event.accept()
        else:event.ignore()

    def populate_portraits(self,entity):
        self.image_candidates.blockSignals(True);self.image_candidates.clear()
        if entity['index']>=0:
            selector=struct.unpack_from('<H',self.document.units[entity['index']],4)[0]
            resolution=self.resolver.resolve(selector);seen=set()
            for scope in ('active_mapping',):
                mapping=resolution[scope]
                for template in mapping['template_ids']:
                    key=(mapping['family'],template)
                    if key in seen:continue
                    seen.add(key);self.image_candidates.addItem(f"{mapping['family'].capitalize()} template {template}",key)
        self.image_candidates.blockSignals(False);self.image_candidates.setVisible(self.debug_mode and self.image_candidates.count()>1);self.show_portrait()

    def set_debug_mode(self,enabled):
        if hasattr(self,'environment_debug'):self.environment_debug.setVisible(enabled)
        super().set_debug_mode(enabled)
        if hasattr(self,'image_source'):
            self.image_source.setVisible(enabled);self.entity_note.setVisible(enabled)
            self.image_candidates.setVisible(enabled and self.image_candidates.count()>1)
            self.details.setTabVisible(2,enabled);self.statusBar().setVisible(enabled)
            for button in self.findChildren(QPushButton,'debug_trace_button'):button.setVisible(enabled)
            self.show_portrait()

    def show_portrait(self,*_):
        self.portrait.clear();self.image_source.clear();key=self.image_candidates.currentData()
        if not key:
            self.portrait.setText('Base' if self.entity_id is not None and self.entity_id<0 else 'No fixed image reference');return
        try:
            image,source=entity_image(str(self.document.game_root),*key,self.portrait_style.currentIndex()==0)
            self.portrait.setPixmap(QPixmap.fromImage(image).scaled(180,106,Qt.AspectRatioMode.KeepAspectRatio,Qt.TransformationMode.SmoothTransformation))
            self.image_source.setToolTip(source if self.debug_mode else '')
            if self.debug_mode:caption=source
            elif key[0]=='titan' and '/FaceVMes/' in source:caption='Game portrait - no Titan Log entry'
            else:caption='Titan Log image' if key[0]=='titan' and self.portrait_style.currentIndex()==0 else 'Game portrait / thumbnail'
            self.image_source.setText(caption+('\nMultiple template candidates - choose above.' if self.image_candidates.count()>1 else ''))
        except Exception as error:self.portrait.setText('Image unavailable');self.image_source.setText(str(error))


def decode_ui_g1t(data):
    """Decode the first texture/mip of the verified PC UI G1T in RAM."""
    scenario.require(data[:8]==b'GT1G0600','Unsupported image container')
    total,table,count,platform=struct.unpack_from('<4I',data,8)
    scenario.require(total==len(data) and count>=1 and platform==10,'Unsupported UI image layout')
    texture=table+scenario.u32(data,table);fmt=data[texture+1];dims=data[texture+2]
    width,height=1<<(dims&15),1<<(dims>>4)
    scenario.require(width<=8192 and height<=8192,'Invalid image dimensions')
    start=texture+8+(scenario.u32(data,texture+8) if data[texture+7]&0x10 else 0)
    formats={0x59:(b'DXT1',8),0x5A:(b'DXT3',16),0x5B:(b'DXT5',16),0x5F:(b'DX10',16)}
    scenario.require(fmt in formats,f'UI texture format {fmt:#x} is not decoded')
    fourcc,blocksize=formats[fmt];size=((width+3)//4)*((height+3)//4)*blocksize
    scenario.require(start+size<=len(data),'Truncated UI image')
    header=struct.pack('<31I',124,0x81007,height,width,size,0,1,*([0]*11),32,4,int.from_bytes(fourcc,'little'),0,0,0,0,0,0x1000,0,0,0,0)
    extra=struct.pack('<5I',98,3,0,1,0) if fmt==0x5F else b''
    with Image.open(BytesIO(b'DDS '+header+extra+data[start:start+size])) as image:
        rgba=image.convert('RGBA');pixels=rgba.tobytes()
    return QImage(pixels,width,height,width*4,QImage.Format.Format_RGBA8888).copy()


@lru_cache(maxsize=2)
def portrait_tables(root):
    patch,_=scenario.name_archive_paths(Path(root))
    templates,_=scenario.read_name_resource(patch,0)
    advancement,_=scenario.read_name_resource(patch,10)
    scenario.require(len(templates)==110844 and len(advancement)==201664,
                     'Unsupported portrait-table layout')
    capture={}
    for template in range(400):
        # DataAdvancement 140B62AD0: serialized strides 112/112/112 for
        # the first 128-entry tables; +2 padding for 32x14 and 56x34.
        # Native base B5928 + EB4C + 0C = C4480; 140F8D810 reads this
        # resource index before CTitanThumbnailTexture::GetResource.
        offset=0xEB4C-128*4+32*2+56*2+template*16
        picture=struct.unpack_from('<H',advancement,offset+12)[0]
        # A zero type at +00 means no capture entry (140DE42D6 tests
        # native C4474). Its +0C still contains picture 83, a generic
        # default, NOT an image of this Titan. Keep real type-3 entries:
        # those contain the Bizarre Armored/Female/Beast Titan artwork.
        if advancement[offset] and picture<368:capture[template]=picture
    return templates,capture


@lru_cache(maxsize=16)
def entity_image(root,family,template,full=True):
    root=Path(root)
    templates,capture=portrait_tables(str(root));provenance=''
    # CTitanThumbnailTexture::GetResource = 1410C8210;
    # CCartoonTitanTexture::GetResource (full Titan Log) = 1410C0490.
    scenario.require(family in ('human','titan'),'Unsupported portrait family')
    scenario.require(0<=template<(400 if family=='titan' else 353),'Template is outside the table')
    if family=='titan' and template in capture:
        picture=capture[template]
        provenance=f'Titan template {template} → capture picture {picture}'
        if full:
            resource=10186+picture if picture<=362 else 16730+picture
            expected=f'CaptureTitan/still_titan_{picture:03d}.g1t.ZL_'
        else:
            resource=11027+picture if picture<=362 else 16708+picture
            expected=f'TitanThumbnail/still_titan_thumbnail_{picture:03d}.g1t.ZL_'
    else:
        # Human reader 140B67540 preserves serialized byte +0E. Spawn loader
        # 140A501AC -> stack B0 -> 140A50627 stores it in entity portrait +D4;
        # +06/+D5 is the voice ID and MUST NOT be used as the portrait index.
        # CFaceVMesTexture 1410C4390 uses portrait*8+expression; 1410C4360
        # resolves that index, with the expansion range beginning at 864.
        # Titan reader 140B66870 likewise preserves byte +4E. The Titan
        # spawn branch at 140A4FFF2 reads native template +4E (global
        # 38AA) into the same portrait slot. Use it when the capture entry
        # is disabled; e.g. selector 531 -> template 6 -> portrait 93 ->
        # FaceVMes/vmes_1000_00 (Colossal), not default capture picture 83.
        portrait=templates[353*36+template*104+78] if family=='titan' else templates[template*36+14]
        scenario.require(portrait<129,'This template has no fixed dialogue portrait or Titan Log entry')
        index=portrait*8;resource=9175+index if index<=863 else 16018+index
        expected='';provenance=f'{"Titan" if family=="titan" else "Character"} template {template} → portrait {portrait}'
        if family=='titan':provenance+=' (Titan Log entry disabled; generic capture default ignored)'
    name=resource_name(root,resource)
    scenario.require(name.endswith(expected) if expected else '/FaceVMes/' in name,'Executable image catalog does not match the image lookup')
    data,source=read_texture_resource(root,resource)
    decoded=decode_ui_g1t(data)
    scenario.require(decoded.width()>16 and decoded.height()>16,'The game stores a placeholder instead of an image for this entry')
    return decoded,f'{provenance}\n{Path(source["archive"]).name} → {source["entry"]}\n{name}'


def resource_name(root,resource):
    scenario.require(0<=resource<13455 or 14241<=resource<23656,'No verified image-name table for this resource')
    return archive_exe_catalog(str(Path(root)/'AOT2_EU.exe'))['names'][resource]


# --------------------------- 1.17 archive browser ---------------------------
# Directory layout follows the user's LINKDATA extractor:
# https://github.com/the-real-thunderlol/AOT2-MODDING-TOOLKIT/blob/main/custom_libraries/linkdata_extract.py
# Header <4I>; each entry <QII>; sector * header multiplier is its file offset.
# Extract map containers only. JSON records their actual archive entries; split
# scenarios are assembled as .binmap containers and split again for injection.
# EU loader proof (fingerprint EXE_SHA256):
# 14117E202..221 assigns resource 26979 to SCENARIO_DLC_011_011;
# 140CEAB0B reads the loose file's registered length for allocation;
# 140CEAB44..65 selects indexed resource reads for IDs <= 0x6969.
# 141169C00 seeks/reads the archive handle and its directory, not the loose path.
# Resource 26979 = LINKDATA_DLC entry 48. Zeroing the loose file breaks allocation;
# it does not demonstrate that its deployment bytes override the archive payload.

class LinkArchive:
    def __init__(self,path):
        self.path=Path(path).resolve()
        size=self.path.stat().st_size
        with self.path.open('rb') as source:
            header=source.read(16)
            scenario.require(len(header)==16,'Truncated LINKDATA header')
            magic,count,self.unit,_=struct.unpack('<4I',header)
            scenario.require(magic==491001 and 0<count<=100000 and self.unit==256,
                             f'{self.path.name}: unsupported LINKDATA directory')
            scenario.require(16+count*16<=size,'Truncated LINKDATA directory')
            directory=source.read(count*16)
        self.entries=[]
        for i in range(count):
            sector,stored,expanded=struct.unpack_from('<QII',directory,i*16)
            offset=sector*self.unit
            scenario.require(not stored or (offset>=16+count*16 and offset+stored<=size),
                             f'{self.path.name}: entry {i} is outside the archive')
            self.entries.append((offset,stored,expanded))

    def read(self,index):
        return scenario.read_name_resource(self.path,index)[0]

    def prefix(self,index,length=8):
        offset,stored,expanded=self.entries[index]
        if not stored:return b''
        with self.path.open('rb') as source:
            source.seek(offset)
            if not expanded:return source.read(min(length,stored))
            header=source.read(min(stored,8))
            if len(header)!=8:return b''
            total,block=struct.unpack('<II',header)
            if total!=expanded or not 0<block<=stored-8:return b''
            try:return zlib.decompressobj().decompress(source.read(min(block,4096)),length)
            except zlib.error:return b''


def read_archive_catalog_cache(exe_digest):
    path=COMMAND_CACHE_PATH.parent/'archive_catalog.json'
    try:
        stored=json.loads(path.read_text(encoding='utf-8'));catalog=stored['catalog']
        if stored['format']!=1 or stored['exe_sha256']!=exe_digest:return None
        if hashlib.sha256(command_catalog_bytes(catalog)).hexdigest()!=stored['catalog_sha256']:return None
        if set(catalog)!={'runs','names','missions','remaps'}:return None
        runs={int(k):tuple(v) for k,v in catalog['runs'].items()}
        names={int(k):v for k,v in catalog['names'].items()}
        remaps={int(k):v for k,v in catalog['remaps'].items()}
        if not all(len(rows)==count and all(isinstance(n,str) for n in rows) for count,rows in runs.items()):return None
        if not all(isinstance(v,str) for v in names.values()):return None
        if not all(type(v) is int for v in remaps.values()):return None
        if not all(set(row)=={'id','placement','behavior'} and type(row['id']) is int
                   and isinstance(row['placement'],str) and isinstance(row['behavior'],str)
                   for row in catalog['missions'].values()):return None
        return dict(runs=runs,names=names,missions=catalog['missions'],remaps=remaps)
    except (OSError,ValueError,KeyError,TypeError,AttributeError):return None


@lru_cache(maxsize=2)
def archive_exe_catalog(exe):
    raw=Path(exe).read_bytes();digest=hashlib.sha256(raw).hexdigest()
    scenario.require(digest==EXE_SHA256,'Unsupported executable build')
    cached=read_archive_catalog_cache(digest)
    if cached is not None:return cached
    catalog=extract_archive_exe_catalog(raw)
    serialized=json.loads(json.dumps(catalog))
    stored=dict(format=1,exe_sha256=digest,catalog=serialized,
                catalog_sha256=hashlib.sha256(command_catalog_bytes(serialized)).hexdigest())
    try:
        COMMAND_CACHE_PATH.parent.mkdir(parents=True,exist_ok=True)
        atomic_map_write(COMMAND_CACHE_PATH.parent/'archive_catalog.json',command_catalog_bytes(stored))
    except (OSError,ValueError):pass
    return catalog


def extract_archive_exe_catalog(raw):

    """Read filename runs, mission resource pairs and PATCH remaps from the EXE."""
    import pefile
    import capstone
    from capstone.x86_const import X86_OP_REG,X86_OP_IMM,X86_OP_MEM,X86_REG_RIP
    pe=pefile.PE(data=raw,fast_load=True);base=pe.OPTIONAL_HEADER.ImageBase
    section=next(s for s in pe.sections if s.Name.startswith(b'.rdata'))
    data=section.get_data();lo=section.VirtualAddress;hi=lo+len(data)
    runs={};run=[]
    for off in range(0,len(data)-7,8):
        ptr=struct.unpack_from('<Q',data,off)[0]-base;name=None
        if lo<=ptr<hi and data[ptr-lo:ptr-lo+5].lower()==b'file/':
            end=data.find(b'\0',ptr-lo,ptr-lo+400)
            if end>ptr-lo:
                try:name=data[ptr-lo:end].decode('ascii')
                except UnicodeDecodeError:pass
        if name:run.append(name)
        else:
            if len(run)>50:runs[len(run)]=tuple(run)
            run=[]
    scenario.require(all(n in runs for n in (13455,9415,523,2751,55)), 'Missing executable filename arrays')
    # These are the native resource ranges, including the original 523-slot D
    # namespace even when the installed D archive contains just its dummy entry.
    # DEBUG occupies resource 24179; PATCH starts at 24180 (0x5E74).
    ranges=((0,13455),(13455,786),(14241,9415),(23656,523),(24180,2751),(26931,55))
    names={start+i:name for start,count in ranges for i,name in enumerate(runs[count])}
    placement=struct.unpack('<512I',pe.get_data(0x1AF33A0,2048))
    behavior=struct.unpack('<512I',pe.get_data(0x1AF3BA0,2048))
    missions={names[b].lower():dict(id=i,placement=names[a],behavior=names[b])
              for i,(a,b) in enumerate(zip(placement,behavior))
              if a in names and b in names and '/scenario/scdata/' in names[b].lower()}
    # Interpret ONLY the verified, literal table-initialization instruction set.
    # This evaluates the same PATCH mapping used by 141166B30, not a filename
    # heuristic such as "prefer every PATCH file". No native code is executed.
    md=capstone.Cs(capstone.CS_ARCH_X86,capstone.CS_MODE_64);md.detail=True
    registers={};memory={};map_base=0x142086BC0
    def regkey(reg):
        key=md.reg_name(reg)
        return 'r'+key[1:] if key.startswith('e') else key
    def address(op,ins):
        mem=op.mem
        return (ins.address+ins.size if mem.base==X86_REG_RIP else registers.get(regkey(mem.base),0))+mem.disp
    def value(op,ins):
        if op.type==X86_OP_IMM:return op.imm
        if op.type==X86_OP_REG:return registers.get(regkey(op.reg),0)
        raise ValueError('Unexpected PATCH initializer operand')
    def assign(op,v,ins):
        if op.type==X86_OP_REG:registers[regkey(op.reg)]=v & ((1<<(op.size*8))-1)
        elif op.type==X86_OP_MEM:memory[address(op,ins)]=v
        else:raise ValueError('Unexpected PATCH initializer destination')
    for start,size in ((0x14116B0B0,0x2240),(0x14116AE20,0x290),(0x14116A7A0,0x680)):
        instructions={}
        for ins in md.disasm(pe.get_data(start-base,size),start):
            instructions[ins.address]=ins
            if ins.mnemonic=='ret':break
        pc=start;less=False
        for step in range(100000):
            ins=instructions[pc];ops=ins.operands;next_pc=pc+ins.size;op=ins.mnemonic
            if op=='ret':break
            if op=='mov':assign(ops[0],value(ops[1],ins),ins)
            elif op=='lea':assign(ops[0],address(ops[1],ins),ins)
            elif op=='inc':assign(ops[0],value(ops[0],ins)+1,ins)
            elif op=='add':assign(ops[0],value(ops[0],ins)+value(ops[1],ins),ins)
            elif op=='cmp':less=value(ops[0],ins)<value(ops[1],ins)
            elif op=='jl':
                if less:next_pc=value(ops[0],ins)
            elif op!='nop':raise ValueError('Unsupported PATCH initializer instruction: '+op)
            pc=next_pc
        else:raise ValueError('PATCH initializer exceeded its bounded instruction count')
    remaps={(a-map_base)//4:v for a,v in memory.items() if map_base<=a<map_base+0x7F42*4}
    return dict(runs=runs,names=names,missions=missions,remaps=remaps)


def pack_sections(sections):
    scenario.require(len(sections)==34 and all(sections),'Invalid scenario sections')
    header=bytearray(0x410);struct.pack_into('<II',header,0,100,34)
    payload=bytearray();cursor=0x410
    for i,part in enumerate(sections):
        struct.pack_into('<I',header,0x10+i*4,cursor)
        struct.pack_into('<I',header,0x210+i*4,len(part))
        payload.extend(part);padding=(-len(part))%16;payload.extend(bytes(padding));cursor+=len(part)+padding
    return bytes(header+payload)


def pack_text(strings):
    rows=[s.encode('utf8')+b'\0' for s in strings];cursor=4+8*len(rows);directory=[]
    for row in rows:directory.extend((cursor,len(row)));cursor+=len(row)
    return struct.pack('<I',len(rows))+struct.pack('<'+'I'*len(directory),*directory)+b''.join(rows)


def trim_text(data):
    """Standalone text resources may include zero alignment after their payload."""
    n=scenario.u32(data);scenario.require(n<=100000 and 4+8*n<=len(data),'Invalid text directory')
    end=4 if not n else sum(struct.unpack_from('<II',data,4+(n-1)*8))
    scenario.require(end<=len(data) and not any(data[end:]),'Invalid text padding')
    scenario.parse_text(data[:end],dict(id=0,file_offset=0))
    return data[:end]


def split_placements(data):
    cursor=4
    for cap in (256,64,64):
        count=scenario.u32(data,cursor)
        scenario.require(count<=cap,'Placement count exceeds native loader capacity')
        cursor+=4+64*count
        scenario.require(cursor<=len(data),'Truncated placements')
    # Some shipped non-DLC resources have three extra zero words. The native
    # importer consumes only the three groups; keep this tail on archive saves.
    scenario.require(len(data)-cursor<=64 and not any(data[cursor:]),'Unsupported placement extension')
    return data[:cursor],data[cursor:]


class ArchiveLibrary:
    def __init__(self,root,selected,use_overrides=True):
        self.root=Path(root);self.selected=[str(Path(p).resolve()) for p in selected]
        self.catalog=archive_exe_catalog(str(self.root/'AOT2_EU.exe'))
        self.archives={};self.resources={};self.use_overrides=use_overrides;self.archive_errors=[]
        # Companion placement/text resources remain in memory. Selecting one
        # archive scopes the results, while installed companions can supply data.
        paths=list((self.root/'LINKDATA').rglob('LINKDATA*.BIN'))
        paths=[p for p in paths if not any(x.lower() in ('backup','backups') for x in p.parts)]
        paths.sort(key=lambda p:('patch' in p.name.lower(),'eden' in p.name.lower(),str(p)))
        seen=set()
        for path in paths+[Path(p) for p in self.selected]:
            key=str(path.resolve())
            if key in seen:continue
            seen.add(key)
            try:archive=LinkArchive(path)
            except (OSError,ValueError) as error:
                if key in self.selected:self.archive_errors.append(f'{path.name}: {error}')
                continue
            self.archives[key]=archive
            names=self.catalog['runs'].get(len(archive.entries),())
            # DEBUG and the one-entry D dummy do not have scenario name arrays.
            if 'debug' in path.name.lower():names=()
            for index,name in enumerate(names):
                self.resources.setdefault(name.lower(),[]).append((key,index))
        self.selected=[p for p in self.selected if p in self.archives]
        self.titles={}
        try:
            data=self.read_named('File/String/ENG/DataStrScenario.bin.ZL_')
            offset=scenario.u32(data,8);count=scenario.u32(data,offset)
            for i in range(count):
                a,n=struct.unpack_from('<II',data,offset+4+i*8)
                title=data[offset+a:offset+a+n-1].decode('utf8')
                if title and not title.startswith('DUMMY'):self.titles[i]=title
        except (OSError,ValueError,struct.error):pass

    def find_named(self,name,preferred=None):
        candidates=self.resources.get(name.lower(),[])
        scenario.require(candidates,f'Missing companion resource: {name}')
        if preferred:
            hit=next((x for x in candidates if x[0]==preferred),None)
            if hit:return hit
        return candidates[-1]

    def read_named(self,name):
        path,index=self.find_named(name)
        return self.archives[path].read(index)

    def effective(self,path,index,name):
        # Match the resource's native ID and execute its verified remap.
        ids=[i for i,n in self.catalog['names'].items() if n.lower()==name.lower() and i<24179]
        if not ids:return (path,index),''
        mapped=self.catalog['remaps'].get(ids[0],ids[0])
        if 24180<=mapped<26931:
            patch_index=mapped-24180
            patches=[a for a in self.archives.values() if a.path.name.upper()=='LINKDATA_PATCH_000.BIN']
            if patches:
                target=(str(patches[-1].path),patch_index)
                if target!=(path,index):
                    label=f'PATCH entry {patch_index}'
                    return (target if self.use_overrides else (path,index)),label
        return (path,index),''

    def scan(self,progress=lambda *a:None,cancelled=lambda:False):
        rows=[];errors=list(self.archive_errors);total=sum(len(self.archives[p].entries) for p in self.selected);done=0
        for path in self.selected:
            archive=self.archives[path];names=self.catalog['runs'].get(len(archive.entries),())
            for index in range(len(archive.entries)):
                if cancelled():return rows,errors
                done+=1
                if done%64==0 or done==total:progress(done,total,archive.path.name)
                name=names[index] if index<len(names) else ''
                split=re.fullmatch(r'File/Scenario/SCDATA/(SC[A-Z]_\d+)\.BIN(?:\.ZL_)?',name,re.I)
                # Named unrelated resources never need decoding. Unknown archives
                # can still be searched for complete version-100 map containers.
                if name and not split and not re.search(r'/SCENARIO_DLC_\d+_\d+\.bin$',name,re.I):continue
                try:
                    prefix=archive.prefix(index)
                    if prefix==struct.pack('<II',100,34):
                        data=archive.read(index);_,meta=scenario.parse_sections(data)
                        section=lambda n:data[meta[n]['file_offset']:meta[n]['file_offset']+meta[n]['length']]
                        placements=scenario.parse_placements(section(5),0)
                        behavior=scenario.parse_behavior(section(6),0,placements,{})
                        title=scenario.parse_text(section(9),dict(id=9,file_offset=0))
                        match=re.search(r'SCENARIO_DLC_(\d+)_(\d+)',name,re.I)
                        mission=180+int(match[1]) if match else None
                        rows.append(dict(kind='bundle',name=title[0]['text'] if title else f'Map {index}',
                            identifier=Path(name).name or f'Entry {index}',mission=mission,
                            path=path,index=index,parts={None:(path,index)},override='',
                            entities=len(behavior['entities']),events=len(behavior['events'])))
                    elif split:
                        mission=self.catalog['missions'].get(name.lower())
                        scenario.require(mission,f'No executable mission mapping for {name}')
                        effective,override=self.effective(path,index,name)
                        position=self.find_named(mission['placement'],path)
                        if self.use_overrides:position,_=self.effective(*position,mission['placement'])
                        raw=self.archives[effective[0]].read(effective[1]);pos=self.archives[position[0]].read(position[1])
                        scenario.require(scenario.u32(raw)==4,
                            f'Legacy {scenario.u32(raw)}-table scenario; the current game loader uses four tables')
                        placements=scenario.parse_placements(split_placements(pos)[0],0)
                        behavior=scenario.parse_behavior(raw,0,placements,{})
                        title=self.titles.get(mission['id'],split[1])
                        rows.append(dict(kind='split',name=title,identifier=split[1],mission=mission['id'],
                            path=path,index=index,parts={5:position,6:effective},override=override,
                            entities=len(behavior['entities']),events=len(behavior['events'])))
                except (OSError,ValueError,struct.error,UnicodeDecodeError) as error:
                    if split or name:errors.append(f'{archive.path.name} [{index}] {name}: {error}')
        if self.use_overrides:
            unique={}
            for row in rows:
                key=(row['kind'],row['identifier'],tuple(row['parts'].values()))
                unique.setdefault(key,row)
            rows=list(unique.values())
        return rows,errors

    def open(self,row,import_path=None):
        originals={section:self.archives[path].read(index) for section,(path,index) in row['parts'].items()}
        if row['kind']=='bundle':
            data=Path(import_path).read_bytes() if import_path else originals[None]
            source=str(self.root/'FILE'/'DLC'/row['identifier'])
        else:
            scenario.require(not import_path,'Import a standalone BIN only into a bundled DLC scenario')
            # Assemble the existing inspector's container in memory. Only sections
            # 5 and 6 are written back to their real archive entries on Save.
            sections=[struct.pack('<I',0) for _ in range(34)]
            sections[4]=self.read_named('File/Data/DataCharaSet.bin')
            sections[5]=split_placements(originals[5])[0];sections[6]=originals[6]
            sections[9]=pack_text([row['name']])
            for part,suffix in ((18,'TEXT_MESSAGE'),(27,'VOICE_MESSAGE')):
                name=f'File/Scenario/SCDATA/ENG/{row["identifier"]}_{suffix}.bin'
                if name.lower() in self.resources:sections[part]=trim_text(self.read_named(name))
            data=pack_sections(sections);source=str(self.root/(row['identifier']+'.bin'))
        doc=ScenarioDocument(data,source,self.root,mission_id=row['mission'])
        doc.archive_binding=dict(kind=row['kind'],parts=dict(row['parts']),originals=originals,
                                 name=row['name'],identifier=row['identifier'],source=row['path'])
        doc.saved_path=f'{Path(row["path"]).name} [{row["index"]}] - {row["identifier"]}'
        doc.update_archive_context()
        if import_path:doc.saved_bytes=originals[None]
        return doc


def write_archive_updates(updates,commit=None):
    """Append payloads first, then switch only their TOC entries; roll back errors.

    Original payloads remain untouched. Growth never overwrites the next entry.
    The current entry is compared with the bytes opened, rejecting stale edits.
    Invoked only by Inject or Revert. Save never writes to the game archives.
    """
    import os
    from contextlib import ExitStack
    grouped={};loose=[u for u in updates if u['index'] is None]
    for update in updates:
        if update['index'] is not None:grouped.setdefault(update['path'],[]).append(update)
    checkpoints={}
    with ExitStack() as stack:
        files={path:stack.enter_context(open(path,'r+b')) for path in grouped}
        for path,changes in grouped.items():
            archive=LinkArchive(path);source=files[path];source.seek(0,2);end=source.tell();entries={}
            for change in changes:
                index=change['index']
                scenario.require(archive.read(index)==change['before'],
                    f'{Path(path).name} entry {index} changed while preparing injection. No changes were written.')
                source.seek(16+index*16);entries[index]=source.read(16)
            checkpoints[path]=(end,entries)
        for change in loose:
            path=Path(change['path'])
            scenario.require(path.exists()==change['existed'] and (path.read_bytes() if path.exists() else b'')==change['before'],
                             'The loose DLC file changed since the save was prepared')
        loose_written=[]
        try:
            replacements=[]
            for path,changes in grouped.items():
                source=files[path];archive=LinkArchive(path)
                last_file_end=max(offset+size for offset,size,_ in archive.entries)
                # The extractor uses byte_offset = TOC_sector * 256. New data
                # starts at ceil((last offset + stored size) / 256) * 256.
                # Preserve any unreferenced EOF data left by earlier injections.
                source.seek(0,2);end=max(last_file_end,source.tell())
                source.seek(end)
                for change in changes:
                    padding=(-source.tell())%256;source.write(bytes(padding));offset=source.tell()
                    source.write(change['after'])
                    replacements.append((path,change['index'],struct.pack('<QII',offset//256,len(change['after']),0)))
                source.flush();os.fsync(source.fileno())
            for path,index,entry in replacements:
                source=files[path];source.seek(16+index*16);source.write(entry)
            for source in files.values():source.flush();os.fsync(source.fileno())
            for change in (u for u in updates if u['index'] is not None):
                scenario.require(LinkArchive(change['path']).read(change['index'])==change['after'],
                                 'Archive read-back verification failed')
            for change in loose:
                output=QSaveFile(change['path'])
                scenario.require(output.open(QIODevice.OpenModeFlag.WriteOnly),output.errorString())
                if output.write(change['after'])!=len(change['after']):
                    output.cancelWriting();raise ValueError('Incomplete loose DLC write')
                scenario.require(output.commit(),output.errorString());loose_written.append(change)
                scenario.require(Path(change['path']).read_bytes()==change['after'],'Loose DLC verification failed')
            if commit:commit()
        except Exception:
            for change in loose_written:
                if change['existed']:Path(change['path']).write_bytes(change['before'])
                else:Path(change['path']).unlink()
            for path,(end,entries) in checkpoints.items():
                source=files[path]
                for index,entry in entries.items():source.seek(16+index*16);source.write(entry)
                source.truncate(end);source.flush();os.fsync(source.fileno())
            raise

def atomic_map_write(path,data):
    output=QSaveFile(str(path))
    scenario.require(output.open(QIODevice.OpenModeFlag.WriteOnly),output.errorString())
    if output.write(data)!=len(data):
        output.cancelWriting();raise ValueError('Incomplete map/index write')
    scenario.require(output.commit(),output.errorString())


def map_digest(data):return hashlib.sha256(data).hexdigest()


def read_original_archive_entry(source,part):
    """Validate the preserved original payload without changing the live TOC."""
    offset=part['original_offset'];stored=part['original_stored_size'];expanded=part['original_expanded_size']
    scenario.require(offset%256==0 and 0<stored<=64*1024*1024 and 0<=expanded<=64*1024*1024,
                     'Invalid original archive entry metadata')
    source.seek(offset);raw=source.read(stored)
    scenario.require(len(raw)==stored,'Original archive payload is missing')
    if expanded:
        scenario.require(scenario.u32(raw)==expanded,'Original compressed size mismatch')
        data=bytearray();cursor=4;terminated=False
        while cursor<len(raw):
            size=scenario.u32(raw,cursor);cursor+=4
            if not size:
                scenario.require(not any(raw[cursor:]),'Invalid original compression padding');terminated=True;break
            scenario.require(cursor+size<=len(raw),'Truncated original compressed block')
            decoder=zlib.decompressobj();data.extend(decoder.decompress(raw[cursor:cursor+size],expanded-len(data)+1))
            scenario.require(decoder.eof and not decoder.unused_data and not decoder.unconsumed_tail and len(data)<=expanded,
                             'Invalid original compressed block')
            cursor+=size
        scenario.require(terminated and len(data)==expanded,'Incomplete original compressed entry')
        raw=bytes(data)
    scenario.require(map_digest(raw)==part['original_sha256'],'Original archive payload no longer matches its extraction')
    return raw


def restore_archive_directories(plans,loose,commit):
    """Restore original TOC pointers and trim only unreferenced archive tails.

    Keep rollback copies of removed tails until read-back and index commit pass.
    Every entry outside the map library retains its existing TOC record.
    """
    import tempfile
    from contextlib import ExitStack
    with ExitStack() as stack:
        handles={p['path']:stack.enter_context(open(p['path'],'r+b')) for p in plans}
        backups={}
        # Preflight every archive and loose file before changing any of them.
        for plan in plans:
            source=handles[plan['path']];source.seek(0,2)
            scenario.require(source.tell()==plan['old_size'],'Archive size changed during cleanup preparation')
            source.seek(16)
            scenario.require(source.read(len(plan['before']))==plan['before'],'Archive TOC changed during cleanup preparation')
            tail=stack.enter_context(tempfile.SpooledTemporaryFile(max_size=8*1024*1024))
            source.seek(plan['new_size']);remaining=plan['old_size']-plan['new_size']
            while remaining:
                block=source.read(min(1024*1024,remaining));scenario.require(block,'Truncated archive rollback data')
                tail.write(block);remaining-=len(block)
            backups[plan['path']]=tail
        for item in loose:
            path=Path(item['path'])
            scenario.require(path.exists()==item['existed'] and (path.read_bytes() if path.exists() else b'')==item['before'],
                             'A loose DLC file changed during cleanup preparation')
        written=[]
        try:
            for plan in plans:
                source=handles[plan['path']];source.seek(16);source.write(plan['after'])
                source.flush();os.fsync(source.fileno())
                # All remaining TOC references end at/before new_size.
                source.truncate(plan['new_size']);source.flush();os.fsync(source.fileno())
            for plan in plans:
                source=handles[plan['path']];source.seek(16)
                scenario.require(source.read(len(plan['after']))==plan['after'],'Restored TOC verification failed')
                archive=LinkArchive(plan['path'])
                for part in plan['parts']:
                    scenario.require(map_digest(archive.read(part['entry']))==part['original_sha256'],
                                     'Restored map verification failed')
            for item in loose:
                atomic_map_write(item['path'],item['after']);written.append(item)
                scenario.require(Path(item['path']).read_bytes()==item['after'],'Restored loose DLC verification failed')
            commit()
        except Exception:
            for plan in plans:
                source=handles[plan['path']];tail=backups[plan['path']];tail.seek(0);source.seek(plan['new_size'])
                while True:
                    block=tail.read(1024*1024)
                    if not block:break
                    source.write(block)
                source.truncate(plan['old_size']);source.seek(16);source.write(plan['before'])
                source.flush();os.fsync(source.fileno())
            for item in written:
                if item['existed']:atomic_map_write(item['path'],item['before'])
                else:Path(item['path']).unlink()
            raise


GAME_PATH_INI = Path(__file__).resolve().parent/'map-extract'/'mem'/'path.ini'


def remember_game_exe(exe):
    # Keep this beside the editor so it remains readable if the game is moved
    # or its drive disappears. Map snapshots stay in the game's maps-extract.
    import configparser
    from io import StringIO
    settings=configparser.ConfigParser(interpolation=None)
    settings['game']={'exe':str(Path(exe).resolve()) if exe else '""'}
    output=StringIO();settings.write(output);data=output.getvalue().encode('utf-8')
    if GAME_PATH_INI.is_file() and GAME_PATH_INI.read_bytes()==data:return
    GAME_PATH_INI.parent.mkdir(parents=True,exist_ok=True)
    atomic_map_write(GAME_PATH_INI,data)


def remembered_game_exe():
    import configparser
    if not GAME_PATH_INI.is_file():return ''
    settings=configparser.ConfigParser(interpolation=None)
    try:
        settings.read_string(GAME_PATH_INI.read_text(encoding='utf-8'))
        exe=settings.get('game','exe',fallback='').strip().strip('"')
    except (configparser.Error,UnicodeError):
        remember_game_exe('');return ''
    if not exe:return ''
    if not Path(exe).is_file():
        remember_game_exe('');return ''
    return exe


class MapStore:
    """First-run snapshots, timestamped revisions, and exact archive bindings.

    .binmap is the editable scenario container, not a renamed archive entry for
    split non-DLC maps. Its JSON binding preserves the separate placement/event
    destinations and any placement padding. Original snapshots never change.
    """
    def __init__(self,exe):
        self.exe=Path(exe).resolve();self.root=self.exe.parent
        scenario.require(self.exe.is_file() and self.exe.name.lower()=='aot2_eu.exe',
                         'Select the installed AOT2_EU.exe')
        scenario.require(map_digest(self.exe.read_bytes())==EXE_SHA256,'Unsupported game executable build')
        self.folder=self.root/'maps-extract';self.index=self.folder/'maps.json'
        if self.index.exists():
            self.data=json.loads(self.index.read_text(encoding='utf-8'))
            scenario.require(self.data.get('format')==1 and self.data.get('exe_sha256')==EXE_SHA256,
                             'This map index belongs to a different format or game build')
        else:
            self.data=dict(format=1,exe_sha256=EXE_SHA256,game_exe=str(self.exe),complete=False,
                           maps={},scan_errors=[],archive_state={})
    def write_index(self,data=None):
        atomic_map_write(self.index,(json.dumps(self.data if data is None else data,ensure_ascii=False,indent=2)+'\n').encode('utf-8'))

    def environment_original(self):
        if hasattr(self,'_environment_original'):return self._environment_original
        part=self.data.get('environment_resource')
        if part:
            path=self.archive_path(part['archive'])
            with path.open('rb') as source:raw=read_original_archive_entry(source,part)
        else:
            path=self.root/'LINKDATA/PATCH/LINKDATA_PATCH_000.BIN';archive=LinkArchive(path)
            raw=archive.read(4);offset,stored,expanded=archive.entries[4]
            part=dict(section='environment',archive=path.relative_to(self.root).as_posix(),entry=4,
                      original_offset=offset,original_stored_size=stored,original_expanded_size=expanded,
                      original_sha256=map_digest(raw))
        scenario.require(len(raw)==66164,'Unsupported DataScenarioBase environment layout')
        self._environment_part=part;self._environment_original=raw
        return raw

    def local(self,relative):
        path=(self.folder/relative).resolve()
        scenario.require(path.is_relative_to(self.folder.resolve()) and path.suffix.lower()=='.binmap',
                         'Map must be a registered .binmap inside maps-extract')
        scenario.require(path.parent in ((self.folder/'original').resolve(),(self.folder/'modified').resolve()),
                         'Map must be in original or modified')
        return path

    def archive_path(self,relative):
        path=(self.root/relative).resolve()
        scenario.require(path.is_relative_to((self.root/'LINKDATA').resolve()) and path.name.upper().startswith('LINKDATA'),
                         'Invalid archive path in the map index')
        return path

    @staticmethod
    def state_key(part):return part['archive'].casefold()+'|'+str(part['entry'])

    def extract(self,progress=lambda *a:None,cancelled=lambda:False):
        if self.data['complete']:return
        paths=[str(p) for p in (self.root/'LINKDATA').rglob('LINKDATA*.BIN')
               if not any(x.lower() in ('backup','backups') for x in p.parts)]
        scenario.require(paths,'No LINKDATA archives found beside the selected executable')
        library=ArchiveLibrary(self.root,paths,True)
        rows,errors=library.scan(progress,cancelled)
        if cancelled():return
        (self.folder/'original').mkdir(parents=True,exist_ok=True)
        (self.folder/'modified').mkdir(exist_ok=True)
        self.write_index()
        for n,row in enumerate(rows):
            if cancelled():return
            progress(n,len(rows),'Extracting '+row['name'])
            identity=json.dumps([row['kind'],row['identifier'],
                [(k,str(Path(p).relative_to(self.root)),i) for k,(p,i) in row['parts'].items()]])
            key=map_digest(identity.encode())[:16]
            if key in self.data['maps']:continue
            document=library.open(row);payload=document.serialize()
            safe=re.sub(r'[<>:"/\\|?*\x00-\x1f]','_',row['name']).strip(' .')[:85] or 'Map'
            identifier=re.sub(r'[^a-zA-Z0-9_-]','_',Path(row['identifier']).stem)
            stem=f'{safe} -- {identifier} -- {key[:8]}'
            relative='original/'+stem+'.binmap';path=self.local(relative)
            if path.exists():
                scenario.require(path.read_bytes()==payload,'An unindexed original exists with different contents: '+str(path))
            else:atomic_map_write(path,payload)
            parts=[]
            for section,(archive,index) in row['parts'].items():
                source=library.archives[archive];offset,stored,expanded=source.entries[index]
                before=document.archive_binding['originals'][section]
                part=dict(section=section,archive=Path(archive).relative_to(self.root).as_posix(),entry=index,
                          original_offset=offset,original_stored_size=stored,original_expanded_size=expanded,
                          original_sha256=map_digest(before),placement_tail=split_placements(before)[1].hex() if section==5 else '')
                parts.append(part)
                self.data['archive_state'].setdefault(self.state_key(part),dict(sha256=map_digest(before),offset=offset,
                    stored_size=stored,expanded_size=expanded))
            self.data['maps'][key]=dict(name=row['name'],identifier=row['identifier'],kind=row['kind'],mission=row['mission'],
                entities=row['entities'],events=row['events'],override=row['override'],parts=parts,stem=stem,
                original=dict(file=relative,sha256=map_digest(payload)),versions=[],last_action='Extracted')
            self.write_index()
        self.data['scan_errors']=errors;self.data['complete']=True;self.write_index()
        progress(len(rows),len(rows),'Extraction complete')

    def revisions(self,key):
        row=self.data['maps'][key]
        # Modified revisions are opt-in, never silently preferred over Original.
        return [row['original']]+list(reversed(row['versions']))

    def read_revision(self,key,path):
        path=Path(path).resolve()
        version=next((v for v in self.revisions(key) if self.local(v['file'])==path),None)
        scenario.require(version is not None,'Select an extracted .binmap or a saved revision from this map library')
        data=path.read_bytes()
        scenario.require(map_digest(data)==version['sha256'],'The .binmap contents differ from its saved index: '+path.name)
        return data

    def open(self,key,path=None):
        row=self.data['maps'][key]
        path=self.local(row['original']['file']) if path is None else Path(path)
        data=self.read_revision(key,path)
        source=self.root/'FILE'/'DLC'/row['identifier'] if row['kind']=='bundle' else self.root/(row['identifier']+'.bin')
        document=ScenarioDocument(data,str(source),self.root,mission_id=row['mission'])
        document.archive_binding=dict(kind=row['kind'],name=row['name'],identifier=row['identifier'],
            parts={p['section']:(str(self.archive_path(p['archive'])),p['entry']) for p in row['parts']})
        document.map_store=self;document.map_id=key;document.saved_path=str(path)
        document.update_archive_context()
        return document

    def open_file(self,path):
        path=Path(path).resolve()
        scenario.require(path.suffix.lower()=='.binmap','Select a .binmap file')
        for key in self.data['maps']:
            if any(self.local(version['file'])==path for version in self.revisions(key)):
                return self.open(key,path)
        raise ValueError('This file is not registered in this game\'s maps.json. Select a map from maps-extract/original or maps-extract/modified.')

    def save(self,document):
        key=document.map_id;row=self.data['maps'][key];payload=document.serialize()
        scenario.analyze(payload,document.source,game_root=self.root)
        values=environment_values(document);mission=row['mission'];baseline=self.environment_original()
        stamp=datetime.now(timezone.utc).strftime('%Y-%m-%d_%H-%M-%S_%fZ')
        relative='modified/'+row['stem']+' -- '+stamp+'.binmap';path=self.local(relative)
        scenario.require(not path.exists(),'This timestamp already exists; save again')
        atomic_map_write(path,payload)
        updated=copy.deepcopy(self.data)
        if bytes(values)!=baseline[mission*88+4:mission*88+8] and 'environment_resource' not in updated:
            part=copy.deepcopy(self._environment_part);updated['environment_resource']=part
            updated['archive_state'][self.state_key(part)]=dict(sha256=part['original_sha256'],offset=part['original_offset'],
                stored_size=part['original_stored_size'],expanded_size=part['original_expanded_size'])
        updated['maps'][key]['versions'].append(dict(file=relative,sha256=map_digest(payload),saved_utc=stamp,environment=list(values)))
        self.write_index(updated);self.data=updated
        document.saved_bytes=payload;document.saved_path=str(path)
        return path

    def updates(self,key,path):
        row=self.data['maps'][key];data=self.read_revision(key,path)
        # Validate the actual saved revision, not just the unsaved editor state.
        source=str(self.root/row['identifier'])
        scenario.analyze(data,source,game_root=self.root)
        _,sections=scenario.parse_sections(data);updates=[]
        for part in row['parts']:
            section=part['section'];meta=sections[section] if section is not None else None
            after=data if section is None else data[meta['file_offset']:meta['file_offset']+meta['length']]
            if section==5:after+=bytes.fromhex(part['placement_tail'])
            archive=self.archive_path(part['archive']);before=LinkArchive(archive).read(part['entry'])
            expected=self.data['archive_state'][self.state_key(part)]['sha256']
            scenario.require(map_digest(before)==expected or before==after,
                f'{archive.name} entry {part["entry"]} changed outside this library. Injection stopped to preserve that edit.')
            if before!=after:updates.append(dict(path=str(archive),index=part['entry'],before=before,after=after))
        if 'environment_resource' in self.data:
            part=self.data['environment_resource'];mission=row['mission'];start=mission*88+4
            original=self.environment_original()
            version=next(v for v in self.revisions(key) if self.local(v['file'])==Path(path).resolve())
            values=bytes(version.get('environment',original[start:start+4]))
            scenario.require(len(values)==4 and values[0]<10 and values[1]<=24 and all(v<=2 for v in values[2:]),
                             'Invalid saved environment values')
            if 'environment' in version:
                native=sections[0];offset=mission*80+4
                stored=(data[native['file_offset']+offset:native['file_offset']+offset+4]
                        if native['length']>=offset+4 else original[start:start+4])
                scenario.require(values==stored,'Saved environment index disagrees with the .binmap')
            # One mission owns exactly these four bytes. Never inject the whole
            # stale table stored by another map or reset another mission's edit.
            archive=self.archive_path(part['archive']);before=LinkArchive(archive).read(part['entry'])
            expected=self.data['archive_state'][self.state_key(part)]['sha256']
            scenario.require(map_digest(before)==expected,'The mission settings table changed outside this library')
            after=bytearray(before);after[start:start+4]=values
            if after!=before:updates.append(dict(path=str(archive),index=part['entry'],before=before,after=bytes(after),
                                                environment_rows={start:values.hex()}))
        if row['kind']=='bundle' and any(Path(p['archive']).name.upper()=='LINKDATA_DLC.BIN' for p in row['parts']):
            scenario.require(Path(row['identifier']).name==row['identifier'],'Invalid DLC filename')
            loose=self.root/'FILE'/'DLC'/row['identifier']
            scenario.require(loose.parent.is_dir(),'The installed DLC directory is missing')
            before=loose.read_bytes() if loose.exists() else b''
            # The executable allocates by loose-file length, then reads LINKDATA.
            if before!=data:updates.append(dict(path=str(loose),index=None,before=before,after=data,existed=loose.exists()))
        return updates

    def apply(self,updates,actions=None):
        unique={}
        for update in updates:
            key=(update['path'],update['index'])
            if key in unique and 'environment_rows' in update and 'environment_rows' in unique[key]:
                previous=unique[key]
                scenario.require(previous['before']==update['before'],'Mission settings changed while preparing updates')
                rows=previous['environment_rows'];merged=bytearray(previous['after'])
                for offset,value in update['environment_rows'].items():
                    scenario.require(offset not in rows or rows[offset]==value,'Maps disagree on shared environment settings')
                    rows[offset]=value;merged[offset:offset+4]=bytes.fromhex(value)
                previous['after']=bytes(merged);continue
            scenario.require(key not in unique or unique[key]['after']==update['after'],
                             'The selected maps disagree on a shared archive entry')
            unique[key]=update
        updates=list(unique.values());updated=copy.deepcopy(self.data)
        def commit():
            for update in updates:
                if update['index'] is None:continue
                relative=Path(update['path']).relative_to(self.root).as_posix()
                part=dict(archive=relative,entry=update['index'])
                offset,stored,expanded=LinkArchive(update['path']).entries[update['index']]
                updated['archive_state'][self.state_key(part)]=dict(sha256=map_digest(update['after']),offset=offset,
                    stored_size=stored,expanded_size=expanded)
            for key,action in (actions or {}).items():
                updated['maps'][key]['last_action']=action
            self.write_index(updated)
        write_archive_updates(updates,commit)
        self.data=updated

    def revert(self,keys):
        updates=[]
        for key in keys:
            row=self.data['maps'][key];path=self.local(row['original']['file'])
            data=self.read_revision(key,path);_,sections=scenario.parse_sections(data)
            # Verify originals still reproduce the exact extracted entry bytes.
            for part in row['parts']:
                n=part['section'];m=sections[n] if n is not None else None
                raw=data if n is None else data[m['file_offset']:m['file_offset']+m['length']]
                if n==5:raw+=bytes.fromhex(part['placement_tail'])
                scenario.require(map_digest(raw)==part['original_sha256'],'Original map no longer matches its source entry')
            updates.extend(self.updates(key,path))
        self.apply(updates,{key:'Reverted to original' for key in keys})

    def plan_clear_injections(self):
        grouped={};loose=[];updated=copy.deepcopy(self.data)
        if 'environment_resource' in self.data:
            part=self.data['environment_resource'];grouped.setdefault(part['archive'],{})[part['entry']]=part
        for key,row in self.data['maps'].items():
            for part in row['parts']:
                entries=grouped.setdefault(part['archive'],{})
                previous=entries.get(part['entry'])
                scenario.require(previous is None or previous==part,'Maps disagree on an original archive entry')
                entries[part['entry']]=part
        plans=[];changed=set()
        for relative,parts in grouped.items():
            path=self.archive_path(relative);archive=LinkArchive(path)
            with path.open('rb') as source:
                source.seek(16);before=source.read(16*len(archive.entries));after=bytearray(before)
                source.seek(0,2);old_size=source.tell()
                for index,part in parts.items():
                    original=read_original_archive_entry(source,part)
                    current=archive.read(index);expected=self.data['archive_state'][self.state_key(part)]['sha256']
                    scenario.require(map_digest(current)==expected or current==original,
                                     f'{path.name} entry {index} was changed outside this library; cleanup stopped')
                    entry=struct.pack('<QII',part['original_offset']//archive.unit,
                                      part['original_stored_size'],part['original_expanded_size'])
                    if before[index*16:index*16+16]!=entry:changed.add((relative,index))
                    after[index*16:index*16+16]=entry
                    updated['archive_state'][self.state_key(part)]=dict(sha256=part['original_sha256'],
                        offset=part['original_offset'],stored_size=part['original_stored_size'],expanded_size=part['original_expanded_size'])
                end=16+len(after)
                for i in range(len(archive.entries)):
                    sector,stored,_=struct.unpack_from('<QII',after,i*16)
                    if stored:end=max(end,sector*archive.unit+stored)
                scenario.require(end<=old_size,'Restored TOC points outside the archive')
                new_size=min(old_size,((end+archive.unit-1)//archive.unit)*archive.unit)
                if after!=before or new_size<old_size:
                    plans.append(dict(path=str(path),before=before,after=bytes(after),old_size=old_size,
                                      new_size=new_size,parts=list(parts.values())))
        for key,row in updated['maps'].items():
            affected=any((p['archive'],p['entry']) in changed for p in row['parts'])
            if affected or row.get('last_action','Extracted')!='Extracted':row['last_action']='Cleared injections'
            if row['kind']!='bundle' or not any(Path(p['archive']).name.upper()=='LINKDATA_DLC.BIN' for p in row['parts']):continue
            scenario.require(Path(row['identifier']).name==row['identifier'],'Invalid DLC filename')
            original=self.read_revision(key,self.local(row['original']['file']))
            scenario.require(map_digest(original)==row['parts'][0]['original_sha256'],'Original DLC snapshot mismatch')
            path=self.root/'FILE'/'DLC'/row['identifier'];existed=path.exists();before=path.read_bytes() if existed else b''
            scenario.require(path.parent.is_dir(),'Installed DLC folder is missing')
            if before!=original:loose.append(dict(path=str(path),before=before,after=original,existed=existed))
        return plans,loose,updated

    def clear_injections(self):
        plans,loose,updated=self.plan_clear_injections()
        restore_archive_directories(plans,loose,lambda:self.write_index(updated))
        self.data=updated
        return sum(p['old_size']-p['new_size'] for p in plans)


class MapExtraction(QThread):
    progress=Signal(int,int,str)
    completed=Signal(object)
    failed=Signal(str)
    def __init__(self,exe,parent):super().__init__(parent);self.exe=exe
    def run(self):
        try:
            store=MapStore(self.exe)
            remember_game_exe(store.exe)
            store.extract(self.progress.emit,self.isInterruptionRequested)
            self.completed.emit(store)
        except Exception as error:self.failed.emit(str(error))


def map_selection_order(item):
    row=item[1]
    # Native mission IDs order the non-DLC scenario families; DLC follows.
    return (row['kind']=='bundle',row['mission'] if row['mission'] is not None else sys.maxsize,row['identifier'])


class RevertMaps(QDialog):
    def __init__(self,store,parent=None):
        super().__init__(parent);self.store=store;self.reverted_keys=[]
        self.setWindowTitle('Revert maps');self.resize(720,580)
        layout=QVBoxLayout(self)
        label=QLabel('Select maps to restore to their first extraction. Saved modified versions remain available.')
        label.setWordWrap(True);layout.addWidget(label)
        search=QLineEdit();search.setPlaceholderText('Search maps…');layout.addWidget(search)
        self.list=QListWidget();layout.addWidget(self.list)
        for key,row in sorted(store.data['maps'].items(),key=map_selection_order):
            item=QListWidgetItem(row['name']+' - '+Path(row['identifier']).stem,self.list)
            item.setData(Qt.ItemDataRole.UserRole,key);item.setCheckState(Qt.CheckState.Unchecked)
        search.textChanged.connect(lambda text:[self.list.item(i).setHidden(text.casefold() not in self.list.item(i).text().casefold())
                                              for i in range(self.list.count())])
        buttons=QHBoxLayout();layout.addLayout(buttons)
        select=QPushButton('Select visible');select.clicked.connect(lambda:[self.list.item(i).setCheckState(Qt.CheckState.Checked)
            for i in range(self.list.count()) if not self.list.item(i).isHidden()]);buttons.addWidget(select)
        clear=QPushButton('Clear selection');clear.clicked.connect(lambda:[self.list.item(i).setCheckState(Qt.CheckState.Unchecked)
            for i in range(self.list.count())]);buttons.addWidget(clear);buttons.addStretch()
        self.submit=QPushButton('Revert selected');self.submit.clicked.connect(self.revert);buttons.addWidget(self.submit)
        close=QPushButton('Cancel');close.clicked.connect(self.reject);buttons.addWidget(close)

    def revert(self):
        keys=[self.list.item(i).data(Qt.ItemDataRole.UserRole) for i in range(self.list.count())
              if self.list.item(i).checkState()==Qt.CheckState.Checked]
        if not keys:return
        try:self.store.revert(keys)
        except Exception as error:QMessageBox.critical(self,'Revert failed',str(error));return
        self.reverted_keys=list(keys)
        QMessageBox.information(self,'Maps reverted',f'Restored {len(keys)} selected maps and verified their archive entries.')
        self.accept()


class MapSearchValidator(QValidator):
    def __init__(self,browser):
        super().__init__(browser.search);self.browser=browser

    def validate(self,text,position):
        browser=self.browser
        previous=getattr(browser,'filtered_query','')
        counts=getattr(browser,'match_counts',[0,0])
        if (browser.store and not browser.busy and len(text)>len(previous)
                and counts[browser.tabs.currentIndex()]==0):
            # Stop extending a failed search. Deleting/clearing stays available,
            # and replacing it with a matching query is allowed (including paste).
            query=text.strip().casefold();tree=browser.trees[browser.tabs.currentIndex()]
            matches=any(query in tree.topLevelItem(i).data(0,Qt.ItemDataRole.UserRole+2)
                        for i in range(tree.topLevelItemCount()))
            if not matches:return QValidator.State.Invalid,text,position
        return QValidator.State.Acceptable,text,position


class CenteredMapSearch(QLineEdit):
    def paintEvent(self,event):
        super().paintEvent(event)
        # Qt hides centered placeholders on focus. Keep the search instruction
        # visible even though this field is ready for typing at startup.
        if self.hasFocus() and not self.text():
            painter=QPainter(self);painter.setFont(self.font())
            painter.setPen(self.palette().color(QPalette.ColorRole.PlaceholderText))
            painter.drawText(self.contentsRect().adjusted(18,0,-18,0),Qt.AlignmentFlag.AlignCenter,self.placeholderText())
            painter.end()


class MapBrowser(QDialog):
    def __init__(self,store=None,parent=None,exe=None):
        super().__init__(parent)
        self.store=store;self.worker=None;self.busy=False;self.close_pending=False
        self.key=None;self.path=None;self.selected_document=None;self.load_error='';self.cleared_game_root=None
        self.setWindowTitle('AoT2 1.17 - Maps');self.resize(1250,760)
        self.setObjectName('map_picker')
        self.setStyleSheet('''
            QDialog#map_picker { background: #090a0c; }
            QPushButton#game_exe_button { border: 2px solid #ffff00; padding: 8px 14px; }
            QPushButton#game_exe_button[exeFound="true"] { border-color: #008000; }
            QLineEdit#map_search { padding: 10px 16px; border-radius: 7px; font-size: 14px; }
            QLabel#exe_path { color: #aeb6c4; padding: 4px 0; }
            QTabBar::tab { min-width: 130px; padding: 10px 20px; }
            QToolButton#map_warning { border: 0; color: #ffcc33; font-size: 20px; padding: 2px; }
            QToolButton#map_warning:hover { background: #292d36; border-radius: 4px; }
        ''')
        layout=QVBoxLayout(self);layout.setContentsMargins(18,16,18,14);layout.setSpacing(12)
        top=QHBoxLayout();top.setSpacing(10);layout.addLayout(top)
        self.choose_button=QPushButton('Select Game EXE');self.choose_button.setObjectName('game_exe_button')
        self.choose_button.setProperty('exeFound',False);self.choose_button.clicked.connect(self.choose);top.addWidget(self.choose_button)
        self.location=QLabel('No game EXE selected');self.location.setObjectName('exe_path')
        self.location.setTextInteractionFlags(Qt.TextInteractionFlag.TextSelectableByMouse)
        self.location.setWordWrap(True);top.addWidget(self.location,1)
        self.revert_button=QPushButton('Revert maps…');self.revert_button.clicked.connect(self.revert);top.addWidget(self.revert_button)
        self.stop_button=QPushButton('Stop extraction');self.stop_button.clicked.connect(self.stop);self.stop_button.hide();top.addWidget(self.stop_button)
        search_row=QHBoxLayout();search_row.addStretch();layout.addLayout(search_row)
        self.search=CenteredMapSearch();self.search.setObjectName('map_search')
        self.search.setPlaceholderText('Type to search by name / Scenario')
        self.search.setAlignment(Qt.AlignmentFlag.AlignCenter);self.search.setMaximumWidth(820)
        self.search.setMinimumHeight(44);self.search.setClearButtonEnabled(True)
        self.search.textChanged.connect(self.filter);self.search.returnPressed.connect(self.accept_selection)
        search_row.addWidget(self.search,1);search_row.addStretch()
        self.tabs=QTabWidget();layout.addWidget(self.tabs,1)
        self.trees=[];self.empty_labels=[]
        for title in ('Recents','Select Map'):
            page=QWidget();pane=QVBoxLayout(page);pane.setContentsMargins(0,0,0,0);pane.setSpacing(0)
            tree=QTreeWidget();tree.setHeaderLabels(['Map','Scenario','Type','LINKDATA / entry'])
            tree.setRootIsDecorated(False);tree.setAlternatingRowColors(False)
            tree.setSelectionMode(QAbstractItemView.SelectionMode.SingleSelection)
            tree.setSortingEnabled(False)
            tree.header().setSectionResizeMode(0,QHeaderView.ResizeMode.Stretch)
            tree.setColumnWidth(1,245);tree.setColumnWidth(2,90);tree.setColumnWidth(3,360)
            tree.setColumnHidden(2,True);tree.setColumnHidden(3,True)
            tree.itemSelectionChanged.connect(self.selection_changed)
            tree.itemDoubleClicked.connect(lambda *_:self.accept_selection())
            pane.addWidget(tree,1)
            empty=QLabel();empty.setAlignment(Qt.AlignmentFlag.AlignCenter)
            empty.setStyleSheet('color: #aeb6c4; font-size: 14px; padding: 36px;')
            empty.hide();pane.addWidget(empty,1)
            self.trees.append(tree);self.empty_labels.append(empty);self.tabs.addTab(page,title)
        self.recent_tree,self.tree=self.trees
        self.tabs.setCurrentIndex(1);self.tabs.currentChanged.connect(self.filter)
        self.search.setValidator(MapSearchValidator(self))
        bottom=QHBoxLayout();layout.addLayout(bottom)
        self.map_debug_button=QToolButton();self.map_debug_button.setText('Debug')
        self.map_debug_button.setCheckable(True);self.map_debug_button.setFixedSize(48,22)
        self.map_debug_button.setStyleSheet('QToolButton { font-size: 10px; padding: 1px 4px; }')
        self.map_debug_button.setToolTip('Show LINKDATA archives and entry numbers')
        self.map_debug_button.toggled.connect(self.set_map_debug);bottom.addWidget(self.map_debug_button)
        self.clear_button=QPushButton('Clear all injected maps');self.clear_button.clicked.connect(self.clear_injected_maps)
        bottom.addWidget(self.clear_button)
        self.status=QLabel();self.status.hide();bottom.addWidget(self.status)
        bottom.addStretch()
        self.warning_button=QToolButton();self.warning_button.setObjectName('map_warning')
        self.warning_button.setIcon(self.style().standardIcon(QStyle.StandardPixmap.SP_MessageBoxWarning))
        self.warning_button.setIconSize(QSize(20,20))
        self.warning_button.setFixedSize(32,32);self.warning_button.setToolTip('Skipped maps - not implemented')
        self.warning_button.setAccessibleName('Show skipped map warnings')
        self.warning_button.clicked.connect(self.show_warnings);self.warning_button.hide();bottom.addWidget(self.warning_button)
        self.file_button=QPushButton('Open .binmap…');self.file_button.clicked.connect(self.choose_file);bottom.addWidget(self.file_button)
        self.open_button=QPushButton('Open map');self.open_button.clicked.connect(self.accept_selection);bottom.addWidget(self.open_button)
        self.open_button.setAutoDefault(False)
        close=QPushButton('Close');close.clicked.connect(self.reject);bottom.addWidget(close)
        for button in self.findChildren(QPushButton):button.setAutoDefault(False)
        for widget in [self]+self.findChildren(QWidget):widget.installEventFilter(self)
        self.setTabOrder(self.search,self.tabs);self.setTabOrder(self.tabs,self.tree)
        self.revert_button.setEnabled(bool(store));self.clear_button.setEnabled(bool(store));self.file_button.setEnabled(bool(store));self.open_button.setEnabled(False)
        if store:self.set_exe_path(store.exe);self.populate()
        elif exe:QTimer.singleShot(0,lambda:self.load(exe))
        else:self.filter()
        QTimer.singleShot(0,self.search.setFocus)

    def set_map_debug(self,enabled):
        for tree in self.trees:tree.setColumnHidden(3,not enabled)

    def eventFilter(self,watched,event):
        if event.type()==QEvent.Type.KeyPress:
            focus=QApplication.focusWidget()
            if isinstance(focus,QLineEdit):return super().eventFilter(watched,event)
            mods=event.modifiers()
            if mods & (Qt.KeyboardModifier.ControlModifier|Qt.KeyboardModifier.AltModifier|Qt.KeyboardModifier.MetaModifier):
                if event.key()==Qt.Key.Key_F and mods==Qt.KeyboardModifier.ControlModifier:
                    self.search.setFocus();self.search.selectAll();return True
                return super().eventFilter(watched,event)
            if event.text() and event.text().isprintable():
                self.search.setFocus();self.search.insert(event.text());return True
            if event.key()==Qt.Key.Key_Backspace:
                self.search.setFocus();self.search.backspace();return True
        return super().eventFilter(watched,event)

    def set_exe_path(self,exe):
        path=Path(exe) if exe else None
        self.location.setText(str(path) if path else 'No game EXE selected')
        self.location.setToolTip(str(path) if path else '')
        self.choose_button.setProperty('exeFound',bool(path and path.is_file()))
        self.choose_button.style().unpolish(self.choose_button);self.choose_button.style().polish(self.choose_button)
        self.choose_button.update()

    def choose(self):
        initial=str(self.store.exe) if self.store else self.location.toolTip()
        path,_=QFileDialog.getOpenFileName(self,'Select game executable',initial,'AoT2 executable (*.exe)')
        if path:self.load(path)
        self.search.setFocus()

    def load(self,exe):
        if self.busy:return
        self.busy=True;self.store=None;self.load_error='';self.selected_document=None
        for tree in self.trees:tree.clear()
        self.warning_button.hide();self.choose_button.setEnabled(False)
        self.revert_button.setEnabled(False);self.clear_button.setEnabled(False);self.file_button.setEnabled(False);self.open_button.setEnabled(False)
        self.stop_button.show();self.set_exe_path(exe);self.status.setText('Loading maps…');self.status.show()
        self.filter();self.search.setFocus()
        self.worker=MapExtraction(exe,self)
        self.worker.progress.connect(self.extraction_progress)
        self.worker.completed.connect(self.loaded);self.worker.failed.connect(self.load_failed)
        self.worker.finished.connect(self.extraction_finished);self.worker.start()

    def extraction_progress(self,done,total,name):self.status.setText(f'{name} - {done:,} / {total:,}')

    def load_failed(self,message):self.load_error=message;self.status.setText(message)

    def loaded(self,store):
        self.store=store;self.set_exe_path(store.exe);self.populate()

    def map_item(self,key,row,path=None):
        archives={}
        for part in row['parts']:archives.setdefault(part['archive'],[]).append(str(part['entry']))
        targets='\n'.join(f'{Path(path).name} [{", ".join(entries)}]' for path,entries in archives.items())
        item=QTreeWidgetItem([row['name'],Path(row['identifier']).stem,'DLC' if row['kind']=='bundle' else 'Scenario',targets])
        item.setToolTip(3,'\n'.join(f'{ {None:"Scenario",5:"Placements",6:"Events"}[part["section"]]}: '+
            f'{self.store.archive_path(part["archive"])} [{part["entry"]}]' for part in row['parts']))
        item.setData(0,Qt.ItemDataRole.UserRole,key)
        item.setData(0,Qt.ItemDataRole.UserRole+1,str(path or self.store.local(row['original']['file'])))
        item.setData(0,Qt.ItemDataRole.UserRole+2,(item.text(0)+' '+item.text(1)).casefold())
        return item

    def populate(self,choose_tab=True):
        for tree in self.trees:tree.clear()
        for key,row in sorted(self.store.data['maps'].items(),key=map_selection_order):
            if not self.store.local(row['original']['file']).is_file():continue
            self.tree.addTopLevelItem(self.map_item(key,row))
        modified=[]
        for key,row in self.store.data['maps'].items():
            for version in row['versions']:
                path=self.store.local(version['file'])
                if not path.is_file():continue
                try:saved=datetime.strptime(version['saved_utc'],'%Y-%m-%d_%H-%M-%S_%fZ').replace(tzinfo=timezone.utc)
                except (KeyError,ValueError):saved=datetime.fromtimestamp(path.stat().st_mtime,timezone.utc)
                modified.append((saved,key,row,path))
        for saved,key,row,path in sorted(modified,key=lambda value:(value[0],str(value[3])),reverse=True):
            item=self.map_item(key,row,path)
            stamp=saved.astimezone().strftime('%d %b %Y, %H:%M:%S')
            item.setText(0,f'{row["name"]} - {stamp}');item.setToolTip(0,str(path))
            item.setData(0,Qt.ItemDataRole.UserRole+2,(item.text(0)+' '+item.text(1)).casefold())
            self.recent_tree.addTopLevelItem(item)
        if choose_tab:self.tabs.setCurrentIndex(0 if self.recent_tree.topLevelItemCount() else 1)
        self.warning_button.setVisible(bool(self.store.data['scan_errors']))
        self.filter()

    def extraction_finished(self):
        self.busy=False;self.choose_button.setEnabled(True);self.stop_button.hide()
        self.status.hide();self.revert_button.setEnabled(bool(self.store));self.clear_button.setEnabled(bool(self.store));self.file_button.setEnabled(bool(self.store))
        self.filter()
        if self.close_pending:super().reject()

    def show_warnings(self):
        if not self.store or not self.store.data['scan_errors']:return
        dialog=QDialog(self);dialog.setWindowTitle('Skipped maps');dialog.resize(820,400)
        layout=QVBoxLayout(dialog);details=QPlainTextEdit();details.setReadOnly(True)
        details.setPlainText('IGNORE, NOT IMPLEMENTED\n\n'+'\n'.join(self.store.data['scan_errors']))
        layout.addWidget(details,1)
        buttons=QDialogButtonBox(QDialogButtonBox.StandardButton.Close);buttons.rejected.connect(dialog.reject);layout.addWidget(buttons)
        dialog.exec()

    def stop(self):
        if self.worker:self.worker.requestInterruption()

    def filter(self,*_):
        text=self.search.text().strip().casefold();counts=[]
        for index,tree in enumerate(self.trees):
            visible=0
            for i in range(tree.topLevelItemCount()):
                item=tree.topLevelItem(i)
                # Keep deletion/replacement responsive after a failed search.
                match=text in item.data(0,Qt.ItemDataRole.UserRole+2)
                item.setHidden(not match);visible+=int(match)
            counts.append(visible);empty=self.empty_labels[index]
            tree.setVisible(bool(visible));empty.setVisible(not visible)
            empty.setText('Loading maps…' if self.busy else self.load_error or
                ('Select your game EXE to load maps.' if not self.store else
                 'No maps match your search.' if text else
                 'No modified maps yet. Choose a map in Select Map, then save your changes.' if index==0 else 'No maps available.'))
        self.filtered_query=self.search.text();self.match_counts=counts
        self.selection_changed()

    def selection_changed(self):
        item=self.trees[self.tabs.currentIndex()].currentItem()
        self.open_button.setEnabled(bool(self.store and item and not item.isHidden() and not self.busy))

    def accept_selection(self):
        if not self.open_button.isEnabled():return
        item=self.trees[self.tabs.currentIndex()].currentItem()
        self.key=item.data(0,Qt.ItemDataRole.UserRole)
        # Select Map opens Original; a Recents row explicitly selects that save.
        self.path=item.data(0,Qt.ItemDataRole.UserRole+1)
        self.selected_document=None;self.accept()

    def choose_file(self):
        if not self.store or self.busy:return
        path,_=QFileDialog.getOpenFileName(self,'Open saved map',str(self.store.folder/'modified'),'Extracted maps (*.binmap)')
        if not path:return
        try:
            store=MapStore(self.store.exe);document=store.open_file(path)
        except Exception as error:QMessageBox.critical(self,'Cannot open map',str(error));return
        self.store=store;self.selected_document=document;self.key=document.map_id;self.path=str(path);self.accept()

    def open_selected(self):return self.selected_document or self.store.open(self.key,self.path)

    def clear_injected_maps(self):
        if not self.store or self.busy:return
        self.clear_button.setEnabled(False)
        try:
            # Read the latest index before restoring all archived map entries.
            fresh=MapStore(self.store.exe);reclaimed=fresh.clear_injections()
            self.store.data=fresh.data;self.cleared_game_root=self.store.root
            self.populate(choose_tab=False)
        except Exception as error:
            QMessageBox.critical(self,'Cleanup failed',str(error));return
        finally:self.clear_button.setEnabled(True)
        QMessageBox.information(self,'Injected maps cleared',
            'All maps restored to their original archive entries.\n'+
            f'Recovered {reclaimed/1048576:.2f} MB.\n\nSaved .binmap files are kept.')

    def revert(self):
        if self.store:
            dialog=RevertMaps(self.store,self)
            if dialog.exec()==QDialog.DialogCode.Accepted:self.populate(choose_tab=False)

    def reject(self):
        if self.busy and self.worker and self.worker.isRunning():
            self.close_pending=True;self.worker.requestInterruption();self.status.setText('Finishing current map…');return
        super().reject()


def main():
    app=QApplication(sys.argv);app.setStyle('Fusion');app.setStyleSheet(DARK_STYLE)
    try:
        saved_exe=remembered_game_exe()
        exe=Path(sys.argv[1]) if len(sys.argv)>1 else Path(saved_exe) if saved_exe else None
        if exe is not None:scenario.require(exe.suffix.lower()=='.exe','Select the game EXE; maps are opened only through the extracted map library')
        browser=MapBrowser(exe=exe)
        if browser.exec()!=QDialog.DialogCode.Accepted:return 0
        window=EditorWindow(browser.open_selected())
    except Exception as error:QMessageBox.critical(None,'AoT2 Scenario Editor',str(error));return 1
    window.open_maximized(browser.screen());return app.exec()


if __name__=='__main__':sys.exit(main())
