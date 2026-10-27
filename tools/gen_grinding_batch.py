from pathlib import Path
import hashlib,sys
start=int(sys.argv[1]) if len(sys.argv)>1 else 0
count=int(sys.argv[2]) if len(sys.argv)>2 else 16
pp=bytes.fromhex('c487ed3aef7201c095bf4c74aad6b6e3')
seed=bytes(range(32));msg=bytes(i^0x5a for i in range(32))
p='''import EthLib.Cryptography.Proofs.Xmss.GrindingSupport
namespace EthLib.Cryptography.Xmss
open Constants Blake2s.Fast
set_option maxRecDepth 200000
set_option maxHeartbeats 20000000
'''
for t in range(start,start+count):
 tweak=bytes([0,7,0,0])+t.to_bytes(4,'little')+bytes(4)+(7).to_bytes(4,'little')
 rnd=hashlib.blake2s(tweak+pp+seed+msg).digest()[:24]
 p+=f'private def rnd{t} : Randomness := #v['+','.join(map(str,rnd))+']\n'
 p+=f'''private theorem rnd{t}_eq : randomizer examplePublicKey.publicParam grindingSeed exampleMessage 7 {t} = rnd{t} := by
  rw [randomizer_fast]
  decide +kernel
private theorem early_trial{t} : wotsEncode examplePublicKey.publicParam exampleMessage
    (randomizer examplePublicKey.publicParam grindingSeed exampleMessage 7 {t}) 7 = none := by
  rw [rnd{t}_eq,encode_fast]
  decide +kernel
'''
p+=f'''theorem no_early_{start}_{start+count} (t : Nat) (hlo : {start} ≤ t) (hhi : t < {start+count}) :
    wotsEncode examplePublicKey.publicParam exampleMessage
    (randomizer examplePublicKey.publicParam grindingSeed exampleMessage 7 t) 7 = none := by
  have ht : '''+' ∨ '.join(f't={i}' for i in range(start,start+count))+' := by omega\n'
p+='  rcases ht with '+' | '.join('rfl' for i in range(count))+'\n'
for t in range(start,start+count):p+=f'  · exact early_trial{t}\n'
p+=f'#print axioms no_early_{start}_{start+count}\n'
p+='end EthLib.Cryptography.Xmss\n'
out = Path(sys.argv[3]) if len(sys.argv)>3 else Path('EthLib/Cryptography/Proofs/Xmss/GrindingBatches')
out.mkdir(parents=True,exist_ok=True)
(out/f'GrindingBatch{start}_{start+count}.lean').write_text(p)
