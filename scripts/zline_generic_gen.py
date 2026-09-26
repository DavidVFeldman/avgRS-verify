import re,sys
base=open('/workspace/request-project/RequestProject/ZLineAlgBase.lean').read()
# extract structure fields
st=base[base.index('structure ZAlgData'):base.index('lemma deriv_ofNat')]
lines=st.split('\n')
fields={}
cur=None
for l in lines[1:]:
    m=re.match(r'  (h\w+) : (.*)',l)
    if m:
        cur=m.group(1); fields[cur]=m.group(2)
    elif cur and l.startswith('    '):
        fields[cur]+=' '+l.strip()
def tr(s):
    s=s.replace('Z.','')
    s=s.replace('d⁄dX ℚ','Dd')
    s=s.replace('(C t)','T').replace('C t','T').replace('(C w)','W').replace('C w','W')
    return s
def gen(src, name, used_fields, outname):
    txt=open(src).read()
    L=txt.split('\n')
    # find lemma line
    i=[k for k,l in enumerate(L) if l.startswith('lemma ')][0]
    j=[k for k,l in enumerate(L) if l.strip().startswith('obtain ⟨P, Ph')][0]
    header='\n'.join(L[i:j])
    # header: lemma NAME (Z : ZAlgData t w) (...) ... : concl := by
    m=re.match(r'lemma (\w+) \(Z : ZAlgData t w\)(.*):= by\s*$',header,re.S)
    rest=m.group(2)
    lc=[l for l in L if l.strip().startswith('linear_combination')]
    assert len(lc)==1
    simpl=[l for l in L[j:] if l.strip().startswith('simp only')]
    vars='X T W P Ph Q P1 Ph1 Q1 Qh1 p0 q0 p1 q1 G00 G01 G10 G11 D DZ'
    hyps=' '.join('(%s : %s)'%(f,tr(fields[f])) for f in used_fields)
    out=f'''module

public import Mathlib

@[expose] public section

namespace AvgRS

set_option maxHeartbeats 0
set_option maxRecDepth 20000
set_option linter.all false

lemma {outname} {{R : Type*}} [CommRing R] (Dd : Derivation ℤ R R) ({vars} : R)
    (dX : Dd X = 1) (dT : Dd T = 0) (dW : Dd W = 0) {hyps}
   {tr(rest)}:= by
  have d2 : ∀ n : ℕ, [n.AtLeastTwo] → Dd (OfNat.ofNat n : R) = 0 := fun n _ => by
    rw [← Nat.cast_eq_ofNat]; exact Dd.map_natCast n
  simp only [map_add, map_sub, map_neg, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, dX, Derivation.map_one_eq_zero, d2, Nat.cast_ofNat, map_zero, dT, dW]
{lc[0]}

end AvgRS
'''
    return out
if __name__=='__main__':
    src,outname,outfile=sys.argv[1],sys.argv[2],sys.argv[3]
    used=sys.argv[4].split(',')
    open(outfile,'w').write(gen(src,None,used,outname))
