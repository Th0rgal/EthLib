import EthLib.Cryptography.Kzg.TrustedSetupData
import EthLib.Cryptography.Kzg.Constants

namespace EthLib.Cryptography.Kzg.TrustedSetupData
open Constants

set_option maxRecDepth 65536

/-- The embedded monomial setup has the 4096 G1 powers required by blobs. -/
theorem g1MonomialHex_size : g1MonomialHex.size = 4096 := by rfl

/-- The embedded Lagrange setup has the 4096 blob-domain powers. -/
theorem g1LagrangeHex_size : g1LagrangeHex.size = 4096 := by rfl

/-- The embedded G2 monomial setup contains the degree-64 point used by cells. -/
theorem g2MonomialHex_size : g2MonomialHex.size = 65 := by rfl

/-- The first monomial entries are the canonical BLS generators. -/
theorem g1MonomialHex_head : g1MonomialHex[0]! =
    "97f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb" := by rfl

theorem g2MonomialHex_head : g2MonomialHex[0]! =
    "93e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb8" := by rfl

/-- A compact data-level obligation consumed by setup certification. -/
def ShapeCertificate : Prop :=
  g1MonomialHex.size = FIELD_ELEMENTS_PER_BLOB ∧
  g1LagrangeHex.size = FIELD_ELEMENTS_PER_BLOB ∧
  g2MonomialHex.size = FIELD_ELEMENTS_PER_CELL + 1

theorem shapeCertificate : ShapeCertificate :=
  ⟨g1MonomialHex_size, g1LagrangeHex_size, g2MonomialHex_size⟩

end EthLib.Cryptography.Kzg.TrustedSetupData
