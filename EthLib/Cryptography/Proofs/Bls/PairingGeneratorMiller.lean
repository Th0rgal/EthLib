import EthLib.Cryptography.Proofs.Bls.PairingGeneratorMillerSteps
namespace EthLib.Cryptography.Bls.PairingCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem run62 : millerLoop.go blsX R P 1 D61 f61 = f62 := step62.trans (rfl)
theorem run61 : millerLoop.go blsX R P 2 D60 f60 = f62 := step61.trans (run62)
theorem run60 : millerLoop.go blsX R P 3 D59 f59 = f62 := step60.trans (run61)
theorem run59 : millerLoop.go blsX R P 4 D58 f58 = f62 := step59.trans (run60)
theorem run58 : millerLoop.go blsX R P 5 D57 f57 = f62 := step58.trans (run59)
theorem run57 : millerLoop.go blsX R P 6 D56 f56 = f62 := step57.trans (run58)
theorem run56 : millerLoop.go blsX R P 7 D55 f55 = f62 := step56.trans (run57)
theorem run55 : millerLoop.go blsX R P 8 D54 f54 = f62 := step55.trans (run56)
theorem run54 : millerLoop.go blsX R P 9 D53 f53 = f62 := step54.trans (run55)
theorem run53 : millerLoop.go blsX R P 10 D52 f52 = f62 := step53.trans (run54)
theorem run52 : millerLoop.go blsX R P 11 D51 f51 = f62 := step52.trans (run53)
theorem run51 : millerLoop.go blsX R P 12 D50 f50 = f62 := step51.trans (run52)
theorem run50 : millerLoop.go blsX R P 13 D49 f49 = f62 := step50.trans (run51)
theorem run49 : millerLoop.go blsX R P 14 D48 f48 = f62 := step49.trans (run50)
theorem run48 : millerLoop.go blsX R P 15 D47 f47 = f62 := step48.trans (run49)
theorem run47 : millerLoop.go blsX R P 16 A46 f46 = f62 := step47.trans (run48)
theorem run46 : millerLoop.go blsX R P 17 D45 f45 = f62 := step46.trans (run47)
theorem run45 : millerLoop.go blsX R P 18 D44 f44 = f62 := step45.trans (run46)
theorem run44 : millerLoop.go blsX R P 19 D43 f43 = f62 := step44.trans (run45)
theorem run43 : millerLoop.go blsX R P 20 D42 f42 = f62 := step43.trans (run44)
theorem run42 : millerLoop.go blsX R P 21 D41 f41 = f62 := step42.trans (run43)
theorem run41 : millerLoop.go blsX R P 22 D40 f40 = f62 := step41.trans (run42)
theorem run40 : millerLoop.go blsX R P 23 D39 f39 = f62 := step40.trans (run41)
theorem run39 : millerLoop.go blsX R P 24 D38 f38 = f62 := step39.trans (run40)
theorem run38 : millerLoop.go blsX R P 25 D37 f37 = f62 := step38.trans (run39)
theorem run37 : millerLoop.go blsX R P 26 D36 f36 = f62 := step37.trans (run38)
theorem run36 : millerLoop.go blsX R P 27 D35 f35 = f62 := step36.trans (run37)
theorem run35 : millerLoop.go blsX R P 28 D34 f34 = f62 := step35.trans (run36)
theorem run34 : millerLoop.go blsX R P 29 D33 f33 = f62 := step34.trans (run35)
theorem run33 : millerLoop.go blsX R P 30 D32 f32 = f62 := step33.trans (run34)
theorem run32 : millerLoop.go blsX R P 31 D31 f31 = f62 := step32.trans (run33)
theorem run31 : millerLoop.go blsX R P 32 D30 f30 = f62 := step31.trans (run32)
theorem run30 : millerLoop.go blsX R P 33 D29 f29 = f62 := step30.trans (run31)
theorem run29 : millerLoop.go blsX R P 34 D28 f28 = f62 := step29.trans (run30)
theorem run28 : millerLoop.go blsX R P 35 D27 f27 = f62 := step28.trans (run29)
theorem run27 : millerLoop.go blsX R P 36 D26 f26 = f62 := step27.trans (run28)
theorem run26 : millerLoop.go blsX R P 37 D25 f25 = f62 := step26.trans (run27)
theorem run25 : millerLoop.go blsX R P 38 D24 f24 = f62 := step25.trans (run26)
theorem run24 : millerLoop.go blsX R P 39 D23 f23 = f62 := step24.trans (run25)
theorem run23 : millerLoop.go blsX R P 40 D22 f22 = f62 := step23.trans (run24)
theorem run22 : millerLoop.go blsX R P 41 D21 f21 = f62 := step22.trans (run23)
theorem run21 : millerLoop.go blsX R P 42 D20 f20 = f62 := step21.trans (run22)
theorem run20 : millerLoop.go blsX R P 43 D19 f19 = f62 := step20.trans (run21)
theorem run19 : millerLoop.go blsX R P 44 D18 f18 = f62 := step19.trans (run20)
theorem run18 : millerLoop.go blsX R P 45 D17 f17 = f62 := step18.trans (run19)
theorem run17 : millerLoop.go blsX R P 46 D16 f16 = f62 := step17.trans (run18)
theorem run16 : millerLoop.go blsX R P 47 D15 f15 = f62 := step16.trans (run17)
theorem run15 : millerLoop.go blsX R P 48 A14 f14 = f62 := step15.trans (run16)
theorem run14 : millerLoop.go blsX R P 49 D13 f13 = f62 := step14.trans (run15)
theorem run13 : millerLoop.go blsX R P 50 D12 f12 = f62 := step13.trans (run14)
theorem run12 : millerLoop.go blsX R P 51 D11 f11 = f62 := step12.trans (run13)
theorem run11 : millerLoop.go blsX R P 52 D10 f10 = f62 := step11.trans (run12)
theorem run10 : millerLoop.go blsX R P 53 D9 f9 = f62 := step10.trans (run11)
theorem run9 : millerLoop.go blsX R P 54 D8 f8 = f62 := step9.trans (run10)
theorem run8 : millerLoop.go blsX R P 55 D7 f7 = f62 := step8.trans (run9)
theorem run7 : millerLoop.go blsX R P 56 D6 f6 = f62 := step7.trans (run8)
theorem run6 : millerLoop.go blsX R P 57 A5 f5 = f62 := step6.trans (run7)
theorem run5 : millerLoop.go blsX R P 58 D4 f4 = f62 := step5.trans (run6)
theorem run4 : millerLoop.go blsX R P 59 D3 f3 = f62 := step4.trans (run5)
theorem run3 : millerLoop.go blsX R P 60 A2 f2 = f62 := step3.trans (run4)
theorem run2 : millerLoop.go blsX R P 61 D1 f1 = f62 := step2.trans (run3)
theorem run1 : millerLoop.go blsX R P 62 A0 f0 = f62 := step1.trans (run2)
theorem run0 : millerLoop.go blsX R P 63 R Fp12.one = f62 := step0.trans (run1)
theorem loop_start (n : Nat) (R P : EmbeddedPoint) (k : Nat)
    (hr : R.inf = false) (hp : P.inf = false) (hk : n.log2 = k) :
    millerLoop n R P = millerLoop.go n R P k R Fp12.one := by
  simp only [millerLoop, hr, hp, Bool.false_or, Bool.false_eq_true, if_false, hk]

theorem loop_eq : millerLoop blsX (Embedded.ofG2 G2.generator) (Embedded.ofG1 G1.generator) = f62 := by
  have he : millerLoop blsX (Embedded.ofG2 G2.generator) (Embedded.ofG1 G1.generator) =
      millerLoop blsX R P := congrArg₂ (millerLoop blsX) R_eq P_eq
  have hs : millerLoop blsX R P = millerLoop.go blsX R P 63 R Fp12.one :=
    loop_start blsX R P 63 rfl rfl (by decide +kernel)
  exact he.trans (hs.trans run0)

def base : Fp12 := ⟨⟨⟨Fp.ofNat 3123211946202378851377988784307594402671252533842854381374902061945514429011720299288915601982686356857330067727371, Fp.ofNat 2963587891761959162813620596153286371132854266654288983256126277726818396552065672605067273260985705081894836086583⟩, ⟨Fp.ofNat 2521392541507826204070791783192365106154261552295178619108569057191635078966527105030939841270479379179414989177074, Fp.ofNat 3871471664561341402119086084943071224161338480024610904807809978881416909947686604624906262371955568089684748030478⟩, ⟨Fp.ofNat 253273568365393361425210965685643955954307646370037684631790896100357713877370898919058076839647599045297367014201, Fp.ofNat 3548482165003719855988277985985065558023157555655396779093506445657120199284977843288677901902239088622126504030609⟩⟩, ⟨⟨Fp.ofNat 1371832867185700980612534649761120060940739155332931829329745353210728414907910959726397898800632715989210226487845, Fp.ofNat 945139901409301334716510099996669795369870707152096756727788228130197865605512898435198003470462586999797295658091⟩, ⟨Fp.ofNat 3527552782288063992627902878344874742027487674772960288901740356293604940416990129553933455818257786546105619644155, Fp.ofNat 2041922342580490078329509996910434398113399006562150443686803162388080310562817226464059564954643025496456912520620⟩, ⟨Fp.ofNat 2012873700148761751344772321293983796066858847008703213565725237833465394711490892947566967312633511662818879432480, Fp.ofNat 1419402595267533106743680011957090853009907611945173272566144443521758953494251189151066548423721634430655744429497⟩⟩⟩
theorem base_eq : f62.conjugate = base := by decide +kernel
end EthLib.Cryptography.Bls.PairingCertificate
