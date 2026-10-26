import OrdinaryBridge

/- Additive V185 ordinary-map follow-up. No source core is modified.
   This file is a proof candidate until its compiler receipt is attached.
   Domain: q : Nat, n = 55863935003 + 2^37*q.
   The final ordinary endpoint may be even; no exact final accelerated
   valuation is asserted for the whole source cylinder. -/

namespace CollatzResearch
namespace V185Ordinary60Followup

private theorem step_00 (q : Nat) :
    collatzStep (55863935003 + 137438953472 * q) = (167591805010 + 412316860416 * q) := by
  simp only [collatzStep]
  split <;> omega

private theorem step_01 (q : Nat) :
    collatzStep (167591805010 + 412316860416 * q) = (83795902505 + 206158430208 * q) := by
  simp only [collatzStep]
  split <;> omega

private theorem step_02 (q : Nat) :
    collatzStep (83795902505 + 206158430208 * q) = (251387707516 + 618475290624 * q) := by
  simp only [collatzStep]
  split <;> omega

private theorem step_03 (q : Nat) :
    collatzStep (251387707516 + 618475290624 * q) = (125693853758 + 309237645312 * q) := by
  simp only [collatzStep]
  split <;> omega

private theorem step_04 (q : Nat) :
    collatzStep (125693853758 + 309237645312 * q) = (62846926879 + 154618822656 * q) := by
  simp only [collatzStep]
  split <;> omega

private theorem step_05 (q : Nat) :
    collatzStep (62846926879 + 154618822656 * q) = (188540780638 + 463856467968 * q) := by
  simp only [collatzStep]
  split <;> omega

private theorem step_06 (q : Nat) :
    collatzStep (188540780638 + 463856467968 * q) = (94270390319 + 231928233984 * q) := by
  simp only [collatzStep]
  split <;> omega

private theorem step_07 (q : Nat) :
    collatzStep (94270390319 + 231928233984 * q) = (282811170958 + 695784701952 * q) := by
  simp only [collatzStep]
  split <;> omega

private theorem step_08 (q : Nat) :
    collatzStep (282811170958 + 695784701952 * q) = (141405585479 + 347892350976 * q) := by
  simp only [collatzStep]
  split <;> omega

private theorem step_09 (q : Nat) :
    collatzStep (141405585479 + 347892350976 * q) = (424216756438 + 1043677052928 * q) := by
  simp only [collatzStep]
  split <;> omega

private theorem step_10 (q : Nat) :
    collatzStep (424216756438 + 1043677052928 * q) = (212108378219 + 521838526464 * q) := by
  simp only [collatzStep]
  split <;> omega

private theorem step_11 (q : Nat) :
    collatzStep (212108378219 + 521838526464 * q) = (636325134658 + 1565515579392 * q) := by
  simp only [collatzStep]
  split <;> omega

private theorem step_12 (q : Nat) :
    collatzStep (636325134658 + 1565515579392 * q) = (318162567329 + 782757789696 * q) := by
  simp only [collatzStep]
  split <;> omega

private theorem step_13 (q : Nat) :
    collatzStep (318162567329 + 782757789696 * q) = (954487701988 + 2348273369088 * q) := by
  simp only [collatzStep]
  split <;> omega

private theorem step_14 (q : Nat) :
    collatzStep (954487701988 + 2348273369088 * q) = (477243850994 + 1174136684544 * q) := by
  simp only [collatzStep]
  split <;> omega

private theorem step_15 (q : Nat) :
    collatzStep (477243850994 + 1174136684544 * q) = (238621925497 + 587068342272 * q) := by
  simp only [collatzStep]
  split <;> omega

private theorem step_16 (q : Nat) :
    collatzStep (238621925497 + 587068342272 * q) = (715865776492 + 1761205026816 * q) := by
  simp only [collatzStep]
  split <;> omega

private theorem step_17 (q : Nat) :
    collatzStep (715865776492 + 1761205026816 * q) = (357932888246 + 880602513408 * q) := by
  simp only [collatzStep]
  split <;> omega

private theorem step_18 (q : Nat) :
    collatzStep (357932888246 + 880602513408 * q) = (178966444123 + 440301256704 * q) := by
  simp only [collatzStep]
  split <;> omega

private theorem step_19 (q : Nat) :
    collatzStep (178966444123 + 440301256704 * q) = (536899332370 + 1320903770112 * q) := by
  simp only [collatzStep]
  split <;> omega

private theorem step_20 (q : Nat) :
    collatzStep (536899332370 + 1320903770112 * q) = (268449666185 + 660451885056 * q) := by
  simp only [collatzStep]
  split <;> omega

private theorem step_21 (q : Nat) :
    collatzStep (268449666185 + 660451885056 * q) = (805348998556 + 1981355655168 * q) := by
  simp only [collatzStep]
  split <;> omega

private theorem step_22 (q : Nat) :
    collatzStep (805348998556 + 1981355655168 * q) = (402674499278 + 990677827584 * q) := by
  simp only [collatzStep]
  split <;> omega

private theorem step_23 (q : Nat) :
    collatzStep (402674499278 + 990677827584 * q) = (201337249639 + 495338913792 * q) := by
  simp only [collatzStep]
  split <;> omega

private theorem step_24 (q : Nat) :
    collatzStep (201337249639 + 495338913792 * q) = (604011748918 + 1486016741376 * q) := by
  simp only [collatzStep]
  split <;> omega

private theorem step_25 (q : Nat) :
    collatzStep (604011748918 + 1486016741376 * q) = (302005874459 + 743008370688 * q) := by
  simp only [collatzStep]
  split <;> omega

private theorem step_26 (q : Nat) :
    collatzStep (302005874459 + 743008370688 * q) = (906017623378 + 2229025112064 * q) := by
  simp only [collatzStep]
  split <;> omega

private theorem step_27 (q : Nat) :
    collatzStep (906017623378 + 2229025112064 * q) = (453008811689 + 1114512556032 * q) := by
  simp only [collatzStep]
  split <;> omega

private theorem step_28 (q : Nat) :
    collatzStep (453008811689 + 1114512556032 * q) = (1359026435068 + 3343537668096 * q) := by
  simp only [collatzStep]
  split <;> omega

private theorem step_29 (q : Nat) :
    collatzStep (1359026435068 + 3343537668096 * q) = (679513217534 + 1671768834048 * q) := by
  simp only [collatzStep]
  split <;> omega

private theorem step_30 (q : Nat) :
    collatzStep (679513217534 + 1671768834048 * q) = (339756608767 + 835884417024 * q) := by
  simp only [collatzStep]
  split <;> omega

private theorem step_31 (q : Nat) :
    collatzStep (339756608767 + 835884417024 * q) = (1019269826302 + 2507653251072 * q) := by
  simp only [collatzStep]
  split <;> omega

private theorem step_32 (q : Nat) :
    collatzStep (1019269826302 + 2507653251072 * q) = (509634913151 + 1253826625536 * q) := by
  simp only [collatzStep]
  split <;> omega

private theorem step_33 (q : Nat) :
    collatzStep (509634913151 + 1253826625536 * q) = (1528904739454 + 3761479876608 * q) := by
  simp only [collatzStep]
  split <;> omega

private theorem step_34 (q : Nat) :
    collatzStep (1528904739454 + 3761479876608 * q) = (764452369727 + 1880739938304 * q) := by
  simp only [collatzStep]
  split <;> omega

private theorem step_35 (q : Nat) :
    collatzStep (764452369727 + 1880739938304 * q) = (2293357109182 + 5642219814912 * q) := by
  simp only [collatzStep]
  split <;> omega

private theorem step_36 (q : Nat) :
    collatzStep (2293357109182 + 5642219814912 * q) = (1146678554591 + 2821109907456 * q) := by
  simp only [collatzStep]
  split <;> omega

private theorem step_37 (q : Nat) :
    collatzStep (1146678554591 + 2821109907456 * q) = (3440035663774 + 8463329722368 * q) := by
  simp only [collatzStep]
  split <;> omega

private theorem step_38 (q : Nat) :
    collatzStep (3440035663774 + 8463329722368 * q) = (1720017831887 + 4231664861184 * q) := by
  simp only [collatzStep]
  split <;> omega

private theorem step_39 (q : Nat) :
    collatzStep (1720017831887 + 4231664861184 * q) = (5160053495662 + 12694994583552 * q) := by
  simp only [collatzStep]
  split <;> omega

private theorem step_40 (q : Nat) :
    collatzStep (5160053495662 + 12694994583552 * q) = (2580026747831 + 6347497291776 * q) := by
  simp only [collatzStep]
  split <;> omega

private theorem step_41 (q : Nat) :
    collatzStep (2580026747831 + 6347497291776 * q) = (7740080243494 + 19042491875328 * q) := by
  simp only [collatzStep]
  split <;> omega

private theorem step_42 (q : Nat) :
    collatzStep (7740080243494 + 19042491875328 * q) = (3870040121747 + 9521245937664 * q) := by
  simp only [collatzStep]
  split <;> omega

private theorem step_43 (q : Nat) :
    collatzStep (3870040121747 + 9521245937664 * q) = (11610120365242 + 28563737812992 * q) := by
  simp only [collatzStep]
  split <;> omega

private theorem step_44 (q : Nat) :
    collatzStep (11610120365242 + 28563737812992 * q) = (5805060182621 + 14281868906496 * q) := by
  simp only [collatzStep]
  split <;> omega

private theorem step_45 (q : Nat) :
    collatzStep (5805060182621 + 14281868906496 * q) = (17415180547864 + 42845606719488 * q) := by
  simp only [collatzStep]
  split <;> omega

private theorem step_46 (q : Nat) :
    collatzStep (17415180547864 + 42845606719488 * q) = (8707590273932 + 21422803359744 * q) := by
  simp only [collatzStep]
  split <;> omega

private theorem step_47 (q : Nat) :
    collatzStep (8707590273932 + 21422803359744 * q) = (4353795136966 + 10711401679872 * q) := by
  simp only [collatzStep]
  split <;> omega

private theorem step_48 (q : Nat) :
    collatzStep (4353795136966 + 10711401679872 * q) = (2176897568483 + 5355700839936 * q) := by
  simp only [collatzStep]
  split <;> omega

private theorem step_49 (q : Nat) :
    collatzStep (2176897568483 + 5355700839936 * q) = (6530692705450 + 16067102519808 * q) := by
  simp only [collatzStep]
  split <;> omega

private theorem step_50 (q : Nat) :
    collatzStep (6530692705450 + 16067102519808 * q) = (3265346352725 + 8033551259904 * q) := by
  simp only [collatzStep]
  split <;> omega

private theorem step_51 (q : Nat) :
    collatzStep (3265346352725 + 8033551259904 * q) = (9796039058176 + 24100653779712 * q) := by
  simp only [collatzStep]
  split <;> omega

private theorem step_52 (q : Nat) :
    collatzStep (9796039058176 + 24100653779712 * q) = (4898019529088 + 12050326889856 * q) := by
  simp only [collatzStep]
  split <;> omega

private theorem step_53 (q : Nat) :
    collatzStep (4898019529088 + 12050326889856 * q) = (2449009764544 + 6025163444928 * q) := by
  simp only [collatzStep]
  split <;> omega

private theorem step_54 (q : Nat) :
    collatzStep (2449009764544 + 6025163444928 * q) = (1224504882272 + 3012581722464 * q) := by
  simp only [collatzStep]
  split <;> omega

private theorem step_55 (q : Nat) :
    collatzStep (1224504882272 + 3012581722464 * q) = (612252441136 + 1506290861232 * q) := by
  simp only [collatzStep]
  split <;> omega

private theorem step_56 (q : Nat) :
    collatzStep (612252441136 + 1506290861232 * q) = (306126220568 + 753145430616 * q) := by
  simp only [collatzStep]
  split <;> omega

private theorem step_57 (q : Nat) :
    collatzStep (306126220568 + 753145430616 * q) = (153063110284 + 376572715308 * q) := by
  simp only [collatzStep]
  split <;> omega

private theorem step_58 (q : Nat) :
    collatzStep (153063110284 + 376572715308 * q) = (76531555142 + 188286357654 * q) := by
  simp only [collatzStep]
  split <;> omega

private theorem step_59 (q : Nat) :
    collatzStep (76531555142 + 188286357654 * q) = (38265777571 + 94143178827 * q) := by
  simp only [collatzStep]
  split <;> omega

private theorem block_00 (q : Nat) :
    ordinaryRun 5 (55863935003 + 137438953472 * q) = (62846926879 + 154618822656 * q) := by
  simp only [ordinaryRun, step_00, step_01, step_02, step_03, step_04]

private theorem block_01 (q : Nat) :
    ordinaryRun 5 (62846926879 + 154618822656 * q) = (424216756438 + 1043677052928 * q) := by
  simp only [ordinaryRun, step_05, step_06, step_07, step_08, step_09]

private theorem block_02 (q : Nat) :
    ordinaryRun 5 (424216756438 + 1043677052928 * q) = (477243850994 + 1174136684544 * q) := by
  simp only [ordinaryRun, step_10, step_11, step_12, step_13, step_14]

private theorem block_03 (q : Nat) :
    ordinaryRun 5 (477243850994 + 1174136684544 * q) = (536899332370 + 1320903770112 * q) := by
  simp only [ordinaryRun, step_15, step_16, step_17, step_18, step_19]

private theorem block_04 (q : Nat) :
    ordinaryRun 5 (536899332370 + 1320903770112 * q) = (604011748918 + 1486016741376 * q) := by
  simp only [ordinaryRun, step_20, step_21, step_22, step_23, step_24]

private theorem block_05 (q : Nat) :
    ordinaryRun 5 (604011748918 + 1486016741376 * q) = (679513217534 + 1671768834048 * q) := by
  simp only [ordinaryRun, step_25, step_26, step_27, step_28, step_29]

private theorem block_06 (q : Nat) :
    ordinaryRun 5 (679513217534 + 1671768834048 * q) = (764452369727 + 1880739938304 * q) := by
  simp only [ordinaryRun, step_30, step_31, step_32, step_33, step_34]

private theorem block_07 (q : Nat) :
    ordinaryRun 5 (764452369727 + 1880739938304 * q) = (5160053495662 + 12694994583552 * q) := by
  simp only [ordinaryRun, step_35, step_36, step_37, step_38, step_39]

private theorem block_08 (q : Nat) :
    ordinaryRun 5 (5160053495662 + 12694994583552 * q) = (5805060182621 + 14281868906496 * q) := by
  simp only [ordinaryRun, step_40, step_41, step_42, step_43, step_44]

private theorem block_09 (q : Nat) :
    ordinaryRun 5 (5805060182621 + 14281868906496 * q) = (6530692705450 + 16067102519808 * q) := by
  simp only [ordinaryRun, step_45, step_46, step_47, step_48, step_49]

private theorem block_10 (q : Nat) :
    ordinaryRun 5 (6530692705450 + 16067102519808 * q) = (1224504882272 + 3012581722464 * q) := by
  simp only [ordinaryRun, step_50, step_51, step_52, step_53, step_54]

private theorem block_11 (q : Nat) :
    ordinaryRun 5 (1224504882272 + 3012581722464 * q) = (38265777571 + 94143178827 * q) := by
  simp only [ordinaryRun, step_55, step_56, step_57, step_58, step_59]

/-- Exact ordinary 3n+1/halving endpoint for every member of the family. -/
theorem ordinary60_exact (q : Nat) :
    ordinaryRun 60 (55863935003 + 137438953472 * q) = (38265777571 + 94143178827 * q) := by
  calc
    ordinaryRun 60 (55863935003 + 137438953472 * q) = ordinaryRun 55 (ordinaryRun 5 (55863935003 + 137438953472 * q)) := by
      exact ordinaryRun_add 5 55 (55863935003 + 137438953472 * q)
    _ = ordinaryRun 55 (62846926879 + 154618822656 * q) := by
      rw [block_00 q]
    _ = ordinaryRun 50 (ordinaryRun 5 (62846926879 + 154618822656 * q)) := by
      exact ordinaryRun_add 5 50 (62846926879 + 154618822656 * q)
    _ = ordinaryRun 50 (424216756438 + 1043677052928 * q) := by
      rw [block_01 q]
    _ = ordinaryRun 45 (ordinaryRun 5 (424216756438 + 1043677052928 * q)) := by
      exact ordinaryRun_add 5 45 (424216756438 + 1043677052928 * q)
    _ = ordinaryRun 45 (477243850994 + 1174136684544 * q) := by
      rw [block_02 q]
    _ = ordinaryRun 40 (ordinaryRun 5 (477243850994 + 1174136684544 * q)) := by
      exact ordinaryRun_add 5 40 (477243850994 + 1174136684544 * q)
    _ = ordinaryRun 40 (536899332370 + 1320903770112 * q) := by
      rw [block_03 q]
    _ = ordinaryRun 35 (ordinaryRun 5 (536899332370 + 1320903770112 * q)) := by
      exact ordinaryRun_add 5 35 (536899332370 + 1320903770112 * q)
    _ = ordinaryRun 35 (604011748918 + 1486016741376 * q) := by
      rw [block_04 q]
    _ = ordinaryRun 30 (ordinaryRun 5 (604011748918 + 1486016741376 * q)) := by
      exact ordinaryRun_add 5 30 (604011748918 + 1486016741376 * q)
    _ = ordinaryRun 30 (679513217534 + 1671768834048 * q) := by
      rw [block_05 q]
    _ = ordinaryRun 25 (ordinaryRun 5 (679513217534 + 1671768834048 * q)) := by
      exact ordinaryRun_add 5 25 (679513217534 + 1671768834048 * q)
    _ = ordinaryRun 25 (764452369727 + 1880739938304 * q) := by
      rw [block_06 q]
    _ = ordinaryRun 20 (ordinaryRun 5 (764452369727 + 1880739938304 * q)) := by
      exact ordinaryRun_add 5 20 (764452369727 + 1880739938304 * q)
    _ = ordinaryRun 20 (5160053495662 + 12694994583552 * q) := by
      rw [block_07 q]
    _ = ordinaryRun 15 (ordinaryRun 5 (5160053495662 + 12694994583552 * q)) := by
      exact ordinaryRun_add 5 15 (5160053495662 + 12694994583552 * q)
    _ = ordinaryRun 15 (5805060182621 + 14281868906496 * q) := by
      rw [block_08 q]
    _ = ordinaryRun 10 (ordinaryRun 5 (5805060182621 + 14281868906496 * q)) := by
      exact ordinaryRun_add 5 10 (5805060182621 + 14281868906496 * q)
    _ = ordinaryRun 10 (6530692705450 + 16067102519808 * q) := by
      rw [block_09 q]
    _ = ordinaryRun 5 (ordinaryRun 5 (6530692705450 + 16067102519808 * q)) := by
      exact ordinaryRun_add 5 5 (6530692705450 + 16067102519808 * q)
    _ = ordinaryRun 5 (1224504882272 + 3012581722464 * q) := by
      rw [block_10 q]
    _ = (38265777571 + 94143178827 * q) := block_11 q

/-- Strict descent after the fixed 60 ordinary steps. -/
theorem ordinary60_descends (q : Nat) :
    ordinaryRun 60 (55863935003 + 137438953472 * q) < (55863935003 + 137438953472 * q) := by
  rw [ordinary60_exact q]
  omega

/-- Integer form of the strict 0.685 ordinary-step contraction bound. -/
theorem ordinary60_contraction_685 (q : Nat) :
    1000 * ordinaryRun 60 (55863935003 + 137438953472 * q) < 685 * (55863935003 + 137438953472 * q) := by
  rw [ordinary60_exact q]
  omega

end V185Ordinary60Followup
end CollatzResearch

#check CollatzResearch.V185Ordinary60Followup.ordinary60_exact
#check CollatzResearch.V185Ordinary60Followup.ordinary60_descends
#check CollatzResearch.V185Ordinary60Followup.ordinary60_contraction_685
#print axioms CollatzResearch.V185Ordinary60Followup.ordinary60_exact
#print axioms CollatzResearch.V185Ordinary60Followup.ordinary60_descends
#print axioms CollatzResearch.V185Ordinary60Followup.ordinary60_contraction_685
