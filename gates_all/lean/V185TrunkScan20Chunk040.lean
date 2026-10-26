import V185TrunkScan20Chunk039

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_243040 : List Nat := [2, 1, 1, 3, 4, 1, 1, 1, 6]
def baseStart_243040 : Nat := 118140960795 + 243040 * 2 ^ 59
def prefixEnd_243040 : Nat := 4983230072969 + 3 ^ 40 * 243040 * 2
def baseEnd_243040 : Nat := 110930078461186078739809

theorem tailTrace_243040 : CollatzResearch.WordTrace tailWord_243040 prefixEnd_243040 110930078461186078739809 := by
  unfold tailWord_243040
  simp only [CollatzResearch.WordTrace]
  refine ⟨4432198519757531386247287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5909598026343375181663049 4432198519757531386247287)
  ·
    refine ⟨6648297779636297079370931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4432198519757531386247287 6648297779636297079370931)
    ·
      refine ⟨9972446669454445619056397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6648297779636297079370931 9972446669454445619056397)
      ·
        refine ⟨3739667501045417107146149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9972446669454445619056397 3739667501045417107146149)
        ·
          refine ⟨701187656446015707589903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3739667501045417107146149 701187656446015707589903)
          ·
            refine ⟨1051781484669023561384855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 701187656446015707589903 1051781484669023561384855)
            ·
              refine ⟨1577672227003535342077283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1051781484669023561384855 1577672227003535342077283)
              ·
                refine ⟨2366508340505303013115925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1577672227003535342077283 2366508340505303013115925)
                ·
                  refine ⟨110930078461186078739809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2366508340505303013115925 110930078461186078739809)
                  ·
                    rfl

theorem cell20_243040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 6].length) (baseStart_243040 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_243040 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_243040 prefixEnd_243040 := by exact prefixLift 243040
  have htrace : WordTrace (prefixWord ++ tailWord_243040) baseStart_243040 baseEnd_243040 := by
    simpa [prefixWord, tailWord_243040, baseEnd_243040] using wordTrace_append hprefix tailTrace_243040
  have hstable : (prefixWord ++ tailWord_243040).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243040).length < 2 ^ (prefixWord ++ tailWord_243040).sum := by decide
  have hdescent : baseEnd_243040 < baseStart_243040 := by decide
  rcases family_descends (prefixWord ++ tailWord_243040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243057 : List Nat := [1, 2, 2, 2, 1, 2, 3, 5, 2]
def baseStart_243057 : Nat := 118140960795 + 243057 * 2 ^ 59
def prefixEnd_243057 : Nat := 4983230072969 + 3 ^ 40 * 243057 * 2
def baseEnd_243057 : Nat := 110937837724409575173073

theorem tailTrace_243057 : CollatzResearch.WordTrace tailWord_243057 prefixEnd_243057 110937837724409575173073 := by
  unfold tailWord_243057
  simp only [CollatzResearch.WordTrace]
  refine ⟨8865017080453474675863425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5910011386968983117242283 8865017080453474675863425)
  ·
    refine ⟨6648762810340106006897569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8865017080453474675863425 6648762810340106006897569)
    ·
      refine ⟨4986572107755079505173177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6648762810340106006897569 4986572107755079505173177)
      ·
        refine ⟨3739929080816309628879883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4986572107755079505173177 3739929080816309628879883)
        ·
          refine ⟨5609893621224464443319825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3739929080816309628879883 5609893621224464443319825)
          ·
            refine ⟨4207420215918348332489869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5609893621224464443319825 4207420215918348332489869)
            ·
              refine ⟨1577782580969380624683701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4207420215918348332489869 1577782580969380624683701)
              ·
                refine ⟨147917116965879433564097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1577782580969380624683701 147917116965879433564097)
                ·
                  refine ⟨110937837724409575173073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 147917116965879433564097 110937837724409575173073)
                  ·
                    rfl

theorem cell20_243057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 5, 2].length) (baseStart_243057 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_243057 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_243057 prefixEnd_243057 := by exact prefixLift 243057
  have htrace : WordTrace (prefixWord ++ tailWord_243057) baseStart_243057 baseEnd_243057 := by
    simpa [prefixWord, tailWord_243057, baseEnd_243057] using wordTrace_append hprefix tailTrace_243057
  have hstable : (prefixWord ++ tailWord_243057).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243057).length < 2 ^ (prefixWord ++ tailWord_243057).sum := by decide
  have hdescent : baseEnd_243057 < baseStart_243057 := by decide
  rcases family_descends (prefixWord ++ tailWord_243057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243074 : List Nat := [3, 4, 2, 1, 1, 1, 1, 3, 4]
def baseStart_243074 : Nat := 118140960795 + 243074 * 2 ^ 59
def prefixEnd_243074 : Nat := 4983230072969 + 3 ^ 40 * 243074 * 2
def baseEnd_243074 : Nat := 110945596987633071606337

theorem tailTrace_243074 : CollatzResearch.WordTrace tailWord_243074 prefixEnd_243074 110945596987633071606337 := by
  unfold tailWord_243074
  simp only [CollatzResearch.WordTrace]
  refine ⟨2216409280347971644808069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5910424747594591052821517 2216409280347971644808069)
  ·
    refine ⟨415576740065244683401513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2216409280347971644808069 415576740065244683401513)
    ·
      refine ⟨311682555048933512551135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 415576740065244683401513 311682555048933512551135)
      ·
        refine ⟨467523832573400268826703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311682555048933512551135 467523832573400268826703)
        ·
          refine ⟨701285748860100403240055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 467523832573400268826703 701285748860100403240055)
          ·
            refine ⟨1051928623290150604860083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 701285748860100403240055 1051928623290150604860083)
            ·
              refine ⟨1577892934935225907290125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1051928623290150604860083 1577892934935225907290125)
              ·
                refine ⟨591709850600709715233797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1577892934935225907290125 591709850600709715233797)
                ·
                  refine ⟨110945596987633071606337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 591709850600709715233797 110945596987633071606337)
                  ·
                    rfl

theorem cell20_243074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_243074 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_243074 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_243074 prefixEnd_243074 := by exact prefixLift 243074
  have htrace : WordTrace (prefixWord ++ tailWord_243074) baseStart_243074 baseEnd_243074 := by
    simpa [prefixWord, tailWord_243074, baseEnd_243074] using wordTrace_append hprefix tailTrace_243074
  have hstable : (prefixWord ++ tailWord_243074).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243074).length < 2 ^ (prefixWord ++ tailWord_243074).sum := by decide
  have hdescent : baseEnd_243074 < baseStart_243074 := by decide
  rcases family_descends (prefixWord ++ tailWord_243074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243129 : List Nat := [1, 2, 1, 4, 4, 1, 3, 2, 2]
def baseStart_243129 : Nat := 118140960795 + 243129 * 2 ^ 59
def prefixEnd_243129 : Nat := 4983230072969 + 3 ^ 40 * 243129 * 2
def baseEnd_243129 : Nat := 110970700486297324772779

theorem tailTrace_243129 : CollatzResearch.WordTrace tailWord_243129 prefixEnd_243129 110970700486297324772779 := by
  unfold tailWord_243129
  simp only [CollatzResearch.WordTrace]
  refine ⟨8867643136192630972484441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5911762090795087314989627 8867643136192630972484441)
  ·
    refine ⟨6650732352144473229363331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8867643136192630972484441 6650732352144473229363331)
    ·
      refine ⟨9976098528216709844044997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6650732352144473229363331 9976098528216709844044997)
      ·
        refine ⟨1870518474040633095758437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9976098528216709844044997 1870518474040633095758437)
        ·
          refine ⟨350722213882618705454707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1870518474040633095758437 350722213882618705454707)
          ·
            refine ⟨526083320823928058182061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350722213882618705454707 526083320823928058182061)
            ·
              refine ⟨197281245308973021818273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 526083320823928058182061 197281245308973021818273)
              ·
                refine ⟨147960933981729766363705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 197281245308973021818273 147960933981729766363705)
                ·
                  refine ⟨110970700486297324772779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 147960933981729766363705 110970700486297324772779)
                  ·
                    rfl

theorem cell20_243129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 3, 2, 2].length) (baseStart_243129 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_243129 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_243129 prefixEnd_243129 := by exact prefixLift 243129
  have htrace : WordTrace (prefixWord ++ tailWord_243129) baseStart_243129 baseEnd_243129 := by
    simpa [prefixWord, tailWord_243129, baseEnd_243129] using wordTrace_append hprefix tailTrace_243129
  have hstable : (prefixWord ++ tailWord_243129).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243129).length < 2 ^ (prefixWord ++ tailWord_243129).sum := by decide
  have hdescent : baseEnd_243129 < baseStart_243129 := by decide
  rcases family_descends (prefixWord ++ tailWord_243129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243140 : List Nat := [2, 3, 3, 2, 1, 1, 1, 7]
def baseStart_243140 : Nat := 118140960795 + 243140 * 2 ^ 59
def prefixEnd_243140 : Nat := 4983230072969 + 3 ^ 40 * 243140 * 2
def baseEnd_243140 : Nat := 36991907062010058468689

theorem tailTrace_243140 : CollatzResearch.WordTrace tailWord_243140 prefixEnd_243140 36991907062010058468689 := by
  unfold tailWord_243140
  simp only [CollatzResearch.WordTrace]
  refine ⟨4434022169576389925567437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5912029559435186567423249 4434022169576389925567437)
  ·
    refine ⟨1662758313591146222087789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4434022169576389925567437 1662758313591146222087789)
    ·
      refine ⟨623534367596679833282921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1662758313591146222087789 623534367596679833282921)
      ·
        refine ⟨467650775697509874962191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 623534367596679833282921 467650775697509874962191)
        ·
          refine ⟨701476163546264812443287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 467650775697509874962191 701476163546264812443287)
          ·
            refine ⟨1052214245319397218664931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 701476163546264812443287 1052214245319397218664931)
            ·
              refine ⟨1578321367979095827997397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1052214245319397218664931 1578321367979095827997397)
              ·
                refine ⟨36991907062010058468689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1578321367979095827997397 36991907062010058468689)
                ·
                  rfl

theorem cell20_243140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 7].length) (baseStart_243140 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_243140 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_243140 prefixEnd_243140 := by exact prefixLift 243140
  have htrace : WordTrace (prefixWord ++ tailWord_243140) baseStart_243140 baseEnd_243140 := by
    simpa [prefixWord, tailWord_243140, baseEnd_243140] using wordTrace_append hprefix tailTrace_243140
  have hstable : (prefixWord ++ tailWord_243140).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243140).length < 2 ^ (prefixWord ++ tailWord_243140).sum := by decide
  have hdescent : baseEnd_243140 < baseStart_243140 := by decide
  rcases family_descends (prefixWord ++ tailWord_243140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243161 : List Nat := [1, 2, 1, 2, 4, 2, 2, 6]
def baseStart_243161 : Nat := 118140960795 + 243161 * 2 ^ 59
def prefixEnd_243161 : Nat := 4983230072969 + 3 ^ 40 * 243161 * 2
def baseEnd_243161 : Nat := 36995102052749145235327

theorem tailTrace_243161 : CollatzResearch.WordTrace tailWord_243161 prefixEnd_243161 36995102052749145235327 := by
  unfold tailWord_243161
  simp only [CollatzResearch.WordTrace]
  refine ⟨8868810272076700437649337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5912540181384466958432891 8868810272076700437649337)
  ·
    refine ⟨6651607704057525328237003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8868810272076700437649337 6651607704057525328237003)
    ·
      refine ⟨9977411556086287992355505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6651607704057525328237003 9977411556086287992355505)
      ·
        refine ⟨7483058667064715994266629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9977411556086287992355505 7483058667064715994266629)
        ·
          refine ⟨1403073500074634248924993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7483058667064715994266629 1403073500074634248924993)
          ·
            refine ⟨1052305125055975686693745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1403073500074634248924993 1052305125055975686693745)
            ·
              refine ⟨789228843791981765020309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1052305125055975686693745 789228843791981765020309)
              ·
                refine ⟨36995102052749145235327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 789228843791981765020309 36995102052749145235327)
                ·
                  rfl

theorem cell20_243161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 6].length) (baseStart_243161 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_243161 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_243161 prefixEnd_243161 := by exact prefixLift 243161
  have htrace : WordTrace (prefixWord ++ tailWord_243161) baseStart_243161 baseEnd_243161 := by
    simpa [prefixWord, tailWord_243161, baseEnd_243161] using wordTrace_append hprefix tailTrace_243161
  have hstable : (prefixWord ++ tailWord_243161).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243161).length < 2 ^ (prefixWord ++ tailWord_243161).sum := by decide
  have hdescent : baseEnd_243161 < baseStart_243161 := by decide
  rcases family_descends (prefixWord ++ tailWord_243161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243168 : List Nat := [2, 1, 1, 3, 1, 1, 2, 4, 5]
def baseStart_243168 : Nat := 118140960795 + 243168 * 2 ^ 59
def prefixEnd_243168 : Nat := 4983230072969 + 3 ^ 40 * 243168 * 2
def baseEnd_243168 : Nat := 110988501148986522472619

theorem tailTrace_243168 : CollatzResearch.WordTrace tailWord_243168 prefixEnd_243168 110988501148986522472619 := by
  unfold tailWord_243168
  simp only [CollatzResearch.WordTrace]
  refine ⟨4434532791525670316577079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5912710388700893755436105 4434532791525670316577079)
  ·
    refine ⟨6651799187288505474865619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4434532791525670316577079 6651799187288505474865619)
    ·
      refine ⟨9977698780932758212298429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6651799187288505474865619 9977698780932758212298429)
      ·
        refine ⟨3741637042849784329611911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9977698780932758212298429 3741637042849784329611911)
        ·
          refine ⟨5612455564274676494417867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3741637042849784329611911 5612455564274676494417867)
          ·
            refine ⟨8418683346412014741626801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5612455564274676494417867 8418683346412014741626801)
            ·
              refine ⟨6314012509809011056220101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8418683346412014741626801 6314012509809011056220101)
              ·
                refine ⟨1183877345589189573041269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6314012509809011056220101 1183877345589189573041269)
                ·
                  refine ⟨110988501148986522472619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1183877345589189573041269 110988501148986522472619)
                  ·
                    rfl

theorem cell20_243168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4, 5].length) (baseStart_243168 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_243168 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_243168 prefixEnd_243168 := by exact prefixLift 243168
  have htrace : WordTrace (prefixWord ++ tailWord_243168) baseStart_243168 baseEnd_243168 := by
    simpa [prefixWord, tailWord_243168, baseEnd_243168] using wordTrace_append hprefix tailTrace_243168
  have hstable : (prefixWord ++ tailWord_243168).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243168).length < 2 ^ (prefixWord ++ tailWord_243168).sum := by decide
  have hdescent : baseEnd_243168 < baseStart_243168 := by decide
  rcases family_descends (prefixWord ++ tailWord_243168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243178 : List Nat := [3, 1, 3, 1, 5, 7]
def baseStart_243178 : Nat := 118140960795 + 243178 * 2 ^ 59
def prefixEnd_243178 : Nat := 4983230072969 + 3 ^ 40 * 243178 * 2
def baseEnd_243178 : Nat := 4110854274869293782935

theorem tailTrace_243178 : CollatzResearch.WordTrace tailWord_243178 prefixEnd_243178 4110854274869293782935 := by
  unfold tailWord_243178
  simp only [CollatzResearch.WordTrace]
  refine ⟨2217357578253778085254547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5912953542010074894012125 2217357578253778085254547)
  ·
    refine ⟨3326036367380667127881821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2217357578253778085254547 3326036367380667127881821)
    ·
      refine ⟨1247263637767750172955683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3326036367380667127881821 1247263637767750172955683)
      ·
        refine ⟨1870895456651625259433525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1247263637767750172955683 1870895456651625259433525)
        ·
          refine ⟨175396449061089868071893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1870895456651625259433525 175396449061089868071893)
          ·
            refine ⟨4110854274869293782935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 175396449061089868071893 4110854274869293782935)
            ·
              rfl

theorem cell20_243178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 7].length) (baseStart_243178 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_243178 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_243178 prefixEnd_243178 := by exact prefixLift 243178
  have htrace : WordTrace (prefixWord ++ tailWord_243178) baseStart_243178 baseEnd_243178 := by
    simpa [prefixWord, tailWord_243178, baseEnd_243178] using wordTrace_append hprefix tailTrace_243178
  have hstable : (prefixWord ++ tailWord_243178).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243178).length < 2 ^ (prefixWord ++ tailWord_243178).sum := by decide
  have hdescent : baseEnd_243178 < baseStart_243178 := by decide
  rcases family_descends (prefixWord ++ tailWord_243178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243181 : List Nat := [1, 5, 1, 3, 2, 1, 2, 2, 3]
def baseStart_243181 : Nat := 118140960795 + 243181 * 2 ^ 59
def prefixEnd_243181 : Nat := 4983230072969 + 3 ^ 40 * 243181 * 2
def baseEnd_243181 : Nat := 110994434703216255039233

theorem tailTrace_243181 : CollatzResearch.WordTrace tailWord_243181 prefixEnd_243181 110994434703216255039233 := by
  unfold tailWord_243181
  simp only [CollatzResearch.WordTrace]
  refine ⟨8869539732004243853377397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5913026488002829235584931 8869539732004243853377397)
  ·
    refine ⟨831519349875397861254131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8869539732004243853377397 831519349875397861254131)
    ·
      refine ⟨1247279024813096791881197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 831519349875397861254131 1247279024813096791881197)
      ·
        refine ⟨467729634304911296955449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1247279024813096791881197 467729634304911296955449)
        ·
          refine ⟨350797225728683472716587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 467729634304911296955449 350797225728683472716587)
          ·
            refine ⟨526195838593025209074881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350797225728683472716587 526195838593025209074881)
            ·
              refine ⟨394646878944768906806161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 526195838593025209074881 394646878944768906806161)
              ·
                refine ⟨295985159208576680104621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 394646878944768906806161 295985159208576680104621)
                ·
                  refine ⟨110994434703216255039233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 295985159208576680104621 110994434703216255039233)
                  ·
                    rfl

theorem cell20_243181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_243181 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_243181 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_243181 prefixEnd_243181 := by exact prefixLift 243181
  have htrace : WordTrace (prefixWord ++ tailWord_243181) baseStart_243181 baseEnd_243181 := by
    simpa [prefixWord, tailWord_243181, baseEnd_243181] using wordTrace_append hprefix tailTrace_243181
  have hstable : (prefixWord ++ tailWord_243181).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243181).length < 2 ^ (prefixWord ++ tailWord_243181).sum := by decide
  have hdescent : baseEnd_243181 < baseStart_243181 := by decide
  rcases family_descends (prefixWord ++ tailWord_243181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243185 : List Nat := [1, 2, 2, 2, 3, 2, 1, 4, 3]
def baseStart_243185 : Nat := 118140960795 + 243185 * 2 ^ 59
def prefixEnd_243185 : Nat := 4983230072969 + 3 ^ 40 * 243185 * 2
def baseEnd_243185 : Nat := 110996260412210018905883

theorem tailTrace_243185 : CollatzResearch.WordTrace tailWord_243185 prefixEnd_243185 110996260412210018905883 := by
  unfold tailWord_243185
  simp only [CollatzResearch.WordTrace]
  refine ⟨8869685623989752536523009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5913123749326501691015339 8869685623989752536523009)
  ·
    refine ⟨6652264217992314402392257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8869685623989752536523009 6652264217992314402392257)
    ·
      refine ⟨4989198163494235801794193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6652264217992314402392257 4989198163494235801794193)
      ·
        refine ⟨3741898622620676851345645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4989198163494235801794193 3741898622620676851345645)
        ·
          refine ⟨1403211983482753819254617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3741898622620676851345645 1403211983482753819254617)
          ·
            refine ⟨1052408987612065364440963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1403211983482753819254617 1052408987612065364440963)
            ·
              refine ⟨1578613481418098046661445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1052408987612065364440963 1578613481418098046661445)
              ·
                refine ⟨295990027765893383749021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1578613481418098046661445 295990027765893383749021)
                ·
                  refine ⟨110996260412210018905883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 295990027765893383749021 110996260412210018905883)
                  ·
                    rfl

theorem cell20_243185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 4, 3].length) (baseStart_243185 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_243185 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_243185 prefixEnd_243185 := by exact prefixLift 243185
  have htrace : WordTrace (prefixWord ++ tailWord_243185) baseStart_243185 baseEnd_243185 := by
    simpa [prefixWord, tailWord_243185, baseEnd_243185] using wordTrace_append hprefix tailTrace_243185
  have hstable : (prefixWord ++ tailWord_243185).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243185).length < 2 ^ (prefixWord ++ tailWord_243185).sum := by decide
  have hdescent : baseEnd_243185 < baseStart_243185 := by decide
  rcases family_descends (prefixWord ++ tailWord_243185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243240 : List Nat := [2, 1, 5, 2, 2, 1, 1, 1, 5]
def baseStart_243240 : Nat := 118140960795 + 243240 * 2 ^ 59
def prefixEnd_243240 : Nat := 4983230072969 + 3 ^ 40 * 243240 * 2
def baseEnd_243240 : Nat := 111021363910874272072325

theorem tailTrace_243240 : CollatzResearch.WordTrace tailWord_243240 prefixEnd_243240 111021363910874272072325 := by
  unfold tailWord_243240
  simp only [CollatzResearch.WordTrace]
  refine ⟨4435845819395248464887587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5914461092526997953183449 4435845819395248464887587)
  ·
    refine ⟨6653768729092872697331381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4435845819395248464887587 6653768729092872697331381)
    ·
      refine ⟨623790818352456815374817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6653768729092872697331381 623790818352456815374817)
      ·
        refine ⟨467843113764342611531113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 623790818352456815374817 467843113764342611531113)
        ·
          refine ⟨350882335323256958648335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 467843113764342611531113 350882335323256958648335)
          ·
            refine ⟨526323502984885437972503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350882335323256958648335 526323502984885437972503)
            ·
              refine ⟨789485254477328156958755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 526323502984885437972503 789485254477328156958755)
              ·
                refine ⟨1184227881715992235438133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 789485254477328156958755 1184227881715992235438133)
                ·
                  refine ⟨111021363910874272072325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1184227881715992235438133 111021363910874272072325)
                  ·
                    rfl

theorem cell20_243240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 1, 5].length) (baseStart_243240 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_243240 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_243240 prefixEnd_243240 := by exact prefixLift 243240
  have htrace : WordTrace (prefixWord ++ tailWord_243240) baseStart_243240 baseEnd_243240 := by
    simpa [prefixWord, tailWord_243240, baseEnd_243240] using wordTrace_append hprefix tailTrace_243240
  have hstable : (prefixWord ++ tailWord_243240).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243240).length < 2 ^ (prefixWord ++ tailWord_243240).sum := by decide
  have hdescent : baseEnd_243240 < baseStart_243240 := by decide
  rcases family_descends (prefixWord ++ tailWord_243240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243271 : List Nat := [1, 1, 4, 1, 5, 2, 2, 4]
def baseStart_243271 : Nat := 118140960795 + 243271 * 2 ^ 59
def prefixEnd_243271 : Nat := 4983230072969 + 3 ^ 40 * 243271 * 2
def baseEnd_243271 : Nat := 37011837718525314012955

theorem tailTrace_243271 : CollatzResearch.WordTrace tailWord_243271 prefixEnd_243271 37011837718525314012955 := by
  unfold tailWord_243271
  simp only [CollatzResearch.WordTrace]
  refine ⟨8872822301678189224153667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5915214867785459482769111 8872822301678189224153667)
  ·
    refine ⟨13309233452517283836230501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8872822301678189224153667 13309233452517283836230501)
    ·
      refine ⟨2495481272346990719293219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13309233452517283836230501 2495481272346990719293219)
      ·
        refine ⟨3743221908520486078939829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2495481272346990719293219 3743221908520486078939829)
        ·
          refine ⟨350927053923795569900609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3743221908520486078939829 350927053923795569900609)
          ·
            refine ⟨263195290442846677425457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 350927053923795569900609 263195290442846677425457)
            ·
              refine ⟨197396467832135008069093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 263195290442846677425457 197396467832135008069093)
              ·
                refine ⟨37011837718525314012955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 197396467832135008069093 37011837718525314012955)
                ·
                  rfl

theorem cell20_243271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 2, 4].length) (baseStart_243271 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_243271 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_243271 prefixEnd_243271 := by exact prefixLift 243271
  have htrace : WordTrace (prefixWord ++ tailWord_243271) baseStart_243271 baseEnd_243271 := by
    simpa [prefixWord, tailWord_243271, baseEnd_243271] using wordTrace_append hprefix tailTrace_243271
  have hstable : (prefixWord ++ tailWord_243271).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243271).length < 2 ^ (prefixWord ++ tailWord_243271).sum := by decide
  have hdescent : baseEnd_243271 < baseStart_243271 := by decide
  rcases family_descends (prefixWord ++ tailWord_243271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243289 : List Nat := [1, 2, 1, 2, 2, 1, 1, 4, 6]
def baseStart_243289 : Nat := 118140960795 + 243289 * 2 ^ 59
def prefixEnd_243289 : Nat := 4983230072969 + 3 ^ 40 * 243289 * 2
def baseEnd_243289 : Nat := 111043728846047879438791

theorem tailTrace_243289 : CollatzResearch.WordTrace tailWord_243289 prefixEnd_243289 111043728846047879438791 := by
  unfold tailWord_243289
  simp only [CollatzResearch.WordTrace]
  refine ⟨8873478815612978298308921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5915652543741985532205947 8873478815612978298308921)
  ·
    refine ⟨6655109111709733723731691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8873478815612978298308921 6655109111709733723731691)
    ·
      refine ⟨9982663667564600585597537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6655109111709733723731691 9982663667564600585597537)
      ·
        refine ⟨7486997750673450439198153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9982663667564600585597537 7486997750673450439198153)
        ·
          refine ⟨5615248313005087829398615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7486997750673450439198153 5615248313005087829398615)
          ·
            refine ⟨8422872469507631744097923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5615248313005087829398615 8422872469507631744097923)
            ·
              refine ⟨12634308704261447616146885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8422872469507631744097923 12634308704261447616146885)
              ·
                refine ⟨2368932882049021428027541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12634308704261447616146885 2368932882049021428027541)
                ·
                  refine ⟨111043728846047879438791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2368932882049021428027541 111043728846047879438791)
                  ·
                    rfl

theorem cell20_243289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 6].length) (baseStart_243289 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_243289 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_243289 prefixEnd_243289 := by exact prefixLift 243289
  have htrace : WordTrace (prefixWord ++ tailWord_243289) baseStart_243289 baseEnd_243289 := by
    simpa [prefixWord, tailWord_243289, baseEnd_243289] using wordTrace_append hprefix tailTrace_243289
  have hstable : (prefixWord ++ tailWord_243289).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243289).length < 2 ^ (prefixWord ++ tailWord_243289).sum := by decide
  have hdescent : baseEnd_243289 < baseStart_243289 := by decide
  rcases family_descends (prefixWord ++ tailWord_243289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243292 : List Nat := [2, 2, 4, 1, 2, 3, 6]
def baseStart_243292 : Nat := 118140960795 + 243292 * 2 ^ 59
def prefixEnd_243292 : Nat := 4983230072969 + 3 ^ 40 * 243292 * 2
def baseEnd_243292 : Nat := 12338344236421466926531

theorem tailTrace_243292 : CollatzResearch.WordTrace tailWord_243292 prefixEnd_243292 12338344236421466926531 := by
  unfold tailWord_243292
  simp only [CollatzResearch.WordTrace]
  refine ⟨4436794117301054905334065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5915725489734739873778753 4436794117301054905334065)
  ·
    refine ⟨3327595587975791179000549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4436794117301054905334065 3327595587975791179000549)
    ·
      refine ⟨623924172745460846062603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3327595587975791179000549 623924172745460846062603)
      ·
        refine ⟨935886259118191269093905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 623924172745460846062603 935886259118191269093905)
        ·
          refine ⟨701914694338643451820429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 935886259118191269093905 701914694338643451820429)
          ·
            refine ⟨263218010376991294432661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 701914694338643451820429 263218010376991294432661)
            ·
              refine ⟨12338344236421466926531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 263218010376991294432661 12338344236421466926531)
              ·
                rfl

theorem cell20_243292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 6].length) (baseStart_243292 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_243292 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_243292 prefixEnd_243292 := by exact prefixLift 243292
  have htrace : WordTrace (prefixWord ++ tailWord_243292) baseStart_243292 baseEnd_243292 := by
    simpa [prefixWord, tailWord_243292, baseEnd_243292] using wordTrace_append hprefix tailTrace_243292
  have hstable : (prefixWord ++ tailWord_243292).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243292).length < 2 ^ (prefixWord ++ tailWord_243292).sum := by decide
  have hdescent : baseEnd_243292 < baseStart_243292 := by decide
  rcases family_descends (prefixWord ++ tailWord_243292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243399 : List Nat := [1, 1, 4, 1, 1, 1, 6, 3, 2]
def baseStart_243399 : Nat := 118140960795 + 243399 * 2 ^ 59
def prefixEnd_243399 : Nat := 4983230072969 + 3 ^ 40 * 243399 * 2
def baseEnd_243399 : Nat := 111093935843376385771675

theorem tailTrace_243399 : CollatzResearch.WordTrace tailWord_243399 prefixEnd_243399 111093935843376385771675 := by
  unfold tailWord_243399
  simp only [CollatzResearch.WordTrace]
  refine ⟨8877490845214467084813251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5918327230142978056542167 8877490845214467084813251)
  ·
    refine ⟨13316236267821700627219877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8877490845214467084813251 13316236267821700627219877)
    ·
      refine ⟨2496794300216568867603727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13316236267821700627219877 2496794300216568867603727)
      ·
        refine ⟨3745191450324853301405591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2496794300216568867603727 3745191450324853301405591)
        ·
          refine ⟨5617787175487279952108387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3745191450324853301405591 5617787175487279952108387)
          ·
            refine ⟨8426680763230919928162581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5617787175487279952108387 8426680763230919928162581)
            ·
              refine ⟨395000660776449371632621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8426680763230919928162581 395000660776449371632621)
              ·
                refine ⟨148125247791168514362233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 395000660776449371632621 148125247791168514362233)
                ·
                  refine ⟨111093935843376385771675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 148125247791168514362233 111093935843376385771675)
                  ·
                    rfl

theorem cell20_243399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 3, 2].length) (baseStart_243399 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_243399 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_243399 prefixEnd_243399 := by exact prefixLift 243399
  have htrace : WordTrace (prefixWord ++ tailWord_243399) baseStart_243399 baseEnd_243399 := by
    simpa [prefixWord, tailWord_243399, baseEnd_243399] using wordTrace_append hprefix tailTrace_243399
  have hstable : (prefixWord ++ tailWord_243399).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243399).length < 2 ^ (prefixWord ++ tailWord_243399).sum := by decide
  have hdescent : baseEnd_243399 < baseStart_243399 := by decide
  rcases family_descends (prefixWord ++ tailWord_243399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243489 : List Nat := [1, 2, 3, 2, 1, 4, 1, 3, 3]
def baseStart_243489 : Nat := 118140960795 + 243489 * 2 ^ 59
def prefixEnd_243489 : Nat := 4983230072969 + 3 ^ 40 * 243489 * 2
def baseEnd_243489 : Nat := 111135014295736072771307

theorem tailTrace_243489 : CollatzResearch.WordTrace tailWord_243489 prefixEnd_243489 111135014295736072771307 := by
  unfold tailWord_243489
  simp only [CollatzResearch.WordTrace]
  refine ⟨8880773414888412455589521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5920515609925608303726347 8880773414888412455589521)
  ·
    refine ⟨6660580061166309341692141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8880773414888412455589521 6660580061166309341692141)
    ·
      refine ⟨2497717522937366003134553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6660580061166309341692141 2497717522937366003134553)
      ·
        refine ⟨1873288142203024502350915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2497717522937366003134553 1873288142203024502350915)
        ·
          refine ⟨2809932213304536753526373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1873288142203024502350915 2809932213304536753526373)
          ·
            refine ⟨526862289994600641286195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2809932213304536753526373 526862289994600641286195)
            ·
              refine ⟨790293434991900961929293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 526862289994600641286195 790293434991900961929293)
              ·
                refine ⟨296360038121962860723485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 790293434991900961929293 296360038121962860723485)
                ·
                  refine ⟨111135014295736072771307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 296360038121962860723485 111135014295736072771307)
                  ·
                    rfl

theorem cell20_243489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 3, 3].length) (baseStart_243489 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_243489 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_243489 prefixEnd_243489 := by exact prefixLift 243489
  have htrace : WordTrace (prefixWord ++ tailWord_243489) baseStart_243489 baseEnd_243489 := by
    simpa [prefixWord, tailWord_243489, baseEnd_243489] using wordTrace_append hprefix tailTrace_243489
  have hstable : (prefixWord ++ tailWord_243489).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243489).length < 2 ^ (prefixWord ++ tailWord_243489).sum := by decide
  have hdescent : baseEnd_243489 < baseStart_243489 := by decide
  rcases family_descends (prefixWord ++ tailWord_243489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243526 : List Nat := [6, 1, 1, 2, 1, 1, 4, 2, 2]
def baseStart_243526 : Nat := 118140960795 + 243526 * 2 ^ 59
def prefixEnd_243526 : Nat := 4983230072969 + 3 ^ 40 * 243526 * 2
def baseEnd_243526 : Nat := 111151902103928388537823

theorem tailTrace_243526 : CollatzResearch.WordTrace tailWord_243526 prefixEnd_243526 111151902103928388537823 := by
  unfold tailWord_243526
  simp only [CollatzResearch.WordTrace]
  refine ⟨277566341117323992958951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5921415277169578516457621 277566341117323992958951)
  ·
    refine ⟨416349511675985989438427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277566341117323992958951 416349511675985989438427)
    ·
      refine ⟨624524267513978984157641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416349511675985989438427 624524267513978984157641)
      ·
        refine ⟨468393200635484238118231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 624524267513978984157641 468393200635484238118231)
        ·
          refine ⟨702589800953226357177347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 468393200635484238118231 702589800953226357177347)
          ·
            refine ⟨1053884701429839535766021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 702589800953226357177347 1053884701429839535766021)
            ·
              refine ⟨197603381518094912956129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1053884701429839535766021 197603381518094912956129)
              ·
                refine ⟨148202536138571184717097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 197603381518094912956129 148202536138571184717097)
                ·
                  refine ⟨111151902103928388537823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 148202536138571184717097 111151902103928388537823)
                  ·
                    rfl

theorem cell20_243526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_243526 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_243526 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_243526 prefixEnd_243526 := by exact prefixLift 243526
  have htrace : WordTrace (prefixWord ++ tailWord_243526) baseStart_243526 baseEnd_243526 := by
    simpa [prefixWord, tailWord_243526, baseEnd_243526] using wordTrace_append hprefix tailTrace_243526
  have hstable : (prefixWord ++ tailWord_243526).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243526).length < 2 ^ (prefixWord ++ tailWord_243526).sum := by decide
  have hdescent : baseEnd_243526 < baseStart_243526 := by decide
  rcases family_descends (prefixWord ++ tailWord_243526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243541 : List Nat := [1, 3, 2, 2, 2, 2, 3, 5]
def baseStart_243541 : Nat := 118140960795 + 243541 * 2 ^ 59
def prefixEnd_243541 : Nat := 4983230072969 + 3 ^ 40 * 243541 * 2
def baseEnd_243541 : Nat := 37052916170885001012587

theorem tailTrace_243541 : CollatzResearch.WordTrace tailWord_243541 prefixEnd_243541 37052916170885001012587 := by
  unfold tailWord_243541
  simp only [CollatzResearch.WordTrace]
  refine ⟨8882670010700025336482477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5921780007133350224321651 8882670010700025336482477)
  ·
    refine ⟨3331001254012509501180929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8882670010700025336482477 3331001254012509501180929)
    ·
      refine ⟨2498250940509382125885697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3331001254012509501180929 2498250940509382125885697)
      ·
        refine ⟨1873688205382036594414273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2498250940509382125885697 1873688205382036594414273)
        ·
          refine ⟨1405266154036527445810705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1873688205382036594414273 1405266154036527445810705)
          ·
            refine ⟨1053949615527395584358029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1405266154036527445810705 1053949615527395584358029)
            ·
              refine ⟨395231105822773344134261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1053949615527395584358029 395231105822773344134261)
              ·
                refine ⟨37052916170885001012587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 395231105822773344134261 37052916170885001012587)
                ·
                  rfl

theorem cell20_243541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 5].length) (baseStart_243541 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_243541 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_243541 prefixEnd_243541 := by exact prefixLift 243541
  have htrace : WordTrace (prefixWord ++ tailWord_243541) baseStart_243541 baseEnd_243541 := by
    simpa [prefixWord, tailWord_243541, baseEnd_243541] using wordTrace_append hprefix tailTrace_243541
  have hstable : (prefixWord ++ tailWord_243541).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243541).length < 2 ^ (prefixWord ++ tailWord_243541).sum := by decide
  have hdescent : baseEnd_243541 < baseStart_243541 := by decide
  rcases family_descends (prefixWord ++ tailWord_243541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243582 : List Nat := [4, 2, 3, 1, 1, 2, 1, 1, 5]
def baseStart_243582 : Nat := 118140960795 + 243582 * 2 ^ 59
def prefixEnd_243582 : Nat := 4983230072969 + 3 ^ 40 * 243582 * 2
def baseEnd_243582 : Nat := 111177462029841082670927

theorem tailTrace_243582 : CollatzResearch.WordTrace tailWord_243582 prefixEnd_243582 111177462029841082670927 := by
  unfold tailWord_243582
  simp only [CollatzResearch.WordTrace]
  refine ⟨1110520675443936167340625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5922776935700992892483333 1110520675443936167340625)
  ·
    refine ⟨832890506582952125505469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1110520675443936167340625 832890506582952125505469)
    ·
      refine ⟨312333939968607047064551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 832890506582952125505469 312333939968607047064551)
      ·
        refine ⟨468500909952910570596827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312333939968607047064551 468500909952910570596827)
        ·
          refine ⟨702751364929365855895241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 468500909952910570596827 702751364929365855895241)
          ·
            refine ⟨527063523697024391921431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 702751364929365855895241 527063523697024391921431)
            ·
              refine ⟨790595285545536587882147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 527063523697024391921431 790595285545536587882147)
              ·
                refine ⟨1185892928318304881823221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 790595285545536587882147 1185892928318304881823221)
                ·
                  refine ⟨111177462029841082670927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1185892928318304881823221 111177462029841082670927)
                  ·
                    rfl

theorem cell20_243582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_243582 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_243582 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_243582 prefixEnd_243582 := by exact prefixLift 243582
  have htrace : WordTrace (prefixWord ++ tailWord_243582) baseStart_243582 baseEnd_243582 := by
    simpa [prefixWord, tailWord_243582, baseEnd_243582] using wordTrace_append hprefix tailTrace_243582
  have hstable : (prefixWord ++ tailWord_243582).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243582).length < 2 ^ (prefixWord ++ tailWord_243582).sum := by decide
  have hdescent : baseEnd_243582 < baseStart_243582 := by decide
  rcases family_descends (prefixWord ++ tailWord_243582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243610 : List Nat := [3, 1, 1, 4, 2, 1, 2, 2, 4]
def baseStart_243610 : Nat := 118140960795 + 243610 * 2 ^ 59
def prefixEnd_243610 : Nat := 4983230072969 + 3 ^ 40 * 243610 * 2
def baseEnd_243610 : Nat := 111190241992797429737479

theorem tailTrace_243610 : CollatzResearch.WordTrace tailWord_243610 prefixEnd_243610 111190241992797429737479 := by
  unfold tailWord_243610
  simp only [CollatzResearch.WordTrace]
  refine ⟨2221296661862512530186071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5923457764966700080496189 2221296661862512530186071)
  ·
    refine ⟨3331944992793768795279107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2221296661862512530186071 3331944992793768795279107)
    ·
      refine ⟨4997917489190653192918661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3331944992793768795279107 4997917489190653192918661)
      ·
        refine ⟨937109529223247473672249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4997917489190653192918661 937109529223247473672249)
        ·
          refine ⟨702832146917435605254187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 937109529223247473672249 702832146917435605254187)
          ·
            refine ⟨1054248220376153407881281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 702832146917435605254187 1054248220376153407881281)
            ·
              refine ⟨790686165282115055910961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1054248220376153407881281 790686165282115055910961)
              ·
                refine ⟨593014623961586291933221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 790686165282115055910961 593014623961586291933221)
                ·
                  refine ⟨111190241992797429737479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 593014623961586291933221 111190241992797429737479)
                  ·
                    rfl

theorem cell20_243610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 2, 4].length) (baseStart_243610 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_243610 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_243610 prefixEnd_243610 := by exact prefixLift 243610
  have htrace : WordTrace (prefixWord ++ tailWord_243610) baseStart_243610 baseEnd_243610 := by
    simpa [prefixWord, tailWord_243610, baseEnd_243610] using wordTrace_append hprefix tailTrace_243610
  have hstable : (prefixWord ++ tailWord_243610).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243610).length < 2 ^ (prefixWord ++ tailWord_243610).sum := by decide
  have hdescent : baseEnd_243610 < baseStart_243610 := by decide
  rcases family_descends (prefixWord ++ tailWord_243610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243630 : List Nat := [4, 1, 5, 1, 1, 2, 6]
def baseStart_243630 : Nat := 118140960795 + 243630 * 2 ^ 59
def prefixEnd_243630 : Nat := 4983230072969 + 3 ^ 40 * 243630 * 2
def baseEnd_243630 : Nat := 12355485615307361007859

theorem tailTrace_243630 : CollatzResearch.WordTrace tailWord_243630 prefixEnd_243630 12355485615307361007859 := by
  unfold tailWord_243630
  simp only [CollatzResearch.WordTrace]
  refine ⟨1110739513422199192059043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5923944071585062357648229 1110739513422199192059043)
  ·
    refine ⟨1666109270133298788088565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1110739513422199192059043 1666109270133298788088565)
    ·
      refine ⟨156197744074996761383303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1666109270133298788088565 156197744074996761383303)
      ·
        refine ⟨234296616112495142074955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156197744074996761383303 234296616112495142074955)
        ·
          refine ⟨351444924168742713112433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234296616112495142074955 351444924168742713112433)
          ·
            refine ⟨263583693126557034834325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 351444924168742713112433 263583693126557034834325)
            ·
              refine ⟨12355485615307361007859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 263583693126557034834325 12355485615307361007859)
              ·
                rfl

theorem cell20_243630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 6].length) (baseStart_243630 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_243630 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_243630 prefixEnd_243630 := by exact prefixLift 243630
  have htrace : WordTrace (prefixWord ++ tailWord_243630) baseStart_243630 baseEnd_243630 := by
    simpa [prefixWord, tailWord_243630, baseEnd_243630] using wordTrace_append hprefix tailTrace_243630
  have hstable : (prefixWord ++ tailWord_243630).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243630).length < 2 ^ (prefixWord ++ tailWord_243630).sum := by decide
  have hdescent : baseEnd_243630 < baseStart_243630 := by decide
  rcases family_descends (prefixWord ++ tailWord_243630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243644 : List Nat := [2, 2, 2, 5, 1, 2, 1, 1, 4]
def baseStart_243644 : Nat := 118140960795 + 243644 * 2 ^ 59
def prefixEnd_243644 : Nat := 4983230072969 + 3 ^ 40 * 243644 * 2
def baseEnd_243644 : Nat := 111205760519244422604007

theorem tailTrace_243644 : CollatzResearch.WordTrace tailWord_243644 prefixEnd_243644 111205760519244422604007 := by
  unfold tailWord_243644
  simp only [CollatzResearch.WordTrace]
  refine ⟨4443213364663436963740993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5924284486217915951654657 4443213364663436963740993)
  ·
    refine ⟨3332410023497577722805745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4443213364663436963740993 3332410023497577722805745)
    ·
      refine ⟨2499307517623183292104309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3332410023497577722805745 2499307517623183292104309)
      ·
        refine ⟨234310079777173433634779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2499307517623183292104309 234310079777173433634779)
        ·
          refine ⟨351465119665760150452169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234310079777173433634779 351465119665760150452169)
          ·
            refine ⟨263598839749320112839127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 351465119665760150452169 263598839749320112839127)
            ·
              refine ⟨395398259623980169258691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263598839749320112839127 395398259623980169258691)
              ·
                refine ⟨593097389435970253888037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 395398259623980169258691 593097389435970253888037)
                ·
                  refine ⟨111205760519244422604007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 593097389435970253888037 111205760519244422604007)
                  ·
                    rfl

theorem cell20_243644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 1, 4].length) (baseStart_243644 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_243644 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_243644 prefixEnd_243644 := by exact prefixLift 243644
  have htrace : WordTrace (prefixWord ++ tailWord_243644) baseStart_243644 baseEnd_243644 := by
    simpa [prefixWord, tailWord_243644, baseEnd_243644] using wordTrace_append hprefix tailTrace_243644
  have hstable : (prefixWord ++ tailWord_243644).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243644).length < 2 ^ (prefixWord ++ tailWord_243644).sum := by decide
  have hdescent : baseEnd_243644 < baseStart_243644 := by decide
  rcases family_descends (prefixWord ++ tailWord_243644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243693 : List Nat := [1, 5, 1, 4, 9]
def baseStart_243693 : Nat := 118140960795 + 243693 * 2 ^ 59
def prefixEnd_243693 : Nat := 4983230072969 + 3 ^ 40 * 243693 * 2
def baseEnd_243693 : Nat := 1373186734005160863833

theorem tailTrace_243693 : CollatzResearch.WordTrace tailWord_243693 prefixEnd_243693 1373186734005160863833 := by
  unfold tailWord_243693
  simp only [CollatzResearch.WordTrace]
  refine ⟨8888213906149355296015733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5925475937432903530677155 8888213906149355296015733)
  ·
    refine ⟨833270053701502059001475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8888213906149355296015733 833270053701502059001475)
    ·
      refine ⟨1249905080552253088502213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 833270053701502059001475 1249905080552253088502213)
      ·
        refine ⟨234357202603547454094165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1249905080552253088502213 234357202603547454094165)
        ·
          refine ⟨1373186734005160863833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 234357202603547454094165 1373186734005160863833)
          ·
            rfl

theorem cell20_243693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 9].length) (baseStart_243693 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_243693 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_243693 prefixEnd_243693 := by exact prefixLift 243693
  have htrace : WordTrace (prefixWord ++ tailWord_243693) baseStart_243693 baseEnd_243693 := by
    simpa [prefixWord, tailWord_243693, baseEnd_243693] using wordTrace_append hprefix tailTrace_243693
  have hstable : (prefixWord ++ tailWord_243693).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243693).length < 2 ^ (prefixWord ++ tailWord_243693).sum := by decide
  have hdescent : baseEnd_243693 < baseStart_243693 := by decide
  rcases family_descends (prefixWord ++ tailWord_243693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243710 : List Nat := [4, 2, 2, 2, 1, 1, 3, 5]
def baseStart_243710 : Nat := 118140960795 + 243710 * 2 ^ 59
def prefixEnd_243710 : Nat := 4983230072969 + 3 ^ 40 * 243710 * 2
def baseEnd_243710 : Nat := 37078628239213842134579

theorem tailTrace_243710 : CollatzResearch.WordTrace tailWord_243710 prefixEnd_243710 37078628239213842134579 := by
  unfold tailWord_243710
  simp only [CollatzResearch.WordTrace]
  refine ⟨1111104243385970899923073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5925889298058511466256389 1111104243385970899923073)
  ·
    refine ⟨833328182539478174942305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1111104243385970899923073 833328182539478174942305)
    ·
      refine ⟨624996136904608631206729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 833328182539478174942305 624996136904608631206729)
      ·
        refine ⟨468747102678456473405047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 624996136904608631206729 468747102678456473405047)
        ·
          refine ⟨703120654017684710107571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 468747102678456473405047 703120654017684710107571)
          ·
            refine ⟨1054680981026527065161357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 703120654017684710107571 1054680981026527065161357)
            ·
              refine ⟨395505367884947649435509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1054680981026527065161357 395505367884947649435509)
              ·
                refine ⟨37078628239213842134579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 395505367884947649435509 37078628239213842134579)
                ·
                  rfl

theorem cell20_243710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 5].length) (baseStart_243710 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_243710 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_243710 prefixEnd_243710 := by exact prefixLift 243710
  have htrace : WordTrace (prefixWord ++ tailWord_243710) baseStart_243710 baseEnd_243710 := by
    simpa [prefixWord, tailWord_243710, baseEnd_243710] using wordTrace_append hprefix tailTrace_243710
  have hstable : (prefixWord ++ tailWord_243710).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243710).length < 2 ^ (prefixWord ++ tailWord_243710).sum := by decide
  have hdescent : baseEnd_243710 < baseStart_243710 := by decide
  rcases family_descends (prefixWord ++ tailWord_243710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243721 : List Nat := [1, 2, 1, 1, 3, 1, 1, 1, 9]
def baseStart_243721 : Nat := 118140960795 + 243721 * 2 ^ 59
def prefixEnd_243721 : Nat := 4983230072969 + 3 ^ 40 * 243721 * 2
def baseEnd_243721 : Nat := 111240905417374377037025

theorem tailTrace_243721 : CollatzResearch.WordTrace tailWord_243721 prefixEnd_243721 111240905417374377037025 := by
  unfold tailWord_243721
  simp only [CollatzResearch.WordTrace]
  refine ⟨8889235150047916078035017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5926156766698610718690011 8889235150047916078035017)
  ·
    refine ⟨6666926362535937058526263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8889235150047916078035017 6666926362535937058526263)
    ·
      refine ⟨10000389543803905587789395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6666926362535937058526263 10000389543803905587789395)
      ·
        refine ⟨15000584315705858381684093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10000389543803905587789395 15000584315705858381684093)
        ·
          refine ⟨5625219118389696893131535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15000584315705858381684093 5625219118389696893131535)
          ·
            refine ⟨8437828677584545339697303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5625219118389696893131535 8437828677584545339697303)
            ·
              refine ⟨12656743016376818009545955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8437828677584545339697303 12656743016376818009545955)
              ·
                refine ⟨18985114524565227014318933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12656743016376818009545955 18985114524565227014318933)
                ·
                  refine ⟨111240905417374377037025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 18985114524565227014318933 111240905417374377037025)
                  ·
                    rfl

theorem cell20_243721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 9].length) (baseStart_243721 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_243721 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_243721 prefixEnd_243721 := by exact prefixLift 243721
  have htrace : WordTrace (prefixWord ++ tailWord_243721) baseStart_243721 baseEnd_243721 := by
    simpa [prefixWord, tailWord_243721, baseEnd_243721] using wordTrace_append hprefix tailTrace_243721
  have hstable : (prefixWord ++ tailWord_243721).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243721).length < 2 ^ (prefixWord ++ tailWord_243721).sum := by decide
  have hdescent : baseEnd_243721 < baseStart_243721 := by decide
  rcases family_descends (prefixWord ++ tailWord_243721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243741 : List Nat := [1, 4, 2, 2, 2, 1, 1, 5, 2]
def baseStart_243741 : Nat := 118140960795 + 243741 * 2 ^ 59
def prefixEnd_243741 : Nat := 4983230072969 + 3 ^ 40 * 243741 * 2
def baseEnd_243741 : Nat := 111250033962343196370277

theorem tailTrace_243741 : CollatzResearch.WordTrace tailWord_243741 prefixEnd_243741 111250033962343196370277 := by
  unfold tailWord_243741
  simp only [CollatzResearch.WordTrace]
  refine ⟨8889964609975459493763077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5926643073316972995842051 8889964609975459493763077)
  ·
    refine ⟨1666868364370398655080577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8889964609975459493763077 1666868364370398655080577)
    ·
      refine ⟨1250151273277798991310433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1666868364370398655080577 1250151273277798991310433)
      ·
        refine ⟨937613454958349243482825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1250151273277798991310433 937613454958349243482825)
        ·
          refine ⟨703210091218761932612119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 937613454958349243482825 703210091218761932612119)
          ·
            refine ⟨1054815136828142898918179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 703210091218761932612119 1054815136828142898918179)
            ·
              refine ⟨1582222705242214348377269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1054815136828142898918179 1582222705242214348377269)
              ·
                refine ⟨148333378616457595160369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1582222705242214348377269 148333378616457595160369)
                ·
                  refine ⟨111250033962343196370277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 148333378616457595160369 111250033962343196370277)
                  ·
                    rfl

theorem cell20_243741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 5, 2].length) (baseStart_243741 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_243741 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_243741 prefixEnd_243741 := by exact prefixLift 243741
  have htrace : WordTrace (prefixWord ++ tailWord_243741) baseStart_243741 baseEnd_243741 := by
    simpa [prefixWord, tailWord_243741, baseEnd_243741] using wordTrace_append hprefix tailTrace_243741
  have hstable : (prefixWord ++ tailWord_243741).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243741).length < 2 ^ (prefixWord ++ tailWord_243741).sum := by decide
  have hdescent : baseEnd_243741 < baseStart_243741 := by decide
  rcases family_descends (prefixWord ++ tailWord_243741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243751 : List Nat := [1, 1, 7, 1, 2, 2, 1, 2, 3]
def baseStart_243751 : Nat := 118140960795 + 243751 * 2 ^ 59
def prefixEnd_243751 : Nat := 4983230072969 + 3 ^ 40 * 243751 * 2
def baseEnd_243751 : Nat := 111254598234827606036903

theorem tailTrace_243751 : CollatzResearch.WordTrace tailWord_243751 prefixEnd_243751 111254598234827606036903 := by
  unfold tailWord_243751
  simp only [CollatzResearch.WordTrace]
  refine ⟨8890329339939231201627107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5926886226626154134418071 8890329339939231201627107)
  ·
    refine ⟨13335494009908846802440661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8890329339939231201627107 13335494009908846802440661)
    ·
      refine ⟨312550640857238596932203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 13335494009908846802440661 312550640857238596932203)
      ·
        refine ⟨468825961285857895398305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312550640857238596932203 468825961285857895398305)
        ·
          refine ⟨351619470964393421548729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 468825961285857895398305 351619470964393421548729)
          ·
            refine ⟨263714603223295066161547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 351619470964393421548729 263714603223295066161547)
            ·
              refine ⟨395571904834942599242321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263714603223295066161547 395571904834942599242321)
              ·
                refine ⟨296678928626206949431741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 395571904834942599242321 296678928626206949431741)
                ·
                  refine ⟨111254598234827606036903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 296678928626206949431741 111254598234827606036903)
                  ·
                    rfl

theorem cell20_243751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 2, 3].length) (baseStart_243751 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_243751 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_243751 prefixEnd_243751 := by exact prefixLift 243751
  have htrace : WordTrace (prefixWord ++ tailWord_243751) baseStart_243751 baseEnd_243751 := by
    simpa [prefixWord, tailWord_243751, baseEnd_243751] using wordTrace_append hprefix tailTrace_243751
  have hstable : (prefixWord ++ tailWord_243751).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243751).length < 2 ^ (prefixWord ++ tailWord_243751).sum := by decide
  have hdescent : baseEnd_243751 < baseStart_243751 := by decide
  rcases family_descends (prefixWord ++ tailWord_243751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243762 : List Nat := [3, 2, 1, 1, 2, 4, 2, 1, 4]
def baseStart_243762 : Nat := 118140960795 + 243762 * 2 ^ 59
def prefixEnd_243762 : Nat := 4983230072969 + 3 ^ 40 * 243762 * 2
def baseEnd_243762 : Nat := 111259618934560456670191

theorem tailTrace_243762 : CollatzResearch.WordTrace tailWord_243762 prefixEnd_243762 111259618934560456670191 := by
  unfold tailWord_243762
  simp only [CollatzResearch.WordTrace]
  refine ⟨2222682635724845020069385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5927153695266253386851693 2222682635724845020069385)
  ·
    refine ⟨1667011976793633765052039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2222682635724845020069385 1667011976793633765052039)
    ·
      refine ⟨2500517965190450647578059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1667011976793633765052039 2500517965190450647578059)
      ·
        refine ⟨3750776947785675971367089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2500517965190450647578059 3750776947785675971367089)
        ·
          refine ⟨2813082710839256978525317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3750776947785675971367089 2813082710839256978525317)
          ·
            refine ⟨527453008282360683473497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2813082710839256978525317 527453008282360683473497)
            ·
              refine ⟨395589756211770512605123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 527453008282360683473497 395589756211770512605123)
              ·
                refine ⟨593384634317655768907685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 395589756211770512605123 593384634317655768907685)
                ·
                  refine ⟨111259618934560456670191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 593384634317655768907685 111259618934560456670191)
                  ·
                    rfl

theorem cell20_243762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_243762 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_243762 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_243762 prefixEnd_243762 := by exact prefixLift 243762
  have htrace : WordTrace (prefixWord ++ tailWord_243762) baseStart_243762 baseEnd_243762 := by
    simpa [prefixWord, tailWord_243762, baseEnd_243762] using wordTrace_append hprefix tailTrace_243762
  have hstable : (prefixWord ++ tailWord_243762).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243762).length < 2 ^ (prefixWord ++ tailWord_243762).sum := by decide
  have hdescent : baseEnd_243762 < baseStart_243762 := by decide
  rcases family_descends (prefixWord ++ tailWord_243762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243783 : List Nat := [1, 1, 4, 1, 3, 1, 1, 4, 4]
def baseStart_243783 : Nat := 118140960795 + 243783 * 2 ^ 59
def prefixEnd_243783 : Nat := 4983230072969 + 3 ^ 40 * 243783 * 2
def baseEnd_243783 : Nat := 111269203906777716970105

theorem tailTrace_243783 : CollatzResearch.WordTrace tailWord_243783 prefixEnd_243783 111269203906777716970105 := by
  unfold tailWord_243783
  simp only [CollatzResearch.WordTrace]
  refine ⟨8891496475823300666792003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5927664317215533777861335 8891496475823300666792003)
  ·
    refine ⟨13337244713734951000188005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8891496475823300666792003 13337244713734951000188005)
    ·
      refine ⟨2500733383825303312535251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13337244713734951000188005 2500733383825303312535251)
      ·
        refine ⟨3751100075737954968802877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2500733383825303312535251 3751100075737954968802877)
        ·
          refine ⟨1406662528401733113301079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3751100075737954968802877 1406662528401733113301079)
          ·
            refine ⟨2109993792602599669951619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1406662528401733113301079 2109993792602599669951619)
            ·
              refine ⟨3164990688903899504927429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2109993792602599669951619 3164990688903899504927429)
              ·
                refine ⟨593435754169481157173893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3164990688903899504927429 593435754169481157173893)
                ·
                  refine ⟨111269203906777716970105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 593435754169481157173893 111269203906777716970105)
                  ·
                    rfl

theorem cell20_243783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 4, 4].length) (baseStart_243783 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_243783 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_243783 prefixEnd_243783 := by exact prefixLift 243783
  have htrace : WordTrace (prefixWord ++ tailWord_243783) baseStart_243783 baseEnd_243783 := by
    simpa [prefixWord, tailWord_243783, baseEnd_243783] using wordTrace_append hprefix tailTrace_243783
  have hstable : (prefixWord ++ tailWord_243783).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243783).length < 2 ^ (prefixWord ++ tailWord_243783).sum := by decide
  have hdescent : baseEnd_243783 < baseStart_243783 := by decide
  rcases family_descends (prefixWord ++ tailWord_243783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243817 : List Nat := [1, 2, 1, 1, 1, 5, 5, 2, 2]
def baseStart_243817 : Nat := 118140960795 + 243817 * 2 ^ 59
def prefixEnd_243817 : Nat := 4983230072969 + 3 ^ 40 * 243817 * 2
def baseEnd_243817 : Nat := 111284722433224709836633

theorem tailTrace_243817 : CollatzResearch.WordTrace tailWord_243817 prefixEnd_243817 111284722433224709836633 := by
  unfold tailWord_243817
  simp only [CollatzResearch.WordTrace]
  refine ⟨8892736557700124473529705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5928491038466749649019803 8892736557700124473529705)
  ·
    refine ⟨6669552418275093355147279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8892736557700124473529705 6669552418275093355147279)
    ·
      refine ⟨10004328627412640032720919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6669552418275093355147279 10004328627412640032720919)
      ·
        refine ⟨15006492941118960049081379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10004328627412640032720919 15006492941118960049081379)
        ·
          refine ⟨22509739411678440073622069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15006492941118960049081379 22509739411678440073622069)
          ·
            refine ⟨2110288069844853756902069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22509739411678440073622069 2110288069844853756902069)
            ·
              refine ⟨197839506547955039709569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2110288069844853756902069 197839506547955039709569)
              ·
                refine ⟨148379629910966279782177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 197839506547955039709569 148379629910966279782177)
                ·
                  refine ⟨111284722433224709836633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 148379629910966279782177 111284722433224709836633)
                  ·
                    rfl

theorem cell20_243817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 5, 2, 2].length) (baseStart_243817 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_243817 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_243817 prefixEnd_243817 := by exact prefixLift 243817
  have htrace : WordTrace (prefixWord ++ tailWord_243817) baseStart_243817 baseEnd_243817 := by
    simpa [prefixWord, tailWord_243817, baseEnd_243817] using wordTrace_append hprefix tailTrace_243817
  have hstable : (prefixWord ++ tailWord_243817).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243817).length < 2 ^ (prefixWord ++ tailWord_243817).sum := by decide
  have hdescent : baseEnd_243817 < baseStart_243817 := by decide
  rcases family_descends (prefixWord ++ tailWord_243817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243831 : List Nat := [1, 1, 3, 1, 1, 5, 4, 1, 3]
def baseStart_243831 : Nat := 118140960795 + 243831 * 2 ^ 59
def prefixEnd_243831 : Nat := 4983230072969 + 3 ^ 40 * 243831 * 2
def baseEnd_243831 : Nat := 111291112414702883369909

theorem tailTrace_243831 : CollatzResearch.WordTrace tailWord_243831 prefixEnd_243831 111291112414702883369909 := by
  unfold tailWord_243831
  simp only [CollatzResearch.WordTrace]
  refine ⟨8893247179649404864539347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5928831453099603243026231 8893247179649404864539347)
  ·
    refine ⟨13339870769474107296809021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8893247179649404864539347 13339870769474107296809021)
    ·
      refine ⟨5002451538552790236303383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13339870769474107296809021 5002451538552790236303383)
      ·
        refine ⟨7503677307829185354455075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5002451538552790236303383 7503677307829185354455075)
        ·
          refine ⟨11255515961743778031682613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7503677307829185354455075 11255515961743778031682613)
          ·
            refine ⟨1055204621413479190470245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11255515961743778031682613 1055204621413479190470245)
            ·
              refine ⟨197850866515027348213171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1055204621413479190470245 197850866515027348213171)
              ·
                refine ⟨296776299772541022319757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197850866515027348213171 296776299772541022319757)
                ·
                  refine ⟨111291112414702883369909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 296776299772541022319757 111291112414702883369909)
                  ·
                    rfl

theorem cell20_243831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 4, 1, 3].length) (baseStart_243831 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_243831 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_243831 prefixEnd_243831 := by exact prefixLift 243831
  have htrace : WordTrace (prefixWord ++ tailWord_243831) baseStart_243831 baseEnd_243831 := by
    simpa [prefixWord, tailWord_243831, baseEnd_243831] using wordTrace_append hprefix tailTrace_243831
  have hstable : (prefixWord ++ tailWord_243831).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243831).length < 2 ^ (prefixWord ++ tailWord_243831).sum := by decide
  have hdescent : baseEnd_243831 < baseStart_243831 := by decide
  rcases family_descends (prefixWord ++ tailWord_243831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243866 : List Nat := [3, 1, 1, 5, 10]
def baseStart_243866 : Nat := 118140960795 + 243866 * 2 ^ 59
def prefixEnd_243866 : Nat := 4983230072969 + 3 ^ 40 * 243866 * 2
def baseEnd_243866 : Nat := 1374161572449361940779

theorem tailTrace_243866 : CollatzResearch.WordTrace tailWord_243866 prefixEnd_243866 1374161572449361940779 := by
  unfold tailWord_243866
  simp only [CollatzResearch.WordTrace]
  refine ⟨2223630933630651460515863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5929682489681737228042301 2223630933630651460515863)
  ·
    refine ⟨3335446400445977190773795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2223630933630651460515863 3335446400445977190773795)
    ·
      refine ⟨5003169600668965786160693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3335446400445977190773795 5003169600668965786160693)
      ·
        refine ⟨469047150062715542452565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5003169600668965786160693 469047150062715542452565)
        ·
          refine ⟨1374161572449361940779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 469047150062715542452565 1374161572449361940779)
          ·
            rfl

theorem cell20_243866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 10].length) (baseStart_243866 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_243866 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_243866 prefixEnd_243866 := by exact prefixLift 243866
  have htrace : WordTrace (prefixWord ++ tailWord_243866) baseStart_243866 baseEnd_243866 := by
    simpa [prefixWord, tailWord_243866, baseEnd_243866] using wordTrace_append hprefix tailTrace_243866
  have hstable : (prefixWord ++ tailWord_243866).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243866).length < 2 ^ (prefixWord ++ tailWord_243866).sum := by decide
  have hdescent : baseEnd_243866 < baseStart_243866 := by decide
  rcases family_descends (prefixWord ++ tailWord_243866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243869 : List Nat := [1, 4, 2, 1, 1, 4, 2, 2, 3]
def baseStart_243869 : Nat := 118140960795 + 243869 * 2 ^ 59
def prefixEnd_243869 : Nat := 4983230072969 + 3 ^ 40 * 243869 * 2
def baseEnd_243869 : Nat := 111308456650143640103087

theorem tailTrace_243869 : CollatzResearch.WordTrace tailWord_243869 prefixEnd_243869 111308456650143640103087 := by
  unfold tailWord_243869
  simp only [CollatzResearch.WordTrace]
  refine ⟨8894633153511737354422661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5929755435674491569615107 8894633153511737354422661)
  ·
    refine ⟨1667743716283450753954249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8894633153511737354422661 1667743716283450753954249)
    ·
      refine ⟨1250807787212588065465687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1667743716283450753954249 1250807787212588065465687)
      ·
        refine ⟨1876211680818882098198531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1250807787212588065465687 1876211680818882098198531)
        ·
          refine ⟨2814317521228323147297797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1876211680818882098198531 2814317521228323147297797)
          ·
            refine ⟨527684535230310590118337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2814317521228323147297797 527684535230310590118337)
            ·
              refine ⟨395763401422732942588753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 527684535230310590118337 395763401422732942588753)
              ·
                refine ⟨296822551067049706941565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 395763401422732942588753 296822551067049706941565)
                ·
                  refine ⟨111308456650143640103087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 296822551067049706941565 111308456650143640103087)
                  ·
                    rfl

theorem cell20_243869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 2, 3].length) (baseStart_243869 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_243869 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_243869 prefixEnd_243869 := by exact prefixLift 243869
  have htrace : WordTrace (prefixWord ++ tailWord_243869) baseStart_243869 baseEnd_243869 := by
    simpa [prefixWord, tailWord_243869, baseEnd_243869] using wordTrace_append hprefix tailTrace_243869
  have hstable : (prefixWord ++ tailWord_243869).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243869).length < 2 ^ (prefixWord ++ tailWord_243869).sum := by decide
  have hdescent : baseEnd_243869 < baseStart_243869 := by decide
  rcases family_descends (prefixWord ++ tailWord_243869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243872 : List Nat := [2, 1, 1, 4, 2, 4, 2, 2, 2]
def baseStart_243872 : Nat := 118140960795 + 243872 * 2 ^ 59
def prefixEnd_243872 : Nat := 4983230072969 + 3 ^ 40 * 243872 * 2
def baseEnd_243872 : Nat := 111309825931888963003075

theorem tailTrace_243872 : CollatzResearch.WordTrace tailWord_243872 prefixEnd_243872 111309825931888963003075 := by
  unfold tailWord_243872
  simp only [CollatzResearch.WordTrace]
  refine ⟨4447371286250434433390935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5929828381667245911187913 4447371286250434433390935)
  ·
    refine ⟨6671056929375651650086403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4447371286250434433390935 6671056929375651650086403)
    ·
      refine ⟨10006585394063477475129605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6671056929375651650086403 10006585394063477475129605)
      ·
        refine ⟨1876234761386902026586801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10006585394063477475129605 1876234761386902026586801)
        ·
          refine ⟨1407176071040176519940101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1876234761386902026586801 1407176071040176519940101)
          ·
            refine ⟨263845513320033097488769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1407176071040176519940101 263845513320033097488769)
            ·
              refine ⟨197884134990024823116577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 263845513320033097488769 197884134990024823116577)
              ·
                refine ⟨148413101242518617337433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 197884134990024823116577 148413101242518617337433)
                ·
                  refine ⟨111309825931888963003075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 148413101242518617337433 111309825931888963003075)
                  ·
                    rfl

theorem cell20_243872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 2, 2, 2].length) (baseStart_243872 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_243872 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_243872 prefixEnd_243872 := by exact prefixLift 243872
  have htrace : WordTrace (prefixWord ++ tailWord_243872) baseStart_243872 baseEnd_243872 := by
    simpa [prefixWord, tailWord_243872, baseEnd_243872] using wordTrace_append hprefix tailTrace_243872
  have hstable : (prefixWord ++ tailWord_243872).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243872).length < 2 ^ (prefixWord ++ tailWord_243872).sum := by decide
  have hdescent : baseEnd_243872 < baseStart_243872 := by decide
  rcases family_descends (prefixWord ++ tailWord_243872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243879 : List Nat := [1, 1, 6, 2, 3, 1, 1, 5]
def baseStart_243879 : Nat := 118140960795 + 243879 * 2 ^ 59
def prefixEnd_243879 : Nat := 4983230072969 + 3 ^ 40 * 243879 * 2
def baseEnd_243879 : Nat := 37104340307542683256571

theorem tailTrace_243879 : CollatzResearch.WordTrace tailWord_243879 prefixEnd_243879 37104340307542683256571 := by
  unfold tailWord_243879
  simp only [CollatzResearch.WordTrace]
  refine ⟨8894997883475509062286691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5929998588983672708191127 8894997883475509062286691)
  ·
    refine ⟨13342496825213263593430037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8894997883475509062286691 13342496825213263593430037)
    ·
      refine ⟨625429538681871730942033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 13342496825213263593430037 625429538681871730942033)
      ·
        refine ⟨469072154011403798206525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 625429538681871730942033 469072154011403798206525)
        ·
          refine ⟨175902057754276424327447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 469072154011403798206525 175902057754276424327447)
          ·
            refine ⟨263853086631414636491171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175902057754276424327447 263853086631414636491171)
            ·
              refine ⟨395779629947121954736757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263853086631414636491171 395779629947121954736757)
              ·
                refine ⟨37104340307542683256571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 395779629947121954736757 37104340307542683256571)
                ·
                  rfl

theorem cell20_243879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 5].length) (baseStart_243879 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_243879 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_243879 prefixEnd_243879 := by exact prefixLift 243879
  have htrace : WordTrace (prefixWord ++ tailWord_243879) baseStart_243879 baseEnd_243879 := by
    simpa [prefixWord, tailWord_243879, baseEnd_243879] using wordTrace_append hprefix tailTrace_243879
  have hstable : (prefixWord ++ tailWord_243879).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243879).length < 2 ^ (prefixWord ++ tailWord_243879).sum := by decide
  have hdescent : baseEnd_243879 < baseStart_243879 := by decide
  rcases family_descends (prefixWord ++ tailWord_243879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243890 : List Nat := [3, 2, 1, 1, 1, 3, 1, 5, 3]
def baseStart_243890 : Nat := 118140960795 + 243890 * 2 ^ 59
def prefixEnd_243890 : Nat := 4983230072969 + 3 ^ 40 * 243890 * 2
def baseEnd_243890 : Nat := 111318041622360900403001

theorem tailTrace_243890 : CollatzResearch.WordTrace tailWord_243890 prefixEnd_243890 111318041622360900403001 := by
  unfold tailWord_243890
  simp only [CollatzResearch.WordTrace]
  refine ⟨2223849771608914485234281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5930266057623771960624749 2223849771608914485234281)
  ·
    refine ⟨1667887328706685863925711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2223849771608914485234281 1667887328706685863925711)
    ·
      refine ⟨2501830993060028795888567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1667887328706685863925711 2501830993060028795888567)
      ·
        refine ⟨3752746489590043193832851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2501830993060028795888567 3752746489590043193832851)
        ·
          refine ⟨5629119734385064790749277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3752746489590043193832851 5629119734385064790749277)
          ·
            refine ⟨2110919900394399296530979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5629119734385064790749277 2110919900394399296530979)
            ·
              refine ⟨3166379850591598944796469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2110919900394399296530979 3166379850591598944796469)
              ·
                refine ⟨296848110992962401074669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3166379850591598944796469 296848110992962401074669)
                ·
                  refine ⟨111318041622360900403001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 296848110992962401074669 111318041622360900403001)
                  ·
                    rfl

theorem cell20_243890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 5, 3].length) (baseStart_243890 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_243890 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_243890 prefixEnd_243890 := by exact prefixLift 243890
  have htrace : WordTrace (prefixWord ++ tailWord_243890) baseStart_243890 baseEnd_243890 := by
    simpa [prefixWord, tailWord_243890, baseEnd_243890] using wordTrace_append hprefix tailTrace_243890
  have hstable : (prefixWord ++ tailWord_243890).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243890).length < 2 ^ (prefixWord ++ tailWord_243890).sum := by decide
  have hdescent : baseEnd_243890 < baseStart_243890 := by decide
  rcases family_descends (prefixWord ++ tailWord_243890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243893 : List Nat := [1, 3, 3, 4, 1, 1, 1, 2, 4]
def baseStart_243893 : Nat := 118140960795 + 243893 * 2 ^ 59
def prefixEnd_243893 : Nat := 4983230072969 + 3 ^ 40 * 243893 * 2
def baseEnd_243893 : Nat := 111319410904106223302989

theorem tailTrace_243893 : CollatzResearch.WordTrace tailWord_243893 prefixEnd_243893 111319410904106223302989 := by
  unfold tailWord_243893
  simp only [CollatzResearch.WordTrace]
  refine ⟨8895508505424789453296333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5930339003616526302197555 8895508505424789453296333)
  ·
    refine ⟨3335815689534296044986125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8895508505424789453296333 3335815689534296044986125)
    ·
      refine ⟨1250930883575361016869797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3335815689534296044986125 1250930883575361016869797)
      ·
        refine ⟨234549540670380190663087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1250930883575361016869797 234549540670380190663087)
        ·
          refine ⟨351824311005570285994631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234549540670380190663087 351824311005570285994631)
          ·
            refine ⟨527736466508355428991947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 351824311005570285994631 527736466508355428991947)
            ·
              refine ⟨791604699762533143487921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 527736466508355428991947 791604699762533143487921)
              ·
                refine ⟨593703524821899857615941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 791604699762533143487921 593703524821899857615941)
                ·
                  refine ⟨111319410904106223302989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 593703524821899857615941 111319410904106223302989)
                  ·
                    rfl

theorem cell20_243893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 2, 4].length) (baseStart_243893 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_243893 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_243893 prefixEnd_243893 := by exact prefixLift 243893
  have htrace : WordTrace (prefixWord ++ tailWord_243893) baseStart_243893 baseEnd_243893 := by
    simpa [prefixWord, tailWord_243893, baseEnd_243893] using wordTrace_append hprefix tailTrace_243893
  have hstable : (prefixWord ++ tailWord_243893).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243893).length < 2 ^ (prefixWord ++ tailWord_243893).sum := by decide
  have hdescent : baseEnd_243893 < baseStart_243893 := by decide
  rcases family_descends (prefixWord ++ tailWord_243893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243897 : List Nat := [1, 2, 1, 4, 1, 2, 3, 2, 4]
def baseStart_243897 : Nat := 118140960795 + 243897 * 2 ^ 59
def prefixEnd_243897 : Nat := 4983230072969 + 3 ^ 40 * 243897 * 2
def baseEnd_243897 : Nat := 111321236613099987169639

theorem tailTrace_243897 : CollatzResearch.WordTrace tailWord_243897 prefixEnd_243897 111321236613099987169639 := by
  unfold tailWord_243897
  simp only [CollatzResearch.WordTrace]
  refine ⟨8895654397410298136441945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5930436264940198757627963 8895654397410298136441945)
  ·
    refine ⟨6671740798057723602331459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8895654397410298136441945 6671740798057723602331459)
    ·
      refine ⟨10007611197086585403497189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6671740798057723602331459 10007611197086585403497189)
      ·
        refine ⟨1876427099453734763155723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10007611197086585403497189 1876427099453734763155723)
        ·
          refine ⟨2814640649180602144733585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1876427099453734763155723 2814640649180602144733585)
          ·
            refine ⟨2110980486885451608550189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2814640649180602144733585 2110980486885451608550189)
            ·
              refine ⟨791617682582044353206321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2110980486885451608550189 791617682582044353206321)
              ·
                refine ⟨593713261936533264904741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 791617682582044353206321 593713261936533264904741)
                ·
                  refine ⟨111321236613099987169639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 593713261936533264904741 111321236613099987169639)
                  ·
                    rfl

theorem cell20_243897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 2, 4].length) (baseStart_243897 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_243897 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_243897 prefixEnd_243897 := by exact prefixLift 243897
  have htrace : WordTrace (prefixWord ++ tailWord_243897) baseStart_243897 baseEnd_243897 := by
    simpa [prefixWord, tailWord_243897, baseEnd_243897] using wordTrace_append hprefix tailTrace_243897
  have hstable : (prefixWord ++ tailWord_243897).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243897).length < 2 ^ (prefixWord ++ tailWord_243897).sum := by decide
  have hdescent : baseEnd_243897 < baseStart_243897 := by decide
  rcases family_descends (prefixWord ++ tailWord_243897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243900 : List Nat := [2, 2, 2, 3, 3, 1, 3, 4]
def baseStart_243900 : Nat := 118140960795 + 243900 * 2 ^ 59
def prefixEnd_243900 : Nat := 4983230072969 + 3 ^ 40 * 243900 * 2
def baseEnd_243900 : Nat := 37107535298281770023209

theorem tailTrace_243900 : CollatzResearch.WordTrace tailWord_243900 prefixEnd_243900 37107535298281770023209 := by
  unfold tailWord_243900
  simp only [CollatzResearch.WordTrace]
  refine ⟨4447881908199714824400577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5930509210932953099200769 4447881908199714824400577)
  ·
    refine ⟨3335911431149786118300433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4447881908199714824400577 3335911431149786118300433)
    ·
      refine ⟨2501933573362339588725325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3335911431149786118300433 2501933573362339588725325)
      ·
        refine ⟨938225090010877345771997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2501933573362339588725325 938225090010877345771997)
        ·
          refine ⟨351834408754079004664499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 938225090010877345771997 351834408754079004664499)
          ·
            refine ⟨527751613131118506996749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 351834408754079004664499 527751613131118506996749)
            ·
              refine ⟨197906854924169440123781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 527751613131118506996749 197906854924169440123781)
              ·
                refine ⟨37107535298281770023209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 197906854924169440123781 37107535298281770023209)
                ·
                  rfl

theorem cell20_243900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 3, 4].length) (baseStart_243900 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_243900 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_243900 prefixEnd_243900 := by exact prefixLift 243900
  have htrace : WordTrace (prefixWord ++ tailWord_243900) baseStart_243900 baseEnd_243900 := by
    simpa [prefixWord, tailWord_243900, baseEnd_243900] using wordTrace_append hprefix tailTrace_243900
  have hstable : (prefixWord ++ tailWord_243900).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243900).length < 2 ^ (prefixWord ++ tailWord_243900).sum := by decide
  have hdescent : baseEnd_243900 < baseStart_243900 := by decide
  rcases family_descends (prefixWord ++ tailWord_243900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243928 : List Nat := [2, 1, 2, 2, 4, 2, 1, 1, 5]
def baseStart_243928 : Nat := 118140960795 + 243928 * 2 ^ 59
def prefixEnd_243928 : Nat := 4983230072969 + 3 ^ 40 * 243928 * 2
def baseEnd_243928 : Nat := 111335385857801657136179

theorem tailTrace_243928 : CollatzResearch.WordTrace tailWord_243928 prefixEnd_243928 111335385857801657136179 := by
  unfold tailWord_243928
  simp only [CollatzResearch.WordTrace]
  refine ⟨4448392530148995215410219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5931190040198660287213625 4448392530148995215410219)
  ·
    refine ⟨6672588795223492823115329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4448392530148995215410219 6672588795223492823115329)
    ·
      refine ⟨5004441596417619617336497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6672588795223492823115329 5004441596417619617336497)
      ·
        refine ⟨3753331197313214713002373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5004441596417619617336497 3753331197313214713002373)
        ·
          refine ⟨703749599496227758687945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3753331197313214713002373 703749599496227758687945)
          ·
            refine ⟨527812199622170819015959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 703749599496227758687945 527812199622170819015959)
            ·
              refine ⟨791718299433256228523939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 527812199622170819015959 791718299433256228523939)
              ·
                refine ⟨1187577449149884342785909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 791718299433256228523939 1187577449149884342785909)
                ·
                  refine ⟨111335385857801657136179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1187577449149884342785909 111335385857801657136179)
                  ·
                    rfl

theorem cell20_243928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 1, 5].length) (baseStart_243928 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_243928 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_243928 prefixEnd_243928 := by exact prefixLift 243928
  have htrace : WordTrace (prefixWord ++ tailWord_243928) baseStart_243928 baseEnd_243928 := by
    simpa [prefixWord, tailWord_243928, baseEnd_243928] using wordTrace_append hprefix tailTrace_243928
  have hstable : (prefixWord ++ tailWord_243928).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243928).length < 2 ^ (prefixWord ++ tailWord_243928).sum := by decide
  have hdescent : baseEnd_243928 < baseStart_243928 := by decide
  rcases family_descends (prefixWord ++ tailWord_243928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_243966 : List Nat := [4, 2, 2, 1, 1, 1, 1, 1, 7]
def baseStart_243966 : Nat := 118140960795 + 243966 * 2 ^ 59
def prefixEnd_243966 : Nat := 4983230072969 + 3 ^ 40 * 243966 * 2
def baseEnd_243966 : Nat := 111352730093242413869357

theorem tailTrace_243966 : CollatzResearch.WordTrace tailWord_243966 prefixEnd_243966 111352730093242413869357 := by
  unfold tailWord_243966
  simp only [CollatzResearch.WordTrace]
  refine ⟨1112271379270040365087969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5932114022773548613802501 1112271379270040365087969)
  ·
    refine ⟨834203534452530273815977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1112271379270040365087969 834203534452530273815977)
    ·
      refine ⟨625652650839397705361983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 834203534452530273815977 625652650839397705361983)
      ·
        refine ⟨938478976259096558042975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 625652650839397705361983 938478976259096558042975)
        ·
          refine ⟨1407718464388644837064463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 938478976259096558042975 1407718464388644837064463)
          ·
            refine ⟨2111577696582967255596695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1407718464388644837064463 2111577696582967255596695)
            ·
              refine ⟨3167366544874450883395043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2111577696582967255596695 3167366544874450883395043)
              ·
                refine ⟨4751049817311676325092565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3167366544874450883395043 4751049817311676325092565)
                ·
                  refine ⟨111352730093242413869357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4751049817311676325092565 111352730093242413869357)
                  ·
                    rfl

theorem cell20_243966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_243966 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_243966 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_243966 prefixEnd_243966 := by exact prefixLift 243966
  have htrace : WordTrace (prefixWord ++ tailWord_243966) baseStart_243966 baseEnd_243966 := by
    simpa [prefixWord, tailWord_243966, baseEnd_243966] using wordTrace_append hprefix tailTrace_243966
  have hstable : (prefixWord ++ tailWord_243966).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_243966).length < 2 ^ (prefixWord ++ tailWord_243966).sum := by decide
  have hdescent : baseEnd_243966 < baseStart_243966 := by decide
  rcases family_descends (prefixWord ++ tailWord_243966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244000 : List Nat := [2, 1, 1, 5, 2, 3, 2, 1, 3]
def baseStart_244000 : Nat := 118140960795 + 244000 * 2 ^ 59
def prefixEnd_244000 : Nat := 4983230072969 + 3 ^ 40 * 244000 * 2
def baseEnd_244000 : Nat := 111368248619689406735885

theorem tailTrace_244000 : CollatzResearch.WordTrace tailWord_244000 prefixEnd_244000 111368248619689406735885 := by
  unfold tailWord_244000
  simp only [CollatzResearch.WordTrace]
  refine ⟨4449705558018573363720727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5932940744024764484960969 4449705558018573363720727)
  ·
    refine ⟨6674558337027860045581091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4449705558018573363720727 6674558337027860045581091)
    ·
      refine ⟨10011837505541790068371637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6674558337027860045581091 10011837505541790068371637)
      ·
        refine ⟨938609766144542818909841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10011837505541790068371637 938609766144542818909841)
        ·
          refine ⟨703957324608407114182381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 938609766144542818909841 703957324608407114182381)
          ·
            refine ⟨263983996728152667818393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 703957324608407114182381 263983996728152667818393)
            ·
              refine ⟨197987997546114500863795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 263983996728152667818393 197987997546114500863795)
              ·
                refine ⟨296981996319171751295693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197987997546114500863795 296981996319171751295693)
                ·
                  refine ⟨111368248619689406735885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 296981996319171751295693 111368248619689406735885)
                  ·
                    rfl

theorem cell20_244000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 2, 1, 3].length) (baseStart_244000 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_244000 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_244000 prefixEnd_244000 := by exact prefixLift 244000
  have htrace : WordTrace (prefixWord ++ tailWord_244000) baseStart_244000 baseEnd_244000 := by
    simpa [prefixWord, tailWord_244000, baseEnd_244000] using wordTrace_append hprefix tailTrace_244000
  have hstable : (prefixWord ++ tailWord_244000).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244000).length < 2 ^ (prefixWord ++ tailWord_244000).sum := by decide
  have hdescent : baseEnd_244000 < baseStart_244000 := by decide
  rcases family_descends (prefixWord ++ tailWord_244000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244028 : List Nat := [2, 2, 2, 2, 1, 2, 2, 5, 2]
def baseStart_244028 : Nat := 118140960795 + 244028 * 2 ^ 59
def prefixEnd_244028 : Nat := 4983230072969 + 3 ^ 40 * 244028 * 2
def baseEnd_244028 : Nat := 111381028582645753802437

theorem tailTrace_244028 : CollatzResearch.WordTrace tailWord_244028 prefixEnd_244028 111381028582645753802437 := by
  unfold tailWord_244028
  simp only [CollatzResearch.WordTrace]
  refine ⟨4450216179967853754730369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5933621573290471672973825 4450216179967853754730369)
  ·
    refine ⟨3337662134975890316047777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4450216179967853754730369 3337662134975890316047777)
    ·
      refine ⟨2503246601231917737035833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3337662134975890316047777 2503246601231917737035833)
      ·
        refine ⟨1877434950923938302776875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2503246601231917737035833 1877434950923938302776875)
        ·
          refine ⟨2816152426385907454165313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1877434950923938302776875 2816152426385907454165313)
          ·
            refine ⟨2112114319789430590623985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2816152426385907454165313 2112114319789430590623985)
            ·
              refine ⟨1584085739842072942967989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2112114319789430590623985 1584085739842072942967989)
              ·
                refine ⟨148508038110194338403249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1584085739842072942967989 148508038110194338403249)
                ·
                  refine ⟨111381028582645753802437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 148508038110194338403249 111381028582645753802437)
                  ·
                    rfl

theorem cell20_244028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 5, 2].length) (baseStart_244028 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_244028 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_244028 prefixEnd_244028 := by exact prefixLift 244028
  have htrace : WordTrace (prefixWord ++ tailWord_244028) baseStart_244028 baseEnd_244028 := by
    simpa [prefixWord, tailWord_244028, baseEnd_244028] using wordTrace_append hprefix tailTrace_244028
  have hstable : (prefixWord ++ tailWord_244028).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244028).length < 2 ^ (prefixWord ++ tailWord_244028).sum := by decide
  have hdescent : baseEnd_244028 < baseStart_244028 := by decide
  rcases family_descends (prefixWord ++ tailWord_244028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244032 : List Nat := [2, 1, 1, 2, 2, 1, 2, 1, 8]
def baseStart_244032 : Nat := 118140960795 + 244032 * 2 ^ 59
def prefixEnd_244032 : Nat := 4983230072969 + 3 ^ 40 * 244032 * 2
def baseEnd_244032 : Nat := 111382854291639517669087

theorem tailTrace_244032 : CollatzResearch.WordTrace tailWord_244032 prefixEnd_244032 111382854291639517669087 := by
  unfold tailWord_244032
  simp only [CollatzResearch.WordTrace]
  refine ⟨4450289125960608096303175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5933718834614144128404233 4450289125960608096303175)
  ·
    refine ⟨6675433688940912144454763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4450289125960608096303175 6675433688940912144454763)
    ·
      refine ⟨10013150533411368216682145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6675433688940912144454763 10013150533411368216682145)
      ·
        refine ⟨7509862900058526162511609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10013150533411368216682145 7509862900058526162511609)
        ·
          refine ⟨5632397175043894621883707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7509862900058526162511609 5632397175043894621883707)
          ·
            refine ⟨8448595762565841932825561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5632397175043894621883707 8448595762565841932825561)
            ·
              refine ⟨6336446821924381449619171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8448595762565841932825561 6336446821924381449619171)
              ·
                refine ⟨9504670232886572174428757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6336446821924381449619171 9504670232886572174428757)
                ·
                  refine ⟨111382854291639517669087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9504670232886572174428757 111382854291639517669087)
                  ·
                    rfl

theorem cell20_244032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 8].length) (baseStart_244032 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_244032 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_244032 prefixEnd_244032 := by exact prefixLift 244032
  have htrace : WordTrace (prefixWord ++ tailWord_244032) baseStart_244032 baseEnd_244032 := by
    simpa [prefixWord, tailWord_244032, baseEnd_244032] using wordTrace_append hprefix tailTrace_244032
  have hstable : (prefixWord ++ tailWord_244032).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244032).length < 2 ^ (prefixWord ++ tailWord_244032).sum := by decide
  have hdescent : baseEnd_244032 < baseStart_244032 := by decide
  rcases family_descends (prefixWord ++ tailWord_244032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244066 : List Nat := [3, 3, 2, 1, 1, 3, 1, 2, 4]
def baseStart_244066 : Nat := 118140960795 + 244066 * 2 ^ 59
def prefixEnd_244066 : Nat := 4983230072969 + 3 ^ 40 * 244066 * 2
def baseEnd_244066 : Nat := 111398372818086510535615

theorem tailTrace_244066 : CollatzResearch.WordTrace tailWord_244066 prefixEnd_244066 111398372818086510535615 := by
  unfold tailWord_244066
  simp only [CollatzResearch.WordTrace]
  refine ⟨2225454583449509999836013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5934545555865359999562701 2225454583449509999836013)
  ·
    refine ⟨834545468793566249938505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2225454583449509999836013 834545468793566249938505)
    ·
      refine ⟨625909101595174687453879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 834545468793566249938505 625909101595174687453879)
      ·
        refine ⟨938863652392762031180819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 625909101595174687453879 938863652392762031180819)
        ·
          refine ⟨1408295478589143046771229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 938863652392762031180819 1408295478589143046771229)
          ·
            refine ⟨528110804470928642539211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1408295478589143046771229 528110804470928642539211)
            ·
              refine ⟨792166206706392963808817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 528110804470928642539211 792166206706392963808817)
              ·
                refine ⟨594124655029794722856613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 792166206706392963808817 594124655029794722856613)
                ·
                  refine ⟨111398372818086510535615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 594124655029794722856613 111398372818086510535615)
                  ·
                    rfl

theorem cell20_244066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_244066 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_244066 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_244066 prefixEnd_244066 := by exact prefixLift 244066
  have htrace : WordTrace (prefixWord ++ tailWord_244066) baseStart_244066 baseEnd_244066 := by
    simpa [prefixWord, tailWord_244066, baseEnd_244066] using wordTrace_append hprefix tailTrace_244066
  have hstable : (prefixWord ++ tailWord_244066).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244066).length < 2 ^ (prefixWord ++ tailWord_244066).sum := by decide
  have hdescent : baseEnd_244066 < baseStart_244066 := by decide
  rcases family_descends (prefixWord ++ tailWord_244066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244097 : List Nat := [1, 2, 4, 3, 1, 1, 3, 2, 3]
def baseStart_244097 : Nat := 118140960795 + 244097 * 2 ^ 59
def prefixEnd_244097 : Nat := 4983230072969 + 3 ^ 40 * 244097 * 2
def baseEnd_244097 : Nat := 111412522062788180502155

theorem tailTrace_244097 : CollatzResearch.WordTrace tailWord_244097 prefixEnd_244097 111412522062788180502155 := by
  unfold tailWord_244097
  simp only [CollatzResearch.WordTrace]
  refine ⟨8902948996685732293722545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5935299331123821529148363 8902948996685732293722545)
  ·
    refine ⟨6677211747514299220291909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8902948996685732293722545 6677211747514299220291909)
    ·
      refine ⟨1251977202658931103804733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6677211747514299220291909 1251977202658931103804733)
      ·
        refine ⟨469491450997099163926775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1251977202658931103804733 469491450997099163926775)
        ·
          refine ⟨704237176495648745890163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 469491450997099163926775 704237176495648745890163)
          ·
            refine ⟨1056355764743473118835245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 704237176495648745890163 1056355764743473118835245)
            ·
              refine ⟨396133411778802419563217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1056355764743473118835245 396133411778802419563217)
              ·
                refine ⟨297100058834101814672413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 396133411778802419563217 297100058834101814672413)
                ·
                  refine ⟨111412522062788180502155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 297100058834101814672413 111412522062788180502155)
                  ·
                    rfl

theorem cell20_244097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 2, 3].length) (baseStart_244097 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_244097 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_244097 prefixEnd_244097 := by exact prefixLift 244097
  have htrace : WordTrace (prefixWord ++ tailWord_244097) baseStart_244097 baseEnd_244097 := by
    simpa [prefixWord, tailWord_244097, baseEnd_244097] using wordTrace_append hprefix tailTrace_244097
  have hstable : (prefixWord ++ tailWord_244097).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244097).length < 2 ^ (prefixWord ++ tailWord_244097).sum := by decide
  have hdescent : baseEnd_244097 < baseStart_244097 := by decide
  rcases family_descends (prefixWord ++ tailWord_244097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244104 : List Nat := [2, 1, 3, 3, 1, 1, 1, 6, 2]
def baseStart_244104 : Nat := 118140960795 + 244104 * 2 ^ 59
def prefixEnd_244104 : Nat := 4983230072969 + 3 ^ 40 * 244104 * 2
def baseEnd_244104 : Nat := 111415717053527267268793

theorem tailTrace_244104 : CollatzResearch.WordTrace tailWord_244104 prefixEnd_244104 111415717053527267268793 := by
  unfold tailWord_244104
  simp only [CollatzResearch.WordTrace]
  refine ⟨4451602153830186244613683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5935469538440248326151577 4451602153830186244613683)
  ·
    refine ⟨6677403230745279366920525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4451602153830186244613683 6677403230745279366920525)
    ·
      refine ⟨2504026211529479762595197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6677403230745279366920525 2504026211529479762595197)
      ·
        refine ⟨939009829323554910973199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2504026211529479762595197 939009829323554910973199)
        ·
          refine ⟨1408514743985332366459799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 939009829323554910973199 1408514743985332366459799)
          ·
            refine ⟨2112772115977998549689699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1408514743985332366459799 2112772115977998549689699)
            ·
              refine ⟨3169158173966997824534549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2112772115977998549689699 3169158173966997824534549)
              ·
                refine ⟨148554289404703023025057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3169158173966997824534549 148554289404703023025057)
                ·
                  refine ⟨111415717053527267268793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 148554289404703023025057 111415717053527267268793)
                  ·
                    rfl

theorem cell20_244104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 6, 2].length) (baseStart_244104 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_244104 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_244104 prefixEnd_244104 := by exact prefixLift 244104
  have htrace : WordTrace (prefixWord ++ tailWord_244104) baseStart_244104 baseEnd_244104 := by
    simpa [prefixWord, tailWord_244104, baseEnd_244104] using wordTrace_append hprefix tailTrace_244104
  have hstable : (prefixWord ++ tailWord_244104).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244104).length < 2 ^ (prefixWord ++ tailWord_244104).sum := by decide
  have hdescent : baseEnd_244104 < baseStart_244104 := by decide
  rcases family_descends (prefixWord ++ tailWord_244104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244149 : List Nat := [1, 3, 3, 2, 3, 2, 6]
def baseStart_244149 : Nat := 118140960795 + 244149 * 2 ^ 59
def prefixEnd_244149 : Nat := 4983230072969 + 3 ^ 40 * 244149 * 2
def baseEnd_244149 : Nat := 12381806253300790085401

theorem tailTrace_244149 : CollatzResearch.WordTrace tailWord_244149 prefixEnd_244149 12381806253300790085401 := by
  unfold tailWord_244149
  simp only [CollatzResearch.WordTrace]
  refine ⟨8904845592497345174615501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5936563728331563449743667 8904845592497345174615501)
  ·
    refine ⟨3339317097186504440480813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8904845592497345174615501 3339317097186504440480813)
    ·
      refine ⟨1252243911444939165180305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3339317097186504440480813 1252243911444939165180305)
      ·
        refine ⟨939182933583704373885229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1252243911444939165180305 939182933583704373885229)
        ·
          refine ⟨352193600093889140206961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 939182933583704373885229 352193600093889140206961)
          ·
            refine ⟨264145200070416855155221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 352193600093889140206961 264145200070416855155221)
            ·
              refine ⟨12381806253300790085401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 264145200070416855155221 12381806253300790085401)
              ·
                rfl

theorem cell20_244149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 6].length) (baseStart_244149 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_244149 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_244149 prefixEnd_244149 := by exact prefixLift 244149
  have htrace : WordTrace (prefixWord ++ tailWord_244149) baseStart_244149 baseEnd_244149 := by
    simpa [prefixWord, tailWord_244149, baseEnd_244149] using wordTrace_append hprefix tailTrace_244149
  have hstable : (prefixWord ++ tailWord_244149).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244149).length < 2 ^ (prefixWord ++ tailWord_244149).sum := by decide
  have hdescent : baseEnd_244149 < baseStart_244149 := by decide
  rcases family_descends (prefixWord ++ tailWord_244149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244156 : List Nat := [2, 2, 2, 4, 1, 1, 2, 1, 5]
def baseStart_244156 : Nat := 118140960795 + 244156 * 2 ^ 59
def prefixEnd_244156 : Nat := 4983230072969 + 3 ^ 40 * 244156 * 2
def baseEnd_244156 : Nat := 111439451270446197535247

theorem tailTrace_244156 : CollatzResearch.WordTrace tailWord_244156 prefixEnd_244156 111439451270446197535247 := by
  unfold tailWord_244156
  simp only [CollatzResearch.WordTrace]
  refine ⟨4452550451735992685060161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5936733935647990246746881 4452550451735992685060161)
  ·
    refine ⟨3339412838801994513795121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4452550451735992685060161 3339412838801994513795121)
    ·
      refine ⟨2504559629101495885346341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3339412838801994513795121 2504559629101495885346341)
      ·
        refine ⟨469604930456530478502439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2504559629101495885346341 469604930456530478502439)
        ·
          refine ⟨704407395684795717753659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 469604930456530478502439 704407395684795717753659)
          ·
            refine ⟨1056611093527193576630489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 704407395684795717753659 1056611093527193576630489)
            ·
              refine ⟨792458320145395182472867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1056611093527193576630489 792458320145395182472867)
              ·
                refine ⟨1188687480218092773709301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 792458320145395182472867 1188687480218092773709301)
                ·
                  refine ⟨111439451270446197535247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1188687480218092773709301 111439451270446197535247)
                  ·
                    rfl

theorem cell20_244156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 1, 5].length) (baseStart_244156 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_244156 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_244156 prefixEnd_244156 := by exact prefixLift 244156
  have htrace : WordTrace (prefixWord ++ tailWord_244156) baseStart_244156 baseEnd_244156 := by
    simpa [prefixWord, tailWord_244156, baseEnd_244156] using wordTrace_append hprefix tailTrace_244156
  have hstable : (prefixWord ++ tailWord_244156).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244156).length < 2 ^ (prefixWord ++ tailWord_244156).sum := by decide
  have hdescent : baseEnd_244156 < baseStart_244156 := by decide
  rcases family_descends (prefixWord ++ tailWord_244156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244170 : List Nat := [3, 1, 2, 1, 2, 2, 4, 5]
def baseStart_244170 : Nat := 118140960795 + 244170 * 2 ^ 59
def prefixEnd_244170 : Nat := 4983230072969 + 3 ^ 40 * 244170 * 2
def baseEnd_244170 : Nat := 37148613750641457022841

theorem tailTrace_244170 : CollatzResearch.WordTrace tailWord_244170 prefixEnd_244170 37148613750641457022841 := by
  unfold tailWord_244170
  simp only [CollatzResearch.WordTrace]
  refine ⟨2226402881355316440282491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5937074350280843840753309 2226402881355316440282491)
  ·
    refine ⟨3339604322032974660423737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2226402881355316440282491 3339604322032974660423737)
    ·
      refine ⟨2504703241524730995317803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3339604322032974660423737 2504703241524730995317803)
      ·
        refine ⟨3757054862287096492976705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2504703241524730995317803 3757054862287096492976705)
        ·
          refine ⟨2817791146715322369732529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3757054862287096492976705 2817791146715322369732529)
          ·
            refine ⟨2113343360036491777299397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2817791146715322369732529 2113343360036491777299397)
            ·
              refine ⟨396251880006842208243637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2113343360036491777299397 396251880006842208243637)
              ·
                refine ⟨37148613750641457022841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 396251880006842208243637 37148613750641457022841)
                ·
                  rfl

theorem cell20_244170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 5].length) (baseStart_244170 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_244170 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_244170 prefixEnd_244170 := by exact prefixLift 244170
  have htrace : WordTrace (prefixWord ++ tailWord_244170) baseStart_244170 baseEnd_244170 := by
    simpa [prefixWord, tailWord_244170, baseEnd_244170] using wordTrace_append hprefix tailTrace_244170
  have hstable : (prefixWord ++ tailWord_244170).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244170).length < 2 ^ (prefixWord ++ tailWord_244170).sum := by decide
  have hdescent : baseEnd_244170 < baseStart_244170 := by decide
  rcases family_descends (prefixWord ++ tailWord_244170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244184 : List Nat := [2, 1, 2, 2, 2, 1, 1, 3, 6]
def baseStart_244184 : Nat := 118140960795 + 244184 * 2 ^ 59
def prefixEnd_244184 : Nat := 4983230072969 + 3 ^ 40 * 244184 * 2
def baseEnd_244184 : Nat := 111452231233402544601799

theorem tailTrace_244184 : CollatzResearch.WordTrace tailWord_244184 prefixEnd_244184 111452231233402544601799 := by
  unfold tailWord_244184
  simp only [CollatzResearch.WordTrace]
  refine ⟨4453061073685273076069803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5937414764913697434759737 4453061073685273076069803)
  ·
    refine ⟨6679591610527909614104705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4453061073685273076069803 6679591610527909614104705)
    ·
      refine ⟨5009693707895932210578529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6679591610527909614104705 5009693707895932210578529)
      ·
        refine ⟨3757270280921949157933897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5009693707895932210578529 3757270280921949157933897)
        ·
          refine ⟨2817952710691461868450423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3757270280921949157933897 2817952710691461868450423)
          ·
            refine ⟨4226929066037192802675635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2817952710691461868450423 4226929066037192802675635)
            ·
              refine ⟨6340393599055789204013453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4226929066037192802675635 6340393599055789204013453)
              ·
                refine ⟨2377647599645920951505045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6340393599055789204013453 2377647599645920951505045)
                ·
                  refine ⟨111452231233402544601799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2377647599645920951505045 111452231233402544601799)
                  ·
                    rfl

theorem cell20_244184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 6].length) (baseStart_244184 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_244184 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_244184 prefixEnd_244184 := by exact prefixLift 244184
  have htrace : WordTrace (prefixWord ++ tailWord_244184) baseStart_244184 baseEnd_244184 := by
    simpa [prefixWord, tailWord_244184, baseEnd_244184] using wordTrace_append hprefix tailTrace_244184
  have hstable : (prefixWord ++ tailWord_244184).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244184).length < 2 ^ (prefixWord ++ tailWord_244184).sum := by decide
  have hdescent : baseEnd_244184 < baseStart_244184 := by decide
  rcases family_descends (prefixWord ++ tailWord_244184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244225 : List Nat := [1, 2, 4, 1, 3, 3, 1, 5]
def baseStart_244225 : Nat := 118140960795 + 244225 * 2 ^ 59
def prefixEnd_244225 : Nat := 4983230072969 + 3 ^ 40 * 244225 * 2
def baseEnd_244225 : Nat := 37156981583529541411655

theorem tailTrace_244225 : CollatzResearch.WordTrace tailWord_244225 prefixEnd_244225 37156981583529541411655 := by
  unfold tailWord_244225
  simp only [CollatzResearch.WordTrace]
  refine ⟨8907617540222010154382129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5938411693481340102921419 8907617540222010154382129)
  ·
    refine ⟨6680713155166507615786597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8907617540222010154382129 6680713155166507615786597)
    ·
      refine ⟨1252633716593720177959987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6680713155166507615786597 1252633716593720177959987)
      ·
        refine ⟨1878950574890580266939981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1252633716593720177959987 1878950574890580266939981)
        ·
          refine ⟨704606465583967600102493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1878950574890580266939981 704606465583967600102493)
          ·
            refine ⟨264227424593987850038435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 704606465583967600102493 264227424593987850038435)
            ·
              refine ⟨396341136890981775057653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264227424593987850038435 396341136890981775057653)
              ·
                refine ⟨37156981583529541411655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 396341136890981775057653 37156981583529541411655)
                ·
                  rfl

theorem cell20_244225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 5].length) (baseStart_244225 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_244225 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_244225 prefixEnd_244225 := by exact prefixLift 244225
  have htrace : WordTrace (prefixWord ++ tailWord_244225) baseStart_244225 baseEnd_244225 := by
    simpa [prefixWord, tailWord_244225, baseEnd_244225] using wordTrace_append hprefix tailTrace_244225
  have hstable : (prefixWord ++ tailWord_244225).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244225).length < 2 ^ (prefixWord ++ tailWord_244225).sum := by decide
  have hdescent : baseEnd_244225 < baseStart_244225 := by decide
  rcases family_descends (prefixWord ++ tailWord_244225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244277 : List Nat := [1, 3, 3, 1, 1, 2, 4, 1, 4]
def baseStart_244277 : Nat := 118140960795 + 244277 * 2 ^ 59
def prefixEnd_244277 : Nat := 4983230072969 + 3 ^ 40 * 244277 * 2
def baseEnd_244277 : Nat := 111494678967507554501419

theorem tailTrace_244277 : CollatzResearch.WordTrace tailWord_244277 prefixEnd_244277 111494678967507554501419 := by
  unfold tailWord_244277
  simp only [CollatzResearch.WordTrace]
  refine ⟨8909514136033623035275085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5939676090689082023516723 8909514136033623035275085)
  ·
    refine ⟨3341067801012608638228157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8909514136033623035275085 3341067801012608638228157)
    ·
      refine ⟨1252900425379728239335559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3341067801012608638228157 1252900425379728239335559)
      ·
        refine ⟨1879350638069592359003339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1252900425379728239335559 1879350638069592359003339)
        ·
          refine ⟨2819025957104388538505009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1879350638069592359003339 2819025957104388538505009)
          ·
            refine ⟨2114269467828291403878757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2819025957104388538505009 2114269467828291403878757)
            ·
              refine ⟨396425525217804638227267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2114269467828291403878757 396425525217804638227267)
              ·
                refine ⟨594638287826706957340901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 396425525217804638227267 594638287826706957340901)
                ·
                  refine ⟨111494678967507554501419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 594638287826706957340901 111494678967507554501419)
                  ·
                    rfl

theorem cell20_244277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 1, 4].length) (baseStart_244277 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_244277 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_244277 prefixEnd_244277 := by exact prefixLift 244277
  have htrace : WordTrace (prefixWord ++ tailWord_244277) baseStart_244277 baseEnd_244277 := by
    simpa [prefixWord, tailWord_244277, baseEnd_244277] using wordTrace_append hprefix tailTrace_244277
  have hstable : (prefixWord ++ tailWord_244277).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244277).length < 2 ^ (prefixWord ++ tailWord_244277).sum := by decide
  have hdescent : baseEnd_244277 < baseStart_244277 := by decide
  rcases family_descends (prefixWord ++ tailWord_244277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244291 : List Nat := [1, 1, 1, 3, 1, 2, 1, 7, 3]
def baseStart_244291 : Nat := 118140960795 + 244291 * 2 ^ 59
def prefixEnd_244291 : Nat := 4983230072969 + 3 ^ 40 * 244291 * 2
def baseEnd_244291 : Nat := 111501068948985728034695

theorem tailTrace_244291 : CollatzResearch.WordTrace tailWord_244291 prefixEnd_244291 111501068948985728034695 := by
  unfold tailWord_244291
  simp only [CollatzResearch.WordTrace]
  refine ⟨8910024757982903426284727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5940016505321935617523151 8910024757982903426284727)
  ·
    refine ⟨13365037136974355139427091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8910024757982903426284727 13365037136974355139427091)
    ·
      refine ⟨20047555705461532709140637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13365037136974355139427091 20047555705461532709140637)
      ·
        refine ⟨7517833389548074765927739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20047555705461532709140637 7517833389548074765927739)
        ·
          refine ⟨11276750084322112148891609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7517833389548074765927739 11276750084322112148891609)
          ·
            refine ⟨8457562563241584111668707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11276750084322112148891609 8457562563241584111668707)
            ·
              refine ⟨12686343844862376167503061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8457562563241584111668707 12686343844862376167503061)
              ·
                refine ⟨297336183863961941425853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 12686343844862376167503061 297336183863961941425853)
                ·
                  refine ⟨111501068948985728034695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 297336183863961941425853 111501068948985728034695)
                  ·
                    rfl

theorem cell20_244291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 7, 3].length) (baseStart_244291 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_244291 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_244291 prefixEnd_244291 := by exact prefixLift 244291
  have htrace : WordTrace (prefixWord ++ tailWord_244291) baseStart_244291 baseEnd_244291 := by
    simpa [prefixWord, tailWord_244291, baseEnd_244291] using wordTrace_append hprefix tailTrace_244291
  have hstable : (prefixWord ++ tailWord_244291).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244291).length < 2 ^ (prefixWord ++ tailWord_244291).sum := by decide
  have hdescent : baseEnd_244291 < baseStart_244291 := by decide
  rcases family_descends (prefixWord ++ tailWord_244291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244301 : List Nat := [1, 6, 1, 1, 2, 2, 1, 6]
def baseStart_244301 : Nat := 118140960795 + 244301 * 2 ^ 59
def prefixEnd_244301 : Nat := 4983230072969 + 3 ^ 40 * 244301 * 2
def baseEnd_244301 : Nat := 37168544407156712567107

theorem tailTrace_244301 : CollatzResearch.WordTrace tailWord_244301 prefixEnd_244301 37168544407156712567107 := by
  unfold tailWord_244301
  simp only [CollatzResearch.WordTrace]
  refine ⟨8910389487946675134148757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5940259658631116756099171 8910389487946675134148757)
  ·
    refine ⟨417674507247500396913223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 8910389487946675134148757 417674507247500396913223)
    ·
      refine ⟨626511760871250595369835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417674507247500396913223 626511760871250595369835)
      ·
        refine ⟨939767641306875893054753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 626511760871250595369835 939767641306875893054753)
        ·
          refine ⟨704825730980156919791065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 939767641306875893054753 704825730980156919791065)
          ·
            refine ⟨528619298235117689843299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 704825730980156919791065 528619298235117689843299)
            ·
              refine ⟨792928947352676534764949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 528619298235117689843299 792928947352676534764949)
              ·
                refine ⟨37168544407156712567107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 792928947352676534764949 37168544407156712567107)
                ·
                  rfl

theorem cell20_244301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 6].length) (baseStart_244301 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_244301 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_244301 prefixEnd_244301 := by exact prefixLift 244301
  have htrace : WordTrace (prefixWord ++ tailWord_244301) baseStart_244301 baseEnd_244301 := by
    simpa [prefixWord, tailWord_244301, baseEnd_244301] using wordTrace_append hprefix tailTrace_244301
  have hstable : (prefixWord ++ tailWord_244301).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244301).length < 2 ^ (prefixWord ++ tailWord_244301).sum := by decide
  have hdescent : baseEnd_244301 < baseStart_244301 := by decide
  rcases family_descends (prefixWord ++ tailWord_244301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244328 : List Nat := [2, 1, 4, 3, 2, 1, 3, 2, 2]
def baseStart_244328 : Nat := 118140960795 + 244328 * 2 ^ 59
def prefixEnd_244328 : Nat := 4983230072969 + 3 ^ 40 * 244328 * 2
def baseEnd_244328 : Nat := 111517956757178043801211

theorem tailTrace_244328 : CollatzResearch.WordTrace tailWord_244328 prefixEnd_244328 111517956757178043801211 := by
  unfold tailWord_244328
  simp only [CollatzResearch.WordTrace]
  refine ⟨4455687129424429372690819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5940916172565905830254425 4455687129424429372690819)
  ·
    refine ⟨6683530694136644059036229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4455687129424429372690819 6683530694136644059036229)
    ·
      refine ⟨1253162005150620761069293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6683530694136644059036229 1253162005150620761069293)
      ·
        refine ⟨469935751931482785400985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1253162005150620761069293 469935751931482785400985)
        ·
          refine ⟨352451813948612089050739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 469935751931482785400985 352451813948612089050739)
          ·
            refine ⟨528677720922918133576109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352451813948612089050739 528677720922918133576109)
            ·
              refine ⟨198254145346094300091041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 528677720922918133576109 198254145346094300091041)
              ·
                refine ⟨148690609009570725068281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 198254145346094300091041 148690609009570725068281)
                ·
                  refine ⟨111517956757178043801211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 148690609009570725068281 111517956757178043801211)
                  ·
                    rfl

theorem cell20_244328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 3, 2, 2].length) (baseStart_244328 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_244328 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_244328 prefixEnd_244328 := by exact prefixLift 244328
  have htrace : WordTrace (prefixWord ++ tailWord_244328) baseStart_244328 baseEnd_244328 := by
    simpa [prefixWord, tailWord_244328, baseEnd_244328] using wordTrace_append hprefix tailTrace_244328
  have hstable : (prefixWord ++ tailWord_244328).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244328).length < 2 ^ (prefixWord ++ tailWord_244328).sum := by decide
  have hdescent : baseEnd_244328 < baseStart_244328 := by decide
  rcases family_descends (prefixWord ++ tailWord_244328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244329 : List Nat := [1, 2, 1, 1, 1, 4, 1, 6, 3]
def baseStart_244329 : Nat := 118140960795 + 244329 * 2 ^ 59
def prefixEnd_244329 : Nat := 4983230072969 + 3 ^ 40 * 244329 * 2
def baseEnd_244329 : Nat := 111518413184426484767873

theorem tailTrace_244329 : CollatzResearch.WordTrace tailWord_244329 prefixEnd_244329 111518413184426484767873 := by
  unfold tailWord_244329
  simp only [CollatzResearch.WordTrace]
  refine ⟨8911410731845235916168041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5940940487896823944112027 8911410731845235916168041)
  ·
    refine ⟨6683558048883926937126031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8911410731845235916168041 6683558048883926937126031)
    ·
      refine ⟨10025337073325890405689047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6683558048883926937126031 10025337073325890405689047)
      ·
        refine ⟨15038005609988835608533571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10025337073325890405689047 15038005609988835608533571)
        ·
          refine ⟨22557008414983253412800357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15038005609988835608533571 22557008414983253412800357)
          ·
            refine ⟨4229439077809360014900067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22557008414983253412800357 4229439077809360014900067)
            ·
              refine ⟨6344158616714040022350101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4229439077809360014900067 6344158616714040022350101)
              ·
                refine ⟨297382435158470626047661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6344158616714040022350101 297382435158470626047661)
                ·
                  refine ⟨111518413184426484767873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 297382435158470626047661 111518413184426484767873)
                  ·
                    rfl

theorem cell20_244329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 6, 3].length) (baseStart_244329 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_244329 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_244329 prefixEnd_244329 := by exact prefixLift 244329
  have htrace : WordTrace (prefixWord ++ tailWord_244329) baseStart_244329 baseEnd_244329 := by
    simpa [prefixWord, tailWord_244329, baseEnd_244329] using wordTrace_append hprefix tailTrace_244329
  have hstable : (prefixWord ++ tailWord_244329).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244329).length < 2 ^ (prefixWord ++ tailWord_244329).sum := by decide
  have hdescent : baseEnd_244329 < baseStart_244329 := by decide
  rcases family_descends (prefixWord ++ tailWord_244329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244343 : List Nat := [1, 1, 3, 1, 1, 3, 3, 7]
def baseStart_244343 : Nat := 118140960795 + 244343 * 2 ^ 59
def prefixEnd_244343 : Nat := 4983230072969 + 3 ^ 40 * 244343 * 2
def baseEnd_244343 : Nat := 37174934388634886100383

theorem tailTrace_244343 : CollatzResearch.WordTrace tailWord_244343 prefixEnd_244343 37174934388634886100383 := by
  unfold tailWord_244343
  simp only [CollatzResearch.WordTrace]
  refine ⟨8911921353794516307177683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5941280902529677538118455 8911921353794516307177683)
  ·
    refine ⟨13367882030691774460766525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8911921353794516307177683 13367882030691774460766525)
    ·
      refine ⟨5012955761509415422787447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13367882030691774460766525 5012955761509415422787447)
      ·
        refine ⟨7519433642264123134181171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5012955761509415422787447 7519433642264123134181171)
        ·
          refine ⟨11279150463396184701271757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7519433642264123134181171 11279150463396184701271757)
          ·
            refine ⟨4229681423773569262976909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11279150463396184701271757 4229681423773569262976909)
            ·
              refine ⟨1586130533915088473616341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4229681423773569262976909 1586130533915088473616341)
              ·
                refine ⟨37174934388634886100383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1586130533915088473616341 37174934388634886100383)
                ·
                  rfl

theorem cell20_244343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 7].length) (baseStart_244343 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_244343 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_244343 prefixEnd_244343 := by exact prefixLift 244343
  have htrace : WordTrace (prefixWord ++ tailWord_244343) baseStart_244343 baseEnd_244343 := by
    simpa [prefixWord, tailWord_244343, baseEnd_244343] using wordTrace_append hprefix tailTrace_244343
  have hstable : (prefixWord ++ tailWord_244343).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244343).length < 2 ^ (prefixWord ++ tailWord_244343).sum := by decide
  have hdescent : baseEnd_244343 < baseStart_244343 := by decide
  rcases family_descends (prefixWord ++ tailWord_244343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244474 : List Nat := [3, 1, 1, 1, 1, 3, 6, 4]
def baseStart_244474 : Nat := 118140960795 + 244474 * 2 ^ 59
def prefixEnd_244474 : Nat := 4983230072969 + 3 ^ 40 * 244474 * 2
def baseEnd_244474 : Nat := 37194865045150141644649

theorem tailTrace_244474 : CollatzResearch.WordTrace tailWord_244474 prefixEnd_244474 37194865045150141644649 := by
  unfold tailWord_244474
  simp only [CollatzResearch.WordTrace]
  refine ⟨2229174829079981420049119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5944466210879950453464317 2229174829079981420049119)
  ·
    refine ⟨3343762243619972130073679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2229174829079981420049119 3343762243619972130073679)
    ·
      refine ⟨5015643365429958195110519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3343762243619972130073679 5015643365429958195110519)
      ·
        refine ⟨7523465048144937292665779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5015643365429958195110519 7523465048144937292665779)
        ·
          refine ⟨11285197572217405938998669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7523465048144937292665779 11285197572217405938998669)
          ·
            refine ⟨4231949089581527227124501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11285197572217405938998669 4231949089581527227124501)
            ·
              refine ⟨198372613574134088771461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4231949089581527227124501 198372613574134088771461)
              ·
                refine ⟨37194865045150141644649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 198372613574134088771461 37194865045150141644649)
                ·
                  rfl

theorem cell20_244474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 6, 4].length) (baseStart_244474 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_244474 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_244474 prefixEnd_244474 := by exact prefixLift 244474
  have htrace : WordTrace (prefixWord ++ tailWord_244474) baseStart_244474 baseEnd_244474 := by
    simpa [prefixWord, tailWord_244474, baseEnd_244474] using wordTrace_append hprefix tailTrace_244474
  have hstable : (prefixWord ++ tailWord_244474).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244474).length < 2 ^ (prefixWord ++ tailWord_244474).sum := by decide
  have hdescent : baseEnd_244474 < baseStart_244474 := by decide
  rcases family_descends (prefixWord ++ tailWord_244474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244512 : List Nat := [2, 1, 1, 5, 1, 3, 2, 5]
def baseStart_244512 : Nat := 118140960795 + 244512 * 2 ^ 59
def prefixEnd_244512 : Nat := 4983230072969 + 3 ^ 40 * 244512 * 2
def baseEnd_244512 : Nat := 37200646456963727222375

theorem tailTrace_244512 : CollatzResearch.WordTrace tailWord_244512 prefixEnd_244512 37200646456963727222375 := by
  unfold tailWord_244512
  simp only [CollatzResearch.WordTrace]
  refine ⟨4459042645091129085039895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5945390193454838780053193 4459042645091129085039895)
  ·
    refine ⟨6688563967636693627559843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4459042645091129085039895 6688563967636693627559843)
    ·
      refine ⟨10032845951455040441339765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6688563967636693627559843 10032845951455040441339765)
      ·
        refine ⟨940579307948910041375603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10032845951455040441339765 940579307948910041375603)
        ·
          refine ⟨1410868961923365062063405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 940579307948910041375603 1410868961923365062063405)
          ·
            refine ⟨529075860721261898273777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1410868961923365062063405 529075860721261898273777)
            ·
              refine ⟨396806895540946423705333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 529075860721261898273777 396806895540946423705333)
              ·
                refine ⟨37200646456963727222375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 396806895540946423705333 37200646456963727222375)
                ·
                  rfl

theorem cell20_244512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 5].length) (baseStart_244512 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_244512 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_244512 prefixEnd_244512 := by exact prefixLift 244512
  have htrace : WordTrace (prefixWord ++ tailWord_244512) baseStart_244512 baseEnd_244512 := by
    simpa [prefixWord, tailWord_244512, baseEnd_244512] using wordTrace_append hprefix tailTrace_244512
  have hstable : (prefixWord ++ tailWord_244512).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244512).length < 2 ^ (prefixWord ++ tailWord_244512).sum := by decide
  have hdescent : baseEnd_244512 < baseStart_244512 := by decide
  rcases family_descends (prefixWord ++ tailWord_244512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244560 : List Nat := [2, 1, 1, 1, 1, 4, 6, 2, 2]
def baseStart_244560 : Nat := 118140960795 + 244560 * 2 ^ 59
def prefixEnd_244560 : Nat := 4983230072969 + 3 ^ 40 * 244560 * 2
def baseEnd_244560 : Nat := 111623847878816348066929

theorem tailTrace_244560 : CollatzResearch.WordTrace tailWord_244560 prefixEnd_244560 111623847878816348066929 := by
  unfold tailWord_244560
  simp only [CollatzResearch.WordTrace]
  refine ⟨4459917997004181183913567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5946557329338908245218089 4459917997004181183913567)
  ·
    refine ⟨6689876995506271775870351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4459917997004181183913567 6689876995506271775870351)
    ·
      refine ⟨10034815493259407663805527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6689876995506271775870351 10034815493259407663805527)
      ·
        refine ⟨15052223239889111495708291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10034815493259407663805527 15052223239889111495708291)
        ·
          refine ⟨22578334859833667243562437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15052223239889111495708291 22578334859833667243562437)
          ·
            refine ⟨4233437786218812608167957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22578334859833667243562437 4233437786218812608167957)
            ·
              refine ⟨198442396229006841007873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4233437786218812608167957 198442396229006841007873)
              ·
                refine ⟨148831797171755130755905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 198442396229006841007873 148831797171755130755905)
                ·
                  refine ⟨111623847878816348066929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 148831797171755130755905 111623847878816348066929)
                  ·
                    rfl

theorem cell20_244560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 6, 2, 2].length) (baseStart_244560 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_244560 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_244560 prefixEnd_244560 := by exact prefixLift 244560
  have htrace : WordTrace (prefixWord ++ tailWord_244560) baseStart_244560 baseEnd_244560 := by
    simpa [prefixWord, tailWord_244560, baseEnd_244560] using wordTrace_append hprefix tailTrace_244560
  have hstable : (prefixWord ++ tailWord_244560).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244560).length < 2 ^ (prefixWord ++ tailWord_244560).sum := by decide
  have hdescent : baseEnd_244560 < baseStart_244560 := by decide
  rcases family_descends (prefixWord ++ tailWord_244560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244588 : List Nat := [2, 2, 1, 1, 4, 1, 5, 4]
def baseStart_244588 : Nat := 118140960795 + 244588 * 2 ^ 59
def prefixEnd_244588 : Nat := 4983230072969 + 3 ^ 40 * 244588 * 2
def baseEnd_244588 : Nat := 37212209280590898377827

theorem tailTrace_244588 : CollatzResearch.WordTrace tailWord_244588 prefixEnd_244588 37212209280590898377827 := by
  unfold tailWord_244588
  simp only [CollatzResearch.WordTrace]
  refine ⟨4460428618953461574923209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5947238158604615433230945 4460428618953461574923209)
  ·
    refine ⟨3345321464215096181192407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4460428618953461574923209 3345321464215096181192407)
    ·
      refine ⟨5017982196322644271788611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3345321464215096181192407 5017982196322644271788611)
      ·
        refine ⟨7526973294483966407682917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5017982196322644271788611 7526973294483966407682917)
        ·
          refine ⟨1411307492715743701440547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7526973294483966407682917 1411307492715743701440547)
          ·
            refine ⟨2116961239073615552160821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1411307492715743701440547 2116961239073615552160821)
            ·
              refine ⟨198465116163151458015077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2116961239073615552160821 198465116163151458015077)
              ·
                refine ⟨37212209280590898377827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 198465116163151458015077 37212209280590898377827)
                ·
                  rfl

theorem cell20_244588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 5, 4].length) (baseStart_244588 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_244588 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_244588 prefixEnd_244588 := by exact prefixLift 244588
  have htrace : WordTrace (prefixWord ++ tailWord_244588) baseStart_244588 baseEnd_244588 := by
    simpa [prefixWord, tailWord_244588, baseEnd_244588] using wordTrace_append hprefix tailTrace_244588
  have hstable : (prefixWord ++ tailWord_244588).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244588).length < 2 ^ (prefixWord ++ tailWord_244588).sum := by decide
  have hdescent : baseEnd_244588 < baseStart_244588 := by decide
  rcases family_descends (prefixWord ++ tailWord_244588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244619 : List Nat := [1, 1, 1, 1, 4, 2, 4, 4, 2]
def baseStart_244619 : Nat := 118140960795 + 244619 * 2 ^ 59
def prefixEnd_244619 : Nat := 4983230072969 + 3 ^ 40 * 244619 * 2
def baseEnd_244619 : Nat := 111650777086474365100021

theorem tailTrace_244619 : CollatzResearch.WordTrace tailWord_244619 prefixEnd_244619 111650777086474365100021 := by
  unfold tailWord_244619
  simp only [CollatzResearch.WordTrace]
  refine ⟨8921987900794615444224911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5947991933863076962816607 8921987900794615444224911)
  ·
    refine ⟨13382981851191923166337367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8921987900794615444224911 13382981851191923166337367)
    ·
      refine ⟨20074472776787884749506051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13382981851191923166337367 20074472776787884749506051)
      ·
        refine ⟨30111709165181827124259077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20074472776787884749506051 30111709165181827124259077)
        ·
          refine ⟨5645945468471592585798577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30111709165181827124259077 5645945468471592585798577)
          ·
            refine ⟨4234459101353694439348933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5645945468471592585798577 4234459101353694439348933)
            ·
              refine ⟨793961081503817707377925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4234459101353694439348933 793961081503817707377925)
              ·
                refine ⟨148867702781965820133361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 793961081503817707377925 148867702781965820133361)
                ·
                  refine ⟨111650777086474365100021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 148867702781965820133361 111650777086474365100021)
                  ·
                    rfl

theorem cell20_244619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 4, 2].length) (baseStart_244619 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_244619 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_244619 prefixEnd_244619 := by exact prefixLift 244619
  have htrace : WordTrace (prefixWord ++ tailWord_244619) baseStart_244619 baseEnd_244619 := by
    simpa [prefixWord, tailWord_244619, baseEnd_244619] using wordTrace_append hprefix tailTrace_244619
  have hstable : (prefixWord ++ tailWord_244619).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244619).length < 2 ^ (prefixWord ++ tailWord_244619).sum := by decide
  have hdescent : baseEnd_244619 < baseStart_244619 := by decide
  rcases family_descends (prefixWord ++ tailWord_244619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244640 : List Nat := [2, 1, 1, 4, 1, 1, 4, 2, 4]
def baseStart_244640 : Nat := 118140960795 + 244640 * 2 ^ 59
def prefixEnd_244640 : Nat := 4983230072969 + 3 ^ 40 * 244640 * 2
def baseEnd_244640 : Nat := 111660362058691625399935

theorem tailTrace_244640 : CollatzResearch.WordTrace tailWord_244640 prefixEnd_244640 111660362058691625399935 := by
  unfold tailWord_244640
  simp only [CollatzResearch.WordTrace]
  refine ⟨4461376916859268015369687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5948502555812357353826249 4461376916859268015369687)
  ·
    refine ⟨6692065375288902023054531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4461376916859268015369687 6692065375288902023054531)
    ·
      refine ⟨10038098062933353034581797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6692065375288902023054531 10038098062933353034581797)
      ·
        refine ⟨1882143386800003693984087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10038098062933353034581797 1882143386800003693984087)
        ·
          refine ⟨2823215080200005540976131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1882143386800003693984087 2823215080200005540976131)
          ·
            refine ⟨4234822620300008311464197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2823215080200005540976131 4234822620300008311464197)
            ·
              refine ⟨794029241306251558399537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4234822620300008311464197 794029241306251558399537)
              ·
                refine ⟨595521930979688668799653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 794029241306251558399537 595521930979688668799653)
                ·
                  refine ⟨111660362058691625399935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 595521930979688668799653 111660362058691625399935)
                  ·
                    rfl

theorem cell20_244640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 2, 4].length) (baseStart_244640 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_244640 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_244640 prefixEnd_244640 := by exact prefixLift 244640
  have htrace : WordTrace (prefixWord ++ tailWord_244640) baseStart_244640 baseEnd_244640 := by
    simpa [prefixWord, tailWord_244640, baseEnd_244640] using wordTrace_append hprefix tailTrace_244640
  have hstable : (prefixWord ++ tailWord_244640).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244640).length < 2 ^ (prefixWord ++ tailWord_244640).sum := by decide
  have hdescent : baseEnd_244640 < baseStart_244640 := by decide
  rcases family_descends (prefixWord ++ tailWord_244640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244725 : List Nat := [1, 3, 5, 2, 1, 2, 2, 2, 2]
def baseStart_244725 : Nat := 118140960795 + 244725 * 2 ^ 59
def prefixEnd_244725 : Nat := 4983230072969 + 3 ^ 40 * 244725 * 2
def baseEnd_244725 : Nat := 111699158374809107566255

theorem tailTrace_244725 : CollatzResearch.WordTrace tailWord_244725 prefixEnd_244725 111699158374809107566255 := by
  unfold tailWord_244725
  simp only [CollatzResearch.WordTrace]
  refine ⟨8925854038410595547583629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5950569358940397031722419 8925854038410595547583629)
  ·
    refine ⟨3347195264403973330343861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8925854038410595547583629 3347195264403973330343861)
    ·
      refine ⟨313799556037872499719737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3347195264403973330343861 313799556037872499719737)
      ·
        refine ⟨235349667028404374789803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313799556037872499719737 235349667028404374789803)
        ·
          refine ⟨353024500542606562184705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235349667028404374789803 353024500542606562184705)
          ·
            refine ⟨264768375406954921638529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 353024500542606562184705 264768375406954921638529)
            ·
              refine ⟨198576281555216191228897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264768375406954921638529 198576281555216191228897)
              ·
                refine ⟨148932211166412143421673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 198576281555216191228897 148932211166412143421673)
                ·
                  refine ⟨111699158374809107566255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 148932211166412143421673 111699158374809107566255)
                  ·
                    rfl

theorem cell20_244725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 2, 2, 2].length) (baseStart_244725 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_244725 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_244725 prefixEnd_244725 := by exact prefixLift 244725
  have htrace : WordTrace (prefixWord ++ tailWord_244725) baseStart_244725 baseEnd_244725 := by
    simpa [prefixWord, tailWord_244725, baseEnd_244725] using wordTrace_append hprefix tailTrace_244725
  have hstable : (prefixWord ++ tailWord_244725).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244725).length < 2 ^ (prefixWord ++ tailWord_244725).sum := by decide
  have hdescent : baseEnd_244725 < baseStart_244725 := by decide
  rcases family_descends (prefixWord ++ tailWord_244725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244726 : List Nat := [5, 1, 1, 1, 3, 1, 1, 4, 3]
def baseStart_244726 : Nat := 118140960795 + 244726 * 2 ^ 59
def prefixEnd_244726 : Nat := 4983230072969 + 3 ^ 40 * 244726 * 2
def baseEnd_244726 : Nat := 111699614802057548532917

theorem tailTrace_244726 : CollatzResearch.WordTrace tailWord_244726 prefixEnd_244726 111699614802057548532917 := by
  unfold tailWord_244726
  simp only [CollatzResearch.WordTrace]
  refine ⟨557868156962935794898127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5950593674271315145580021 557868156962935794898127)
  ·
    refine ⟨836802235444403692347191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 557868156962935794898127 836802235444403692347191)
    ·
      refine ⟨1255203353166605538520787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 836802235444403692347191 1255203353166605538520787)
      ·
        refine ⟨1882805029749908307781181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1255203353166605538520787 1882805029749908307781181)
        ·
          refine ⟨706051886156215615417943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1882805029749908307781181 706051886156215615417943)
          ·
            refine ⟨1059077829234323423126915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 706051886156215615417943 1059077829234323423126915)
            ·
              refine ⟨1588616743851485134690373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1059077829234323423126915 1588616743851485134690373)
              ·
                refine ⟨297865639472153462754445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1588616743851485134690373 297865639472153462754445)
                ·
                  refine ⟨111699614802057548532917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 297865639472153462754445 111699614802057548532917)
                  ·
                    rfl

theorem cell20_244726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_244726 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_244726 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_244726 prefixEnd_244726 := by exact prefixLift 244726
  have htrace : WordTrace (prefixWord ++ tailWord_244726) baseStart_244726 baseEnd_244726 := by
    simpa [prefixWord, tailWord_244726, baseEnd_244726] using wordTrace_append hprefix tailTrace_244726
  have hstable : (prefixWord ++ tailWord_244726).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244726).length < 2 ^ (prefixWord ++ tailWord_244726).sum := by decide
  have hdescent : baseEnd_244726 < baseStart_244726 := by decide
  rcases family_descends (prefixWord ++ tailWord_244726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244730 : List Nat := [3, 1, 1, 1, 1, 2, 1, 5, 5]
def baseStart_244730 : Nat := 118140960795 + 244730 * 2 ^ 59
def prefixEnd_244730 : Nat := 4983230072969 + 3 ^ 40 * 244730 * 2
def baseEnd_244730 : Nat := 111701440511051312399567

theorem tailTrace_244730 : CollatzResearch.WordTrace tailWord_244730 prefixEnd_244730 111701440511051312399567 := by
  unfold tailWord_244730
  simp only [CollatzResearch.WordTrace]
  refine ⟨2231509100848120350378911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5950690935594987601010429 2231509100848120350378911)
  ·
    refine ⟨3347263651272180525568367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2231509100848120350378911 3347263651272180525568367)
    ·
      refine ⟨5020895476908270788352551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3347263651272180525568367 5020895476908270788352551)
      ·
        refine ⟨7531343215362406182528827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5020895476908270788352551 7531343215362406182528827)
        ·
          refine ⟨11297014823043609273793241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7531343215362406182528827 11297014823043609273793241)
          ·
            refine ⟨8472761117282706955344931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11297014823043609273793241 8472761117282706955344931)
            ·
              refine ⟨12709141675924060433017397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8472761117282706955344931 12709141675924060433017397)
              ·
                refine ⟨1191482032117880665595381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12709141675924060433017397 1191482032117880665595381)
                ·
                  refine ⟨111701440511051312399567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1191482032117880665595381 111701440511051312399567)
                  ·
                    rfl

theorem cell20_244730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5, 5].length) (baseStart_244730 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_244730 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_244730 prefixEnd_244730 := by exact prefixLift 244730
  have htrace : WordTrace (prefixWord ++ tailWord_244730) baseStart_244730 baseEnd_244730 := by
    simpa [prefixWord, tailWord_244730, baseEnd_244730] using wordTrace_append hprefix tailTrace_244730
  have hstable : (prefixWord ++ tailWord_244730).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244730).length < 2 ^ (prefixWord ++ tailWord_244730).sum := by decide
  have hdescent : baseEnd_244730 < baseStart_244730 := by decide
  rcases family_descends (prefixWord ++ tailWord_244730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244747 : List Nat := [1, 1, 1, 1, 6, 2, 2, 3, 3]
def baseStart_244747 : Nat := 118140960795 + 244747 * 2 ^ 59
def prefixEnd_244747 : Nat := 4983230072969 + 3 ^ 40 * 244747 * 2
def baseEnd_244747 : Nat := 111709199774274808832831

theorem tailTrace_244747 : CollatzResearch.WordTrace tailWord_244747 prefixEnd_244747 111709199774274808832831 := by
  unfold tailWord_244747
  simp only [CollatzResearch.WordTrace]
  refine ⟨8926656444330893304884495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5951104296220595536589663 8926656444330893304884495)
  ·
    refine ⟨13389984666496339957326743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8926656444330893304884495 13389984666496339957326743)
    ·
      refine ⟨20084976999744509935990115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13389984666496339957326743 20084976999744509935990115)
      ·
        refine ⟨30127465499616764903985173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20084976999744509935990115 30127465499616764903985173)
        ·
          refine ⟨1412224945294535854874305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 30127465499616764903985173 1412224945294535854874305)
          ·
            refine ⟨1059168708970901891155729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1412224945294535854874305 1059168708970901891155729)
            ·
              refine ⟨794376531728176418366797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1059168708970901891155729 794376531728176418366797)
              ·
                refine ⟨297891199398066156887549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 794376531728176418366797 297891199398066156887549)
                ·
                  refine ⟨111709199774274808832831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 297891199398066156887549 111709199774274808832831)
                  ·
                    rfl

theorem cell20_244747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 3, 3].length) (baseStart_244747 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_244747 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_244747 prefixEnd_244747 := by exact prefixLift 244747
  have htrace : WordTrace (prefixWord ++ tailWord_244747) baseStart_244747 baseEnd_244747 := by
    simpa [prefixWord, tailWord_244747, baseEnd_244747] using wordTrace_append hprefix tailTrace_244747
  have hstable : (prefixWord ++ tailWord_244747).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244747).length < 2 ^ (prefixWord ++ tailWord_244747).sum := by decide
  have hdescent : baseEnd_244747 < baseStart_244747 := by decide
  rcases family_descends (prefixWord ++ tailWord_244747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244771 : List Nat := [1, 1, 1, 4, 3, 2, 1, 5, 2]
def baseStart_244771 : Nat := 118140960795 + 244771 * 2 ^ 59
def prefixEnd_244771 : Nat := 4983230072969 + 3 ^ 40 * 244771 * 2
def baseEnd_244771 : Nat := 111720154028237392032733

theorem tailTrace_244771 : CollatzResearch.WordTrace tailWord_244771 prefixEnd_244771 111720154028237392032733 := by
  unfold tailWord_244771
  simp only [CollatzResearch.WordTrace]
  refine ⟨8927531796243945403758167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5951687864162630269172111 8927531796243945403758167)
  ·
    refine ⟨13391297694365918105637251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8927531796243945403758167 13391297694365918105637251)
    ·
      refine ⟨20086946541548877158455877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13391297694365918105637251 20086946541548877158455877)
      ·
        refine ⟨3766302476540414467210477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20086946541548877158455877 3766302476540414467210477)
        ·
          refine ⟨1412363428702655425203929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3766302476540414467210477 1412363428702655425203929)
          ·
            refine ⟨1059272571526991568902947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1412363428702655425203929 1059272571526991568902947)
            ·
              refine ⟨1588908857290487353354421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1059272571526991568902947 1588908857290487353354421)
              ·
                refine ⟨148960205370983189376977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1588908857290487353354421 148960205370983189376977)
                ·
                  refine ⟨111720154028237392032733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 148960205370983189376977 111720154028237392032733)
                  ·
                    rfl

theorem cell20_244771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 5, 2].length) (baseStart_244771 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_244771 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_244771 prefixEnd_244771 := by exact prefixLift 244771
  have htrace : WordTrace (prefixWord ++ tailWord_244771) baseStart_244771 baseEnd_244771 := by
    simpa [prefixWord, tailWord_244771, baseEnd_244771] using wordTrace_append hprefix tailTrace_244771
  have hstable : (prefixWord ++ tailWord_244771).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244771).length < 2 ^ (prefixWord ++ tailWord_244771).sum := by decide
  have hdescent : baseEnd_244771 < baseStart_244771 := by decide
  rcases family_descends (prefixWord ++ tailWord_244771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244778 : List Nat := [3, 1, 4, 1, 3, 1, 7]
def baseStart_244778 : Nat := 118140960795 + 244778 * 2 ^ 59
def prefixEnd_244778 : Nat := 4983230072969 + 3 ^ 40 * 244778 * 2
def baseEnd_244778 : Nat := 12413705446552942088819

theorem tailTrace_244778 : CollatzResearch.WordTrace tailWord_244778 prefixEnd_244778 12413705446552942088819 := by
  unfold tailWord_244778
  simp only [CollatzResearch.WordTrace]
  refine ⟨2231946776804646399815747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5951858071479057066175325 2231946776804646399815747)
  ·
    refine ⟨3347920165206969599723621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2231946776804646399815747 3347920165206969599723621)
    ·
      refine ⟨627735030976306799948179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3347920165206969599723621 627735030976306799948179)
      ·
        refine ⟨941602546464460199922269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 627735030976306799948179 941602546464460199922269)
        ·
          refine ⟨353100954924172574970851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 941602546464460199922269 353100954924172574970851)
          ·
            refine ⟨529651432386258862456277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353100954924172574970851 529651432386258862456277)
            ·
              refine ⟨12413705446552942088819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 529651432386258862456277 12413705446552942088819)
              ·
                rfl

theorem cell20_244778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 7].length) (baseStart_244778 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_244778 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_244778 prefixEnd_244778 := by exact prefixLift 244778
  have htrace : WordTrace (prefixWord ++ tailWord_244778) baseStart_244778 baseEnd_244778 := by
    simpa [prefixWord, tailWord_244778, baseEnd_244778] using wordTrace_append hprefix tailTrace_244778
  have hstable : (prefixWord ++ tailWord_244778).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244778).length < 2 ^ (prefixWord ++ tailWord_244778).sum := by decide
  have hdescent : baseEnd_244778 < baseStart_244778 := by decide
  rcases family_descends (prefixWord ++ tailWord_244778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244788 : List Nat := [2, 5, 1, 2, 1, 2, 2, 1, 4]
def baseStart_244788 : Nat := 118140960795 + 244788 * 2 ^ 59
def prefixEnd_244788 : Nat := 4983230072969 + 3 ^ 40 * 244788 * 2
def baseEnd_244788 : Nat := 111727913291460888465997

theorem tailTrace_244788 : CollatzResearch.WordTrace tailWord_244788 prefixEnd_244788 111727913291460888465997 := by
  unfold tailWord_244788
  simp only [CollatzResearch.WordTrace]
  refine ⟨4464075918591178653563509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5952101224788238204751345 4464075918591178653563509)
  ·
    refine ⟨418507117367922998771579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4464075918591178653563509 418507117367922998771579)
    ·
      refine ⟨627760676051884498157369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418507117367922998771579 627760676051884498157369)
      ·
        refine ⟨470820507038913373618027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 627760676051884498157369 470820507038913373618027)
        ·
          refine ⟨706230760558370060427041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 470820507038913373618027 706230760558370060427041)
          ·
            refine ⟨529673070418777545320281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 706230760558370060427041 529673070418777545320281)
            ·
              refine ⟨397254802814083158990211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 529673070418777545320281 397254802814083158990211)
              ·
                refine ⟨595882204221124738485317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 397254802814083158990211 595882204221124738485317)
                ·
                  refine ⟨111727913291460888465997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 595882204221124738485317 111727913291460888465997)
                  ·
                    rfl

theorem cell20_244788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_244788 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_244788 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_244788 prefixEnd_244788 := by exact prefixLift 244788
  have htrace : WordTrace (prefixWord ++ tailWord_244788) baseStart_244788 baseEnd_244788 := by
    simpa [prefixWord, tailWord_244788, baseEnd_244788] using wordTrace_append hprefix tailTrace_244788
  have hstable : (prefixWord ++ tailWord_244788).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244788).length < 2 ^ (prefixWord ++ tailWord_244788).sum := by decide
  have hdescent : baseEnd_244788 < baseStart_244788 := by decide
  rcases family_descends (prefixWord ++ tailWord_244788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244792 : List Nat := [2, 1, 2, 1, 5, 1, 1, 3, 4]
def baseStart_244792 : Nat := 118140960795 + 244792 * 2 ^ 59
def prefixEnd_244792 : Nat := 4983230072969 + 3 ^ 40 * 244792 * 2
def baseEnd_244792 : Nat := 111729739000454652332647

theorem tailTrace_244792 : CollatzResearch.WordTrace tailWord_244792 prefixEnd_244792 111729739000454652332647 := by
  unfold tailWord_244792
  simp only [CollatzResearch.WordTrace]
  refine ⟨4464148864583932995136315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5952198486111910660181753 4464148864583932995136315)
  ·
    refine ⟨6696223296875899492704473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4464148864583932995136315 6696223296875899492704473)
    ·
      refine ⟨5022167472656924619528355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6696223296875899492704473 5022167472656924619528355)
      ·
        refine ⟨7533251208985386929292533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5022167472656924619528355 7533251208985386929292533)
        ·
          refine ⟨706242300842380024621175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7533251208985386929292533 706242300842380024621175)
          ·
            refine ⟨1059363451263570036931763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 706242300842380024621175 1059363451263570036931763)
            ·
              refine ⟨1589045176895355055397645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1059363451263570036931763 1589045176895355055397645)
              ·
                refine ⟨595891941335758145774117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1589045176895355055397645 595891941335758145774117)
                ·
                  refine ⟨111729739000454652332647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 595891941335758145774117 111729739000454652332647)
                  ·
                    rfl

theorem cell20_244792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 3, 4].length) (baseStart_244792 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_244792 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_244792 prefixEnd_244792 := by exact prefixLift 244792
  have htrace : WordTrace (prefixWord ++ tailWord_244792) baseStart_244792 baseEnd_244792 := by
    simpa [prefixWord, tailWord_244792, baseEnd_244792] using wordTrace_append hprefix tailTrace_244792
  have hstable : (prefixWord ++ tailWord_244792).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244792).length < 2 ^ (prefixWord ++ tailWord_244792).sum := by decide
  have hdescent : baseEnd_244792 < baseStart_244792 := by decide
  rcases family_descends (prefixWord ++ tailWord_244792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244844 : List Nat := [2, 2, 1, 1, 3, 2, 1, 3, 5]
def baseStart_244844 : Nat := 118140960795 + 244844 * 2 ^ 59
def prefixEnd_244844 : Nat := 4983230072969 + 3 ^ 40 * 244844 * 2
def baseEnd_244844 : Nat := 111753473217373582599101

theorem tailTrace_244844 : CollatzResearch.WordTrace tailWord_244844 prefixEnd_244844 111753473217373582599101 := by
  unfold tailWord_244844
  simp only [CollatzResearch.WordTrace]
  refine ⟨4465097162489739435582793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5953462883319652580777057 4465097162489739435582793)
  ·
    refine ⟨3348822871867304576687095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4465097162489739435582793 3348822871867304576687095)
    ·
      refine ⟨5023234307800956865030643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3348822871867304576687095 5023234307800956865030643)
      ·
        refine ⟨7534851461701435297545965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5023234307800956865030643 7534851461701435297545965)
        ·
          refine ⟨2825569298138038236579737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7534851461701435297545965 2825569298138038236579737)
          ·
            refine ⟨2119176973603528677434803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2825569298138038236579737 2119176973603528677434803)
            ·
              refine ⟨3178765460405293016152205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2119176973603528677434803 3178765460405293016152205)
              ·
                refine ⟨1192037047651984881057077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3178765460405293016152205 1192037047651984881057077)
                ·
                  refine ⟨111753473217373582599101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1192037047651984881057077 111753473217373582599101)
                  ·
                    rfl

theorem cell20_244844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 5].length) (baseStart_244844 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_244844 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_244844 prefixEnd_244844 := by exact prefixLift 244844
  have htrace : WordTrace (prefixWord ++ tailWord_244844) baseStart_244844 baseEnd_244844 := by
    simpa [prefixWord, tailWord_244844, baseEnd_244844] using wordTrace_append hprefix tailTrace_244844
  have hstable : (prefixWord ++ tailWord_244844).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244844).length < 2 ^ (prefixWord ++ tailWord_244844).sum := by decide
  have hdescent : baseEnd_244844 < baseStart_244844 := by decide
  rcases family_descends (prefixWord ++ tailWord_244844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244853 : List Nat := [1, 3, 4, 3, 2, 1, 2, 1, 3]
def baseStart_244853 : Nat := 118140960795 + 244853 * 2 ^ 59
def prefixEnd_244853 : Nat := 4983230072969 + 3 ^ 40 * 244853 * 2
def baseEnd_244853 : Nat := 111757581062609551299065

theorem tailTrace_244853 : CollatzResearch.WordTrace tailWord_244853 prefixEnd_244853 111757581062609551299065 := by
  unfold tailWord_244853
  simp only [CollatzResearch.WordTrace]
  refine ⟨8930522581946873408243213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5953681721297915605495475 8930522581946873408243213)
  ·
    refine ⟨3348945968230077528091205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8930522581946873408243213 3348945968230077528091205)
    ·
      refine ⟨627927369043139536517101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3348945968230077528091205 627927369043139536517101)
      ·
        refine ⟨235472763391177326193913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 627927369043139536517101 235472763391177326193913)
        ·
          refine ⟨176604572543382994645435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235472763391177326193913 176604572543382994645435)
          ·
            refine ⟨264906858815074491968153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176604572543382994645435 264906858815074491968153)
            ·
              refine ⟨198680144111305868976115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264906858815074491968153 198680144111305868976115)
              ·
                refine ⟨298020216166958803464173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198680144111305868976115 298020216166958803464173)
                ·
                  refine ⟨111757581062609551299065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 298020216166958803464173 111757581062609551299065)
                  ·
                    rfl

theorem cell20_244853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 2, 1, 3].length) (baseStart_244853 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_244853 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_244853 prefixEnd_244853 := by exact prefixLift 244853
  have htrace : WordTrace (prefixWord ++ tailWord_244853) baseStart_244853 baseEnd_244853 := by
    simpa [prefixWord, tailWord_244853, baseEnd_244853] using wordTrace_append hprefix tailTrace_244853
  have hstable : (prefixWord ++ tailWord_244853).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244853).length < 2 ^ (prefixWord ++ tailWord_244853).sum := by decide
  have hdescent : baseEnd_244853 < baseStart_244853 := by decide
  rcases family_descends (prefixWord ++ tailWord_244853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244854 : List Nat := [5, 1, 1, 2, 1, 1, 4, 5]
def baseStart_244854 : Nat := 118140960795 + 244854 * 2 ^ 59
def prefixEnd_244854 : Nat := 4983230072969 + 3 ^ 40 * 244854 * 2
def baseEnd_244854 : Nat := 37252679163285997421909

theorem tailTrace_244854 : CollatzResearch.WordTrace tailWord_244854 prefixEnd_244854 37252679163285997421909 := by
  unfold tailWord_244854
  simp only [CollatzResearch.WordTrace]
  refine ⟨558159940933953161189351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5953706036628833719353077 558159940933953161189351)
  ·
    refine ⟨837239911400929741784027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 558159940933953161189351 837239911400929741784027)
    ·
      refine ⟨1255859867101394612676041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 837239911400929741784027 1255859867101394612676041)
      ·
        refine ⟨941894900326045959507031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1255859867101394612676041 941894900326045959507031)
        ·
          refine ⟨1412842350489068939260547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 941894900326045959507031 1412842350489068939260547)
          ·
            refine ⟨2119263525733603408890821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1412842350489068939260547 2119263525733603408890821)
            ·
              refine ⟨397361911075050639167029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2119263525733603408890821 397361911075050639167029)
              ·
                refine ⟨37252679163285997421909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 397361911075050639167029 37252679163285997421909)
                ·
                  rfl

theorem cell20_244854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_244854 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_244854 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_244854 prefixEnd_244854 := by exact prefixLift 244854
  have htrace : WordTrace (prefixWord ++ tailWord_244854) baseStart_244854 baseEnd_244854 := by
    simpa [prefixWord, tailWord_244854, baseEnd_244854] using wordTrace_append hprefix tailTrace_244854
  have hstable : (prefixWord ++ tailWord_244854).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244854).length < 2 ^ (prefixWord ++ tailWord_244854).sum := by decide
  have hdescent : baseEnd_244854 < baseStart_244854 := by decide
  rcases family_descends (prefixWord ++ tailWord_244854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244857 : List Nat := [1, 2, 1, 3, 5, 2, 2, 1, 3]
def baseStart_244857 : Nat := 118140960795 + 244857 * 2 ^ 59
def prefixEnd_244857 : Nat := 4983230072969 + 3 ^ 40 * 244857 * 2
def baseEnd_244857 : Nat := 111759406771603315165715

theorem tailTrace_244857 : CollatzResearch.WordTrace tailWord_244857 prefixEnd_244857 111759406771603315165715 := by
  unfold tailWord_244857
  simp only [CollatzResearch.WordTrace]
  refine ⟨8930668473932382091388825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5953778982621588060925883 8930668473932382091388825)
  ·
    refine ⟨6698001355449286568541619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8930668473932382091388825 6698001355449286568541619)
    ·
      refine ⟨10047002033173929852812429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6698001355449286568541619 10047002033173929852812429)
      ·
        refine ⟨3767625762440223694804661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10047002033173929852812429 3767625762440223694804661)
        ·
          refine ⟨353214915228770971387937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3767625762440223694804661 353214915228770971387937)
          ·
            refine ⟨264911186421578228540953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 353214915228770971387937 264911186421578228540953)
            ·
              refine ⟨198683389816183671405715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264911186421578228540953 198683389816183671405715)
              ·
                refine ⟨298025084724275507108573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198683389816183671405715 298025084724275507108573)
                ·
                  refine ⟨111759406771603315165715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 298025084724275507108573 111759406771603315165715)
                  ·
                    rfl

theorem cell20_244857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 2, 1, 3].length) (baseStart_244857 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_244857 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_244857 prefixEnd_244857 := by exact prefixLift 244857
  have htrace : WordTrace (prefixWord ++ tailWord_244857) baseStart_244857 baseEnd_244857 := by
    simpa [prefixWord, tailWord_244857, baseEnd_244857] using wordTrace_append hprefix tailTrace_244857
  have hstable : (prefixWord ++ tailWord_244857).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244857).length < 2 ^ (prefixWord ++ tailWord_244857).sum := by decide
  have hdescent : baseEnd_244857 < baseStart_244857 := by decide
  rcases family_descends (prefixWord ++ tailWord_244857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244861 : List Nat := [1, 4, 1, 1, 3, 1, 3, 3, 3]
def baseStart_244861 : Nat := 118140960795 + 244861 * 2 ^ 59
def prefixEnd_244861 : Nat := 4983230072969 + 3 ^ 40 * 244861 * 2
def baseEnd_244861 : Nat := 111761232480597079032365

theorem tailTrace_244861 : CollatzResearch.WordTrace tailWord_244861 prefixEnd_244861 111761232480597079032365 := by
  unfold tailWord_244861
  simp only [CollatzResearch.WordTrace]
  refine ⟨8930814365917890774534437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5953876243945260516356291 8930814365917890774534437)
  ·
    refine ⟨1674527693609604520225207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8930814365917890774534437 1674527693609604520225207)
    ·
      refine ⟨2511791540414406780337811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1674527693609604520225207 2511791540414406780337811)
      ·
        refine ⟨3767687310621610170506717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2511791540414406780337811 3767687310621610170506717)
        ·
          refine ⟨1412882741483103813940019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3767687310621610170506717 1412882741483103813940019)
          ·
            refine ⟨2119324112224655720910029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1412882741483103813940019 2119324112224655720910029)
            ·
              refine ⟨794746542084245895341261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2119324112224655720910029 794746542084245895341261)
              ·
                refine ⟨298029953281592210752973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 794746542084245895341261 298029953281592210752973)
                ·
                  refine ⟨111761232480597079032365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 298029953281592210752973 111761232480597079032365)
                  ·
                    rfl

theorem cell20_244861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 3, 3].length) (baseStart_244861 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_244861 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_244861 prefixEnd_244861 := by exact prefixLift 244861
  have htrace : WordTrace (prefixWord ++ tailWord_244861) baseStart_244861 baseEnd_244861 := by
    simpa [prefixWord, tailWord_244861, baseEnd_244861] using wordTrace_append hprefix tailTrace_244861
  have hstable : (prefixWord ++ tailWord_244861).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244861).length < 2 ^ (prefixWord ++ tailWord_244861).sum := by decide
  have hdescent : baseEnd_244861 < baseStart_244861 := by decide
  rcases family_descends (prefixWord ++ tailWord_244861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244898 : List Nat := [3, 3, 1, 3, 2, 2, 2, 2, 2]
def baseStart_244898 : Nat := 118140960795 + 244898 * 2 ^ 59
def prefixEnd_244898 : Nat := 4983230072969 + 3 ^ 40 * 244898 * 2
def baseEnd_244898 : Nat := 111778120288789394798881

theorem tailTrace_244898 : CollatzResearch.WordTrace tailWord_244898 prefixEnd_244898 111778120288789394798881 := by
  unfold tailWord_244898
  simp only [CollatzResearch.WordTrace]
  refine ⟨2233040966695961523407837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5954775911189230729087565 2233040966695961523407837)
  ·
    refine ⟨837390362510985571277939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2233040966695961523407837 837390362510985571277939)
    ·
      refine ⟨1256085543766478356916909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 837390362510985571277939 1256085543766478356916909)
      ·
        refine ⟨471032078912429383843841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1256085543766478356916909 471032078912429383843841)
        ·
          refine ⟨353274059184322037882881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 471032078912429383843841 353274059184322037882881)
          ·
            refine ⟨264955544388241528412161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 353274059184322037882881 264955544388241528412161)
            ·
              refine ⟨198716658291181146309121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264955544388241528412161 198716658291181146309121)
              ·
                refine ⟨149037493718385859731841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 198716658291181146309121 149037493718385859731841)
                ·
                  refine ⟨111778120288789394798881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 149037493718385859731841 111778120288789394798881)
                  ·
                    rfl

theorem cell20_244898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 2, 2, 2].length) (baseStart_244898 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_244898 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_244898 prefixEnd_244898 := by exact prefixLift 244898
  have htrace : WordTrace (prefixWord ++ tailWord_244898) baseStart_244898 baseEnd_244898 := by
    simpa [prefixWord, tailWord_244898, baseEnd_244898] using wordTrace_append hprefix tailTrace_244898
  have hstable : (prefixWord ++ tailWord_244898).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244898).length < 2 ^ (prefixWord ++ tailWord_244898).sum := by decide
  have hdescent : baseEnd_244898 < baseStart_244898 := by decide
  rcases family_descends (prefixWord ++ tailWord_244898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244909 : List Nat := [1, 5, 2, 1, 3, 2, 1, 5]
def baseStart_244909 : Nat := 118140960795 + 244909 * 2 ^ 59
def prefixEnd_244909 : Nat := 4983230072969 + 3 ^ 40 * 244909 * 2
def baseEnd_244909 : Nat := 37261046996174081810723

theorem tailTrace_244909 : CollatzResearch.WordTrace tailWord_244909 prefixEnd_244909 37261046996174081810723 := by
  unfold tailWord_244909
  simp only [CollatzResearch.WordTrace]
  refine ⟨8932565069743994972281781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5955043379829329981521187 8932565069743994972281781)
  ·
    refine ⟨837427975288499528651417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8932565069743994972281781 837427975288499528651417)
    ·
      refine ⟨628070981466374646488563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 837427975288499528651417 628070981466374646488563)
      ·
        refine ⟨942106472199561969732845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 628070981466374646488563 942106472199561969732845)
        ·
          refine ⟨353289927074835738649817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 942106472199561969732845 353289927074835738649817)
          ·
            refine ⟨264967445306126803987363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 353289927074835738649817 264967445306126803987363)
            ·
              refine ⟨397451167959190205981045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264967445306126803987363 397451167959190205981045)
              ·
                refine ⟨37261046996174081810723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 397451167959190205981045 37261046996174081810723)
                ·
                  rfl

theorem cell20_244909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 5].length) (baseStart_244909 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_244909 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_244909 prefixEnd_244909 := by exact prefixLift 244909
  have htrace : WordTrace (prefixWord ++ tailWord_244909) baseStart_244909 baseEnd_244909 := by
    simpa [prefixWord, tailWord_244909, baseEnd_244909] using wordTrace_append hprefix tailTrace_244909
  have hstable : (prefixWord ++ tailWord_244909).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244909).length < 2 ^ (prefixWord ++ tailWord_244909).sum := by decide
  have hdescent : baseEnd_244909 < baseStart_244909 := by decide
  rcases family_descends (prefixWord ++ tailWord_244909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244927 : List Nat := [1, 1, 2, 2, 2, 2, 3, 1, 6]
def baseStart_244927 : Nat := 118140960795 + 244927 * 2 ^ 59
def prefixEnd_244927 : Nat := 4983230072969 + 3 ^ 40 * 244927 * 2
def baseEnd_244927 : Nat := 111791356678994182832095

theorem tailTrace_244927 : CollatzResearch.WordTrace tailWord_244927 prefixEnd_244927 111791356678994182832095 := by
  unfold tailWord_244927
  simp only [CollatzResearch.WordTrace]
  refine ⟨8933221583678784046437035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5955481055785856030958023 8933221583678784046437035)
  ·
    refine ⟨13399832375518176069655553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8933221583678784046437035 13399832375518176069655553)
    ·
      refine ⟨10049874281638632052241665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13399832375518176069655553 10049874281638632052241665)
      ·
        refine ⟨7537405711228974039181249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10049874281638632052241665 7537405711228974039181249)
        ·
          refine ⟨5653054283421730529385937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7537405711228974039181249 5653054283421730529385937)
          ·
            refine ⟨4239790712566297897039453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5653054283421730529385937 4239790712566297897039453)
            ·
              refine ⟨1589921517212361711389795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4239790712566297897039453 1589921517212361711389795)
              ·
                refine ⟨2384882275818542567084693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1589921517212361711389795 2384882275818542567084693)
                ·
                  refine ⟨111791356678994182832095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2384882275818542567084693 111791356678994182832095)
                  ·
                    rfl

theorem cell20_244927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 6].length) (baseStart_244927 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_244927 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_244927 prefixEnd_244927 := by exact prefixLift 244927
  have htrace : WordTrace (prefixWord ++ tailWord_244927) baseStart_244927 baseEnd_244927 := by
    simpa [prefixWord, tailWord_244927, baseEnd_244927] using wordTrace_append hprefix tailTrace_244927
  have hstable : (prefixWord ++ tailWord_244927).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244927).length < 2 ^ (prefixWord ++ tailWord_244927).sum := by decide
  have hdescent : baseEnd_244927 < baseStart_244927 := by decide
  rcases family_descends (prefixWord ++ tailWord_244927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244950 : List Nat := [5, 2, 1, 2, 2, 2, 1, 2, 3]
def baseStart_244950 : Nat := 118140960795 + 244950 * 2 ^ 59
def prefixEnd_244950 : Nat := 4983230072969 + 3 ^ 40 * 244950 * 2
def baseEnd_244950 : Nat := 111801854505708325065335

theorem tailTrace_244950 : CollatzResearch.WordTrace tailWord_244950 prefixEnd_244950 111801854505708325065335 := by
  unfold tailWord_244950
  simp only [CollatzResearch.WordTrace]
  refine ⟨558378778912216185907769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5956040308396972649682869 558378778912216185907769)
  ·
    refine ⟨418784084184162139430827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 558378778912216185907769 418784084184162139430827)
    ·
      refine ⟨628176126276243209146241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418784084184162139430827 628176126276243209146241)
      ·
        refine ⟨471132094707182406859681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 628176126276243209146241 471132094707182406859681)
        ·
          refine ⟨353349071030386805144761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 471132094707182406859681 353349071030386805144761)
          ·
            refine ⟨265011803272790103858571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 353349071030386805144761 265011803272790103858571)
            ·
              refine ⟨397517704909185155787857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265011803272790103858571 397517704909185155787857)
              ·
                refine ⟨298138278681888866840893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 397517704909185155787857 298138278681888866840893)
                ·
                  refine ⟨111801854505708325065335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 298138278681888866840893 111801854505708325065335)
                  ·
                    rfl

theorem cell20_244950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_244950 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_244950 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_244950 prefixEnd_244950 := by exact prefixLift 244950
  have htrace : WordTrace (prefixWord ++ tailWord_244950) baseStart_244950 baseEnd_244950 := by
    simpa [prefixWord, tailWord_244950, baseEnd_244950] using wordTrace_append hprefix tailTrace_244950
  have hstable : (prefixWord ++ tailWord_244950).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244950).length < 2 ^ (prefixWord ++ tailWord_244950).sum := by decide
  have hdescent : baseEnd_244950 < baseStart_244950 := by decide
  rcases family_descends (prefixWord ++ tailWord_244950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_244961 : List Nat := [1, 2, 3, 1, 3, 2, 2, 4, 2]
def baseStart_244961 : Nat := 118140960795 + 244961 * 2 ^ 59
def prefixEnd_244961 : Nat := 4983230072969 + 3 ^ 40 * 244961 * 2
def baseEnd_244961 : Nat := 111806875205441175698623

theorem tailTrace_244961 : CollatzResearch.WordTrace tailWord_244961 prefixEnd_244961 111806875205441175698623 := by
  unfold tailWord_244961
  simp only [CollatzResearch.WordTrace]
  refine ⟨8934461665555607853174737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5956307777037071902116491 8934461665555607853174737)
  ·
    refine ⟨6700846249166705889881053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8934461665555607853174737 6700846249166705889881053)
    ·
      refine ⟨2512817343437514708705395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6700846249166705889881053 2512817343437514708705395)
      ·
        refine ⟨3769226015156272063058093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2512817343437514708705395 3769226015156272063058093)
        ·
          refine ⟨1413459755683602023646785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3769226015156272063058093 1413459755683602023646785)
          ·
            refine ⟨1060094816762701517735089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1413459755683602023646785 1060094816762701517735089)
            ·
              refine ⟨795071112572026138301317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1060094816762701517735089 795071112572026138301317)
              ·
                refine ⟨149075833607254900931497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 795071112572026138301317 149075833607254900931497)
                ·
                  refine ⟨111806875205441175698623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 149075833607254900931497 111806875205441175698623)
                  ·
                    rfl

theorem cell20_244961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 4, 2].length) (baseStart_244961 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_244961 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_244961 prefixEnd_244961 := by exact prefixLift 244961
  have htrace : WordTrace (prefixWord ++ tailWord_244961) baseStart_244961 baseEnd_244961 := by
    simpa [prefixWord, tailWord_244961, baseEnd_244961] using wordTrace_append hprefix tailTrace_244961
  have hstable : (prefixWord ++ tailWord_244961).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_244961).length < 2 ^ (prefixWord ++ tailWord_244961).sum := by decide
  have hdescent : baseEnd_244961 < baseStart_244961 := by decide
  rcases family_descends (prefixWord ++ tailWord_244961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245016 : List Nat := [2, 1, 2, 3, 1, 4, 3, 2, 2]
def baseStart_245016 : Nat := 118140960795 + 245016 * 2 ^ 59
def prefixEnd_245016 : Nat := 4983230072969 + 3 ^ 40 * 245016 * 2
def baseEnd_245016 : Nat := 111831978704105428865065

theorem tailTrace_245016 : CollatzResearch.WordTrace tailWord_245016 prefixEnd_245016 111831978704105428865065 := by
  unfold tailWord_245016
  simp only [CollatzResearch.WordTrace]
  refine ⟨4468233840178176123213451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5957645120237568164284601 4468233840178176123213451)
  ·
    refine ⟨6702350760267264184820177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4468233840178176123213451 6702350760267264184820177)
    ·
      refine ⟨5026763070200448138615133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6702350760267264184820177 5026763070200448138615133)
      ·
        refine ⟨1885036151325168051980675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5026763070200448138615133 1885036151325168051980675)
        ·
          refine ⟨2827554226987752077971013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1885036151325168051980675 2827554226987752077971013)
          ·
            refine ⟨530166417560203514619565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2827554226987752077971013 530166417560203514619565)
            ·
              refine ⟨198812406585076317982337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 530166417560203514619565 198812406585076317982337)
              ·
                refine ⟨149109304938807238486753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 198812406585076317982337 149109304938807238486753)
                ·
                  refine ⟨111831978704105428865065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 149109304938807238486753 111831978704105428865065)
                  ·
                    rfl

theorem cell20_245016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 3, 2, 2].length) (baseStart_245016 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_245016 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_245016 prefixEnd_245016 := by exact prefixLift 245016
  have htrace : WordTrace (prefixWord ++ tailWord_245016) baseStart_245016 baseEnd_245016 := by
    simpa [prefixWord, tailWord_245016, baseEnd_245016] using wordTrace_append hprefix tailTrace_245016
  have hstable : (prefixWord ++ tailWord_245016).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245016).length < 2 ^ (prefixWord ++ tailWord_245016).sum := by decide
  have hdescent : baseEnd_245016 < baseStart_245016 := by decide
  rcases family_descends (prefixWord ++ tailWord_245016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245020 : List Nat := [2, 2, 3, 1, 1, 1, 5, 1, 4]
def baseStart_245020 : Nat := 118140960795 + 245020 * 2 ^ 59
def prefixEnd_245020 : Nat := 4983230072969 + 3 ^ 40 * 245020 * 2
def baseEnd_245020 : Nat := 111833804413099192731715

theorem tailTrace_245020 : CollatzResearch.WordTrace tailWord_245020 prefixEnd_245020 111833804413099192731715 := by
  unfold tailWord_245020
  simp only [CollatzResearch.WordTrace]
  refine ⟨4468306786170930464786257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5957742381561240619715009 4468306786170930464786257)
  ·
    refine ⟨3351230089628197848589693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4468306786170930464786257 3351230089628197848589693)
    ·
      refine ⟨1256711283610574193221135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3351230089628197848589693 1256711283610574193221135)
      ·
        refine ⟨1885066925415861289831703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1256711283610574193221135 1885066925415861289831703)
        ·
          refine ⟨2827600388123791934747555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1885066925415861289831703 2827600388123791934747555)
          ·
            refine ⟨4241400582185687902121333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2827600388123791934747555 4241400582185687902121333)
            ·
              refine ⟨397631304579908240823875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4241400582185687902121333 397631304579908240823875)
              ·
                refine ⟨596446956869862361235813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 397631304579908240823875 596446956869862361235813)
                ·
                  refine ⟨111833804413099192731715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 596446956869862361235813 111833804413099192731715)
                  ·
                    rfl

theorem cell20_245020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 1, 4].length) (baseStart_245020 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_245020 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_245020 prefixEnd_245020 := by exact prefixLift 245020
  have htrace : WordTrace (prefixWord ++ tailWord_245020) baseStart_245020 baseEnd_245020 := by
    simpa [prefixWord, tailWord_245020, baseEnd_245020] using wordTrace_append hprefix tailTrace_245020
  have hstable : (prefixWord ++ tailWord_245020).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245020).length < 2 ^ (prefixWord ++ tailWord_245020).sum := by decide
  have hdescent : baseEnd_245020 < baseStart_245020 := by decide
  rcases family_descends (prefixWord ++ tailWord_245020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245026 : List Nat := [3, 3, 1, 1, 5, 1, 2, 1, 3]
def baseStart_245026 : Nat := 118140960795 + 245026 * 2 ^ 59
def prefixEnd_245026 : Nat := 4983230072969 + 3 ^ 40 * 245026 * 2
def baseEnd_245026 : Nat := 111836542976589838531691

theorem tailTrace_245026 : CollatzResearch.WordTrace tailWord_245026 prefixEnd_245026 111836542976589838531691 := by
  unfold tailWord_245026
  simp only [CollatzResearch.WordTrace]
  refine ⟨2234208102580030988572733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5957888273546749302860621 2234208102580030988572733)
  ·
    refine ⟨837828038467511620714775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2234208102580030988572733 837828038467511620714775)
    ·
      refine ⟨1256742057701267431072163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 837828038467511620714775 1256742057701267431072163)
      ·
        refine ⟨1885113086551901146608245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1256742057701267431072163 1885113086551901146608245)
        ·
          refine ⟨176729351864240732494523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1885113086551901146608245 176729351864240732494523)
          ·
            refine ⟨265094027796361098741785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176729351864240732494523 265094027796361098741785)
            ·
              refine ⟨198820520847270824056339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 265094027796361098741785 198820520847270824056339)
              ·
                refine ⟨298230781270906236084509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198820520847270824056339 298230781270906236084509)
                ·
                  refine ⟨111836542976589838531691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 298230781270906236084509 111836542976589838531691)
                  ·
                    rfl

theorem cell20_245026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 2, 1, 3].length) (baseStart_245026 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_245026 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_245026 prefixEnd_245026 := by exact prefixLift 245026
  have htrace : WordTrace (prefixWord ++ tailWord_245026) baseStart_245026 baseEnd_245026 := by
    simpa [prefixWord, tailWord_245026, baseEnd_245026] using wordTrace_append hprefix tailTrace_245026
  have hstable : (prefixWord ++ tailWord_245026).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245026).length < 2 ^ (prefixWord ++ tailWord_245026).sum := by decide
  have hdescent : baseEnd_245026 < baseStart_245026 := by decide
  rcases family_descends (prefixWord ++ tailWord_245026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245027 : List Nat := [1, 1, 1, 4, 2, 4, 2, 5]
def baseStart_245027 : Nat := 118140960795 + 245027 * 2 ^ 59
def prefixEnd_245027 : Nat := 4983230072969 + 3 ^ 40 * 245027 * 2
def baseEnd_245027 : Nat := 37278999801279426499451

theorem tailTrace_245027 : CollatzResearch.WordTrace tailWord_245027 prefixEnd_245027 37278999801279426499451 := by
  unfold tailWord_245027
  simp only [CollatzResearch.WordTrace]
  refine ⟨8936868883316501125077335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5957912588877667416718223 8936868883316501125077335)
  ·
    refine ⟨13405303324974751687616003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8936868883316501125077335 13405303324974751687616003)
    ·
      refine ⟨20107954987462127531424005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13405303324974751687616003 20107954987462127531424005)
      ·
        refine ⟨3770241560149148912142001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20107954987462127531424005 3770241560149148912142001)
        ·
          refine ⟨2827681170111861684106501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3770241560149148912142001 2827681170111861684106501)
          ·
            refine ⟨530190219395974065769969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2827681170111861684106501 530190219395974065769969)
            ·
              refine ⟨397642664546980549327477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 530190219395974065769969 397642664546980549327477)
              ·
                refine ⟨37278999801279426499451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 397642664546980549327477 37278999801279426499451)
                ·
                  rfl

theorem cell20_245027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 5].length) (baseStart_245027 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_245027 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_245027 prefixEnd_245027 := by exact prefixLift 245027
  have htrace : WordTrace (prefixWord ++ tailWord_245027) baseStart_245027 baseEnd_245027 := by
    simpa [prefixWord, tailWord_245027, baseEnd_245027] using wordTrace_append hprefix tailTrace_245027
  have hstable : (prefixWord ++ tailWord_245027).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245027).length < 2 ^ (prefixWord ++ tailWord_245027).sum := by decide
  have hdescent : baseEnd_245027 < baseStart_245027 := by decide
  rcases family_descends (prefixWord ++ tailWord_245027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245103 : List Nat := [1, 1, 2, 1, 3, 1, 7, 4]
def baseStart_245103 : Nat := 118140960795 + 245103 * 2 ^ 59
def prefixEnd_245103 : Nat := 4983230072969 + 3 ^ 40 * 245103 * 2
def baseEnd_245103 : Nat := 37290562624906597654903

theorem tailTrace_245103 : CollatzResearch.WordTrace tailWord_245103 prefixEnd_245103 37290562624906597654903 := by
  unfold tailWord_245103
  simp only [CollatzResearch.WordTrace]
  refine ⟨8939640831041166104843963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5959760554027444069895975 8939640831041166104843963)
  ·
    refine ⟨13409461246561749157265945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8939640831041166104843963 13409461246561749157265945)
    ·
      refine ⟨10057095934921311867949459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13409461246561749157265945 10057095934921311867949459)
      ·
        refine ⟨15085643902381967801924189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10057095934921311867949459 15085643902381967801924189)
        ·
          refine ⟨5657116463393237925721571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15085643902381967801924189 5657116463393237925721571)
          ·
            refine ⟨8485674695089856888582357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5657116463393237925721571 8485674695089856888582357)
            ·
              refine ⟨198883000666168520826149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 8485674695089856888582357 198883000666168520826149)
              ·
                refine ⟨37290562624906597654903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 198883000666168520826149 37290562624906597654903)
                ·
                  rfl

theorem cell20_245103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 7, 4].length) (baseStart_245103 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_245103 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_245103 prefixEnd_245103 := by exact prefixLift 245103
  have htrace : WordTrace (prefixWord ++ tailWord_245103) baseStart_245103 baseEnd_245103 := by
    simpa [prefixWord, tailWord_245103, baseEnd_245103] using wordTrace_append hprefix tailTrace_245103
  have hstable : (prefixWord ++ tailWord_245103).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245103).length < 2 ^ (prefixWord ++ tailWord_245103).sum := by decide
  have hdescent : baseEnd_245103 < baseStart_245103 := by decide
  rcases family_descends (prefixWord ++ tailWord_245103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245117 : List Nat := [1, 4, 1, 1, 2, 2, 1, 2, 6]
def baseStart_245117 : Nat := 118140960795 + 245117 * 2 ^ 59
def prefixEnd_245117 : Nat := 4983230072969 + 3 ^ 40 * 245117 * 2
def baseEnd_245117 : Nat := 111878077856197966497985

theorem tailTrace_245117 : CollatzResearch.WordTrace tailWord_245117 prefixEnd_245117 111878077856197966497985 := by
  unfold tailWord_245117
  simp only [CollatzResearch.WordTrace]
  refine ⟨8940151452990446495853605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5960100968660297663902403 8940151452990446495853605)
  ·
    refine ⟨1676278397435708717972551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8940151452990446495853605 1676278397435708717972551)
    ·
      refine ⟨2514417596153563076958827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1676278397435708717972551 2514417596153563076958827)
      ·
        refine ⟨3771626394230344615438241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2514417596153563076958827 3771626394230344615438241)
        ·
          refine ⟨2828719795672758461578681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3771626394230344615438241 2828719795672758461578681)
          ·
            refine ⟨2121539846754568846184011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2828719795672758461578681 2121539846754568846184011)
            ·
              refine ⟨3182309770131853269276017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2121539846754568846184011 3182309770131853269276017)
              ·
                refine ⟨2386732327598889951957013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3182309770131853269276017 2386732327598889951957013)
                ·
                  refine ⟨111878077856197966497985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2386732327598889951957013 111878077856197966497985)
                  ·
                    rfl

theorem cell20_245117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_245117 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_245117 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_245117 prefixEnd_245117 := by exact prefixLift 245117
  have htrace : WordTrace (prefixWord ++ tailWord_245117) baseStart_245117 baseEnd_245117 := by
    simpa [prefixWord, tailWord_245117, baseEnd_245117] using wordTrace_append hprefix tailTrace_245117
  have hstable : (prefixWord ++ tailWord_245117).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245117).length < 2 ^ (prefixWord ++ tailWord_245117).sum := by decide
  have hdescent : baseEnd_245117 < baseStart_245117 := by decide
  rcases family_descends (prefixWord ++ tailWord_245117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245127 : List Nat := [1, 1, 4, 2, 2, 2, 3, 2, 3]
def baseStart_245127 : Nat := 118140960795 + 245127 * 2 ^ 59
def prefixEnd_245127 : Nat := 4983230072969 + 3 ^ 40 * 245127 * 2
def baseEnd_245127 : Nat := 111882642128682376164611

theorem tailTrace_245127 : CollatzResearch.WordTrace tailWord_245127 prefixEnd_245127 111882642128682376164611 := by
  unfold tailWord_245127
  simp only [CollatzResearch.WordTrace]
  refine ⟨8940516182954218203717635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5960344121969478802478423 8940516182954218203717635)
  ·
    refine ⟨13410774274431327305576453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8940516182954218203717635 13410774274431327305576453)
    ·
      refine ⟨2514520176455873869795585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13410774274431327305576453 2514520176455873869795585)
      ·
        refine ⟨1885890132341905402346689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2514520176455873869795585 1885890132341905402346689)
        ·
          refine ⟨1414417599256429051760017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1885890132341905402346689 1414417599256429051760017)
          ·
            refine ⟨1060813199442321788820013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1414417599256429051760017 1060813199442321788820013)
            ·
              refine ⟨397804949790870670807505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1060813199442321788820013 397804949790870670807505)
              ·
                refine ⟨298353712343153003105629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 397804949790870670807505 298353712343153003105629)
                ·
                  refine ⟨111882642128682376164611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 298353712343153003105629 111882642128682376164611)
                  ·
                    rfl

theorem cell20_245127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 2, 3].length) (baseStart_245127 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_245127 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_245127 prefixEnd_245127 := by exact prefixLift 245127
  have htrace : WordTrace (prefixWord ++ tailWord_245127) baseStart_245127 baseEnd_245127 := by
    simpa [prefixWord, tailWord_245127, baseEnd_245127] using wordTrace_append hprefix tailTrace_245127
  have hstable : (prefixWord ++ tailWord_245127).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245127).length < 2 ^ (prefixWord ++ tailWord_245127).sum := by decide
  have hdescent : baseEnd_245127 < baseStart_245127 := by decide
  rcases family_descends (prefixWord ++ tailWord_245127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245155 : List Nat := [1, 1, 1, 4, 1, 3, 1, 4, 4]
def baseStart_245155 : Nat := 118140960795 + 245155 * 2 ^ 59
def prefixEnd_245155 : Nat := 4983230072969 + 3 ^ 40 * 245155 * 2
def baseEnd_245155 : Nat := 111895422091638723231163

theorem tailTrace_245155 : CollatzResearch.WordTrace tailWord_245155 prefixEnd_245155 111895422091638723231163 := by
  unfold tailWord_245155
  simp only [CollatzResearch.WordTrace]
  refine ⟨8941537426852778985736919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5961024951235185990491279 8941537426852778985736919)
  ·
    refine ⟨13412306140279168478605379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8941537426852778985736919 13412306140279168478605379)
    ·
      refine ⟨20118459210418752717908069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13412306140279168478605379 20118459210418752717908069)
      ·
        refine ⟨3772211101953516134607763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20118459210418752717908069 3772211101953516134607763)
        ·
          refine ⟨5658316652930274201911645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3772211101953516134607763 5658316652930274201911645)
          ·
            refine ⟨2121868744848852825716867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5658316652930274201911645 2121868744848852825716867)
            ·
              refine ⟨3182803117273279238575301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2121868744848852825716867 3182803117273279238575301)
              ·
                refine ⟨596775584488739857232869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3182803117273279238575301 596775584488739857232869)
                ·
                  refine ⟨111895422091638723231163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 596775584488739857232869 111895422091638723231163)
                  ·
                    rfl

theorem cell20_245155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 4, 4].length) (baseStart_245155 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_245155 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_245155 prefixEnd_245155 := by exact prefixLift 245155
  have htrace : WordTrace (prefixWord ++ tailWord_245155) baseStart_245155 baseEnd_245155 := by
    simpa [prefixWord, tailWord_245155, baseEnd_245155] using wordTrace_append hprefix tailTrace_245155
  have hstable : (prefixWord ++ tailWord_245155).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245155).length < 2 ^ (prefixWord ++ tailWord_245155).sum := by decide
  have hdescent : baseEnd_245155 < baseStart_245155 := by decide
  rcases family_descends (prefixWord ++ tailWord_245155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245165 : List Nat := [1, 5, 2, 2, 1, 1, 1, 2, 5]
def baseStart_245165 : Nat := 118140960795 + 245165 * 2 ^ 59
def prefixEnd_245165 : Nat := 4983230072969 + 3 ^ 40 * 245165 * 2
def baseEnd_245165 : Nat := 111899986364123132897789

theorem tailTrace_245165 : CollatzResearch.WordTrace tailWord_245165 prefixEnd_245165 111899986364123132897789 := by
  unfold tailWord_245165
  simp only [CollatzResearch.WordTrace]
  refine ⟨8941902156816550693600949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5961268104544367129067299 8941902156816550693600949)
  ·
    refine ⟨838303327201551627525089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8941902156816550693600949 838303327201551627525089)
    ·
      refine ⟨628727495401163720643817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 838303327201551627525089 628727495401163720643817)
      ·
        refine ⟨471545621550872790482863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 628727495401163720643817 471545621550872790482863)
        ·
          refine ⟨707318432326309185724295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 471545621550872790482863 707318432326309185724295)
          ·
            refine ⟨1060977648489463778586443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 707318432326309185724295 1060977648489463778586443)
            ·
              refine ⟨1591466472734195667879665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1060977648489463778586443 1591466472734195667879665)
              ·
                refine ⟨1193599854550646750909749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1591466472734195667879665 1193599854550646750909749)
                ·
                  refine ⟨111899986364123132897789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1193599854550646750909749 111899986364123132897789)
                  ·
                    rfl

theorem cell20_245165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_245165 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_245165 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_245165 prefixEnd_245165 := by exact prefixLift 245165
  have htrace : WordTrace (prefixWord ++ tailWord_245165) baseStart_245165 baseEnd_245165 := by
    simpa [prefixWord, tailWord_245165, baseEnd_245165] using wordTrace_append hprefix tailTrace_245165
  have hstable : (prefixWord ++ tailWord_245165).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245165).length < 2 ^ (prefixWord ++ tailWord_245165).sum := by decide
  have hdescent : baseEnd_245165 < baseStart_245165 := by decide
  rcases family_descends (prefixWord ++ tailWord_245165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245255 : List Nat := [1, 1, 4, 3, 2, 1, 3, 5]
def baseStart_245255 : Nat := 118140960795 + 245255 * 2 ^ 59
def prefixEnd_245255 : Nat := 4983230072969 + 3 ^ 40 * 245255 * 2
def baseEnd_245255 : Nat := 37313688272160939965807

theorem tailTrace_245255 : CollatzResearch.WordTrace tailWord_245255 prefixEnd_245255 37313688272160939965807 := by
  unfold tailWord_245255
  simp only [CollatzResearch.WordTrace]
  refine ⟨8945184726490496064377219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5963456484326997376251479 8945184726490496064377219)
  ·
    refine ⟨13417777089735744096565829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8945184726490496064377219 13417777089735744096565829)
    ·
      refine ⟨2515833204325452018106093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13417777089735744096565829 2515833204325452018106093)
      ·
        refine ⟨943437451622044506789785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2515833204325452018106093 943437451622044506789785)
        ·
          refine ⟨707578088716533380092339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 943437451622044506789785 707578088716533380092339)
          ·
            refine ⟨1061367133074800070138509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 707578088716533380092339 1061367133074800070138509)
            ·
              refine ⟨398012674903050026301941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1061367133074800070138509 398012674903050026301941)
              ·
                refine ⟨37313688272160939965807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 398012674903050026301941 37313688272160939965807)
                ·
                  rfl

theorem cell20_245255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 5].length) (baseStart_245255 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_245255 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_245255 prefixEnd_245255 := by exact prefixLift 245255
  have htrace : WordTrace (prefixWord ++ tailWord_245255) baseStart_245255 baseEnd_245255 := by
    simpa [prefixWord, tailWord_245255, baseEnd_245255] using wordTrace_append hprefix tailTrace_245255
  have hstable : (prefixWord ++ tailWord_245255).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245255).length < 2 ^ (prefixWord ++ tailWord_245255).sum := by decide
  have hdescent : baseEnd_245255 < baseStart_245255 := by decide
  rcases family_descends (prefixWord ++ tailWord_245255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245269 : List Nat := [1, 3, 2, 1, 3, 2, 1, 1, 6]
def baseStart_245269 : Nat := 118140960795 + 245269 * 2 ^ 59
def prefixEnd_245269 : Nat := 4983230072969 + 3 ^ 40 * 245269 * 2
def baseEnd_245269 : Nat := 111947454797960993430697

theorem tailTrace_245269 : CollatzResearch.WordTrace tailWord_245269 prefixEnd_245269 111947454797960993430697 := by
  unfold tailWord_245269
  simp only [CollatzResearch.WordTrace]
  refine ⟨8945695348439776455386861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5963796898959850970257907 8945695348439776455386861)
  ·
    refine ⟨3354635755664916170770073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8945695348439776455386861 3354635755664916170770073)
    ·
      refine ⟨2515976816748687128077555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3354635755664916170770073 2515976816748687128077555)
      ·
        refine ⟨3773965225123030692116333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2515976816748687128077555 3773965225123030692116333)
        ·
          refine ⟨1415236959421136509543625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3773965225123030692116333 1415236959421136509543625)
          ·
            refine ⟨1061427719565852382157719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1415236959421136509543625 1061427719565852382157719)
            ·
              refine ⟨1592141579348778573236579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1061427719565852382157719 1592141579348778573236579)
              ·
                refine ⟨2388212369023167859854869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1592141579348778573236579 2388212369023167859854869)
                ·
                  refine ⟨111947454797960993430697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2388212369023167859854869 111947454797960993430697)
                  ·
                    rfl

theorem cell20_245269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 6].length) (baseStart_245269 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_245269 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_245269 prefixEnd_245269 := by exact prefixLift 245269
  have htrace : WordTrace (prefixWord ++ tailWord_245269) baseStart_245269 baseEnd_245269 := by
    simpa [prefixWord, tailWord_245269, baseEnd_245269] using wordTrace_append hprefix tailTrace_245269
  have hstable : (prefixWord ++ tailWord_245269).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245269).length < 2 ^ (prefixWord ++ tailWord_245269).sum := by decide
  have hdescent : baseEnd_245269 < baseStart_245269 := by decide
  rcases family_descends (prefixWord ++ tailWord_245269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245272 : List Nat := [2, 1, 2, 3, 4, 1, 3, 4]
def baseStart_245272 : Nat := 118140960795 + 245272 * 2 ^ 59
def prefixEnd_245272 : Nat := 4983230072969 + 3 ^ 40 * 245272 * 2
def baseEnd_245272 : Nat := 37316274693235438776895

theorem tailTrace_245272 : CollatzResearch.WordTrace tailWord_245272 prefixEnd_245272 37316274693235438776895 := by
  unfold tailWord_245272
  simp only [CollatzResearch.WordTrace]
  refine ⟨4472902383714453983873035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5963869844952605311830713 4472902383714453983873035)
  ·
    refine ⟨6709353575571680975809553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4472902383714453983873035 6709353575571680975809553)
    ·
      refine ⟨5032015181678760731857165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6709353575571680975809553 5032015181678760731857165)
      ·
        refine ⟨1887005693129535274446437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5032015181678760731857165 1887005693129535274446437)
        ·
          refine ⟨353813567461787863958707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1887005693129535274446437 353813567461787863958707)
          ·
            refine ⟨530720351192681795938061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353813567461787863958707 530720351192681795938061)
            ·
              refine ⟨199020131697255673476773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 530720351192681795938061 199020131697255673476773)
              ·
                refine ⟨37316274693235438776895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 199020131697255673476773 37316274693235438776895)
                ·
                  rfl

theorem cell20_245272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 3, 4].length) (baseStart_245272 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_245272 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_245272 prefixEnd_245272 := by exact prefixLift 245272
  have htrace : WordTrace (prefixWord ++ tailWord_245272) baseStart_245272 baseEnd_245272 := by
    simpa [prefixWord, tailWord_245272, baseEnd_245272] using wordTrace_append hprefix tailTrace_245272
  have hstable : (prefixWord ++ tailWord_245272).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245272).length < 2 ^ (prefixWord ++ tailWord_245272).sum := by decide
  have hdescent : baseEnd_245272 < baseStart_245272 := by decide
  rcases family_descends (prefixWord ++ tailWord_245272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245317 : List Nat := [1, 3, 1, 1, 1, 4, 5, 1, 3]
def baseStart_245317 : Nat := 118140960795 + 245317 * 2 ^ 59
def prefixEnd_245317 : Nat := 4983230072969 + 3 ^ 40 * 245317 * 2
def baseEnd_245317 : Nat := 111969363305886159830501

theorem tailTrace_245317 : CollatzResearch.WordTrace tailWord_245317 prefixEnd_245317 111969363305886159830501 := by
  unfold tailWord_245317
  simp only [CollatzResearch.WordTrace]
  refine ⟨8947446052265880653134205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5964964034843920435422803 8947446052265880653134205)
  ·
    refine ⟨3355292269599705244925327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8947446052265880653134205 3355292269599705244925327)
    ·
      refine ⟨5032938404399557867387991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3355292269599705244925327 5032938404399557867387991)
      ·
        refine ⟨7549407606599336801081987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5032938404399557867387991 7549407606599336801081987)
        ·
          refine ⟨11324111409899005201622981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7549407606599336801081987 11324111409899005201622981)
          ·
            refine ⟨2123270889356063475304309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11324111409899005201622981 2123270889356063475304309)
            ·
              refine ⟨199056645877130950809779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2123270889356063475304309 199056645877130950809779)
              ·
                refine ⟨298584968815696426214669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199056645877130950809779 298584968815696426214669)
                ·
                  refine ⟨111969363305886159830501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 298584968815696426214669 111969363305886159830501)
                  ·
                    rfl

theorem cell20_245317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 5, 1, 3].length) (baseStart_245317 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_245317 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_245317 prefixEnd_245317 := by exact prefixLift 245317
  have htrace : WordTrace (prefixWord ++ tailWord_245317) baseStart_245317 baseEnd_245317 := by
    simpa [prefixWord, tailWord_245317, baseEnd_245317] using wordTrace_append hprefix tailTrace_245317
  have hstable : (prefixWord ++ tailWord_245317).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245317).length < 2 ^ (prefixWord ++ tailWord_245317).sum := by decide
  have hdescent : baseEnd_245317 < baseStart_245317 := by decide
  rcases family_descends (prefixWord ++ tailWord_245317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245358 : List Nat := [4, 1, 2, 2, 4, 1, 1, 1, 4]
def baseStart_245358 : Nat := 118140960795 + 245358 * 2 ^ 59
def prefixEnd_245358 : Nat := 4983230072969 + 3 ^ 40 * 245358 * 2
def baseEnd_245358 : Nat := 111988076823072239463667

theorem tailTrace_245358 : CollatzResearch.WordTrace tailWord_245358 prefixEnd_245358 111988076823072239463667 := by
  unfold tailWord_245358
  simp only [CollatzResearch.WordTrace]
  refine ⟨1118617680639668081922091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5965960963411563103584485 1118617680639668081922091)
  ·
    refine ⟨1677926520959502122883137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1118617680639668081922091 1677926520959502122883137)
    ·
      refine ⟨1258444890719626592162353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1677926520959502122883137 1258444890719626592162353)
      ·
        refine ⟨943833668039719944121765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1258444890719626592162353 943833668039719944121765)
        ·
          refine ⟨176968812757447489522831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 943833668039719944121765 176968812757447489522831)
          ·
            refine ⟨265453219136171234284247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176968812757447489522831 265453219136171234284247)
            ·
              refine ⟨398179828704256851426371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265453219136171234284247 398179828704256851426371)
              ·
                refine ⟨597269743056385277139557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 398179828704256851426371 597269743056385277139557)
                ·
                  refine ⟨111988076823072239463667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 597269743056385277139557 111988076823072239463667)
                  ·
                    rfl

theorem cell20_245358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 1, 4].length) (baseStart_245358 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_245358 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_245358 prefixEnd_245358 := by exact prefixLift 245358
  have htrace : WordTrace (prefixWord ++ tailWord_245358) baseStart_245358 baseEnd_245358 := by
    simpa [prefixWord, tailWord_245358, baseEnd_245358] using wordTrace_append hprefix tailTrace_245358
  have hstable : (prefixWord ++ tailWord_245358).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245358).length < 2 ^ (prefixWord ++ tailWord_245358).sum := by decide
  have hdescent : baseEnd_245358 < baseStart_245358 := by decide
  rcases family_descends (prefixWord ++ tailWord_245358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245362 : List Nat := [3, 2, 1, 2, 3, 1, 3, 1, 4]
def baseStart_245362 : Nat := 118140960795 + 245362 * 2 ^ 59
def prefixEnd_245362 : Nat := 4983230072969 + 3 ^ 40 * 245362 * 2
def baseEnd_245362 : Nat := 111989902532066003330317

theorem tailTrace_245362 : CollatzResearch.WordTrace tailWord_245362 prefixEnd_245362 111989902532066003330317 := by
  unfold tailWord_245362
  simp only [CollatzResearch.WordTrace]
  refine ⟨2237271834275713334630585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5966058224735235559014893 2237271834275713334630585)
  ·
    refine ⟨1677953875706785000972939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2237271834275713334630585 1677953875706785000972939)
    ·
      refine ⟨2516930813560177501459409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1677953875706785000972939 2516930813560177501459409)
      ·
        refine ⟨1887698110170133126094557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2516930813560177501459409 1887698110170133126094557)
        ·
          refine ⟨707886791313799922285459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1887698110170133126094557 707886791313799922285459)
          ·
            refine ⟨1061830186970699883428189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 707886791313799922285459 1061830186970699883428189)
            ·
              refine ⟨398186320114012456285571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1061830186970699883428189 398186320114012456285571)
              ·
                refine ⟨597279480171018684428357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 398186320114012456285571 597279480171018684428357)
                ·
                  refine ⟨111989902532066003330317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 597279480171018684428357 111989902532066003330317)
                  ·
                    rfl

theorem cell20_245362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_245362 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_245362 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_245362 prefixEnd_245362 := by exact prefixLift 245362
  have htrace : WordTrace (prefixWord ++ tailWord_245362) baseStart_245362 baseEnd_245362 := by
    simpa [prefixWord, tailWord_245362, baseEnd_245362] using wordTrace_append hprefix tailTrace_245362
  have hstable : (prefixWord ++ tailWord_245362).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245362).length < 2 ^ (prefixWord ++ tailWord_245362).sum := by decide
  have hdescent : baseEnd_245362 < baseStart_245362 := by decide
  rcases family_descends (prefixWord ++ tailWord_245362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245376 : List Nat := [2, 1, 1, 2, 1, 4, 3, 3, 3]
def baseStart_245376 : Nat := 118140960795 + 245376 * 2 ^ 59
def prefixEnd_245376 : Nat := 4983230072969 + 3 ^ 40 * 245376 * 2
def baseEnd_245376 : Nat := 111996292513544176863593

theorem tailTrace_245376 : CollatzResearch.WordTrace tailWord_245376 prefixEnd_245376 111996292513544176863593 := by
  unfold tailWord_245376
  simp only [CollatzResearch.WordTrace]
  refine ⟨4474798979526066864765991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5966398639368089153021321 4474798979526066864765991)
  ·
    refine ⟨6712198469289100297148987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4474798979526066864765991 6712198469289100297148987)
    ·
      refine ⟨10068297703933650445723481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6712198469289100297148987 10068297703933650445723481)
      ·
        refine ⟨7551223277950237834292611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10068297703933650445723481 7551223277950237834292611)
        ·
          refine ⟨11326834916925356751438917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7551223277950237834292611 11326834916925356751438917)
          ·
            refine ⟨2123781546923504390894797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11326834916925356751438917 2123781546923504390894797)
            ·
              refine ⟨796418080096314146585549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2123781546923504390894797 796418080096314146585549)
              ·
                refine ⟨298656780036117804969581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 796418080096314146585549 298656780036117804969581)
                ·
                  refine ⟨111996292513544176863593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 298656780036117804969581 111996292513544176863593)
                  ·
                    rfl

theorem cell20_245376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 3, 3].length) (baseStart_245376 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_245376 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_245376 prefixEnd_245376 := by exact prefixLift 245376
  have htrace : WordTrace (prefixWord ++ tailWord_245376) baseStart_245376 baseEnd_245376 := by
    simpa [prefixWord, tailWord_245376, baseEnd_245376] using wordTrace_append hprefix tailTrace_245376
  have hstable : (prefixWord ++ tailWord_245376).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245376).length < 2 ^ (prefixWord ++ tailWord_245376).sum := by decide
  have hdescent : baseEnd_245376 < baseStart_245376 := by decide
  rcases family_descends (prefixWord ++ tailWord_245376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245397 : List Nat := [1, 3, 2, 1, 1, 1, 1, 3, 7]
def baseStart_245397 : Nat := 118140960795 + 245397 * 2 ^ 59
def prefixEnd_245397 : Nat := 4983230072969 + 3 ^ 40 * 245397 * 2
def baseEnd_245397 : Nat := 112005877485761437163507

theorem tailTrace_245397 : CollatzResearch.WordTrace tailWord_245397 prefixEnd_245397 112005877485761437163507 := by
  unfold tailWord_245397
  simp only [CollatzResearch.WordTrace]
  refine ⟨8950363891976054316046445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5966909261317369544030963 8950363891976054316046445)
  ·
    refine ⟨3356386459491020368517417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8950363891976054316046445 3356386459491020368517417)
    ·
      refine ⟨2517289844618265276388063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3356386459491020368517417 2517289844618265276388063)
      ·
        refine ⟨3775934766927397914582095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2517289844618265276388063 3775934766927397914582095)
        ·
          refine ⟨5663902150391096871873143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3775934766927397914582095 5663902150391096871873143)
          ·
            refine ⟨8495853225586645307809715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5663902150391096871873143 8495853225586645307809715)
            ·
              refine ⟨12743779838379967961714573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8495853225586645307809715 12743779838379967961714573)
              ·
                refine ⟨4778917439392487985642965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12743779838379967961714573 4778917439392487985642965)
                ·
                  refine ⟨112005877485761437163507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4778917439392487985642965 112005877485761437163507)
                  ·
                    rfl

theorem cell20_245397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 7].length) (baseStart_245397 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_245397 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_245397 prefixEnd_245397 := by exact prefixLift 245397
  have htrace : WordTrace (prefixWord ++ tailWord_245397) baseStart_245397 baseEnd_245397 := by
    simpa [prefixWord, tailWord_245397, baseEnd_245397] using wordTrace_append hprefix tailTrace_245397
  have hstable : (prefixWord ++ tailWord_245397).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245397).length < 2 ^ (prefixWord ++ tailWord_245397).sum := by decide
  have hdescent : baseEnd_245397 < baseStart_245397 := by decide
  rcases family_descends (prefixWord ++ tailWord_245397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245407 : List Nat := [1, 1, 2, 7, 1, 8]
def baseStart_245407 : Nat := 118140960795 + 245407 * 2 ^ 59
def prefixEnd_245407 : Nat := 4983230072969 + 3 ^ 40 * 245407 * 2
def baseEnd_245407 : Nat := 4148534879935031364079

theorem tailTrace_245407 : CollatzResearch.WordTrace tailWord_245407 prefixEnd_245407 4148534879935031364079 := by
  unfold tailWord_245407
  simp only [CollatzResearch.WordTrace]
  refine ⟨8950728621939826023910475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5967152414626550682606983 8950728621939826023910475)
  ·
    refine ⟨13426092932909739035865713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8950728621939826023910475 13426092932909739035865713)
    ·
      refine ⟨10069569699682304276899285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13426092932909739035865713 10069569699682304276899285)
      ·
        refine ⟨236005539836304006489827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 10069569699682304276899285 236005539836304006489827)
        ·
          refine ⟨354008309754456009734741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236005539836304006489827 354008309754456009734741)
          ·
            refine ⟨4148534879935031364079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 354008309754456009734741 4148534879935031364079)
            ·
              rfl

theorem cell20_245407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 8].length) (baseStart_245407 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_245407 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_245407 prefixEnd_245407 := by exact prefixLift 245407
  have htrace : WordTrace (prefixWord ++ tailWord_245407) baseStart_245407 baseEnd_245407 := by
    simpa [prefixWord, tailWord_245407, baseEnd_245407] using wordTrace_append hprefix tailTrace_245407
  have hstable : (prefixWord ++ tailWord_245407).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245407).length < 2 ^ (prefixWord ++ tailWord_245407).sum := by decide
  have hdescent : baseEnd_245407 < baseStart_245407 := by decide
  rcases family_descends (prefixWord ++ tailWord_245407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245438 : List Nat := [4, 2, 1, 1, 2, 3, 1, 2, 4]
def baseStart_245438 : Nat := 118140960795 + 245438 * 2 ^ 59
def prefixEnd_245438 : Nat := 4983230072969 + 3 ^ 40 * 245438 * 2
def baseEnd_245438 : Nat := 112024591002947516796673

theorem tailTrace_245438 : CollatzResearch.WordTrace tailWord_245438 prefixEnd_245438 112024591002947516796673 := by
  unfold tailWord_245438
  simp only [CollatzResearch.WordTrace]
  refine ⟨1118982410603439789786121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5967906189885012212192645 1118982410603439789786121)
  ·
    refine ⟨839236807952579842339591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1118982410603439789786121 839236807952579842339591)
    ·
      refine ⟨1258855211928869763509387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 839236807952579842339591 1258855211928869763509387)
      ·
        refine ⟨1888282817893304645264081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1258855211928869763509387 1888282817893304645264081)
        ·
          refine ⟨1416212113419978483948061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1888282817893304645264081 1416212113419978483948061)
          ·
            refine ⟨531079542532491931480523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1416212113419978483948061 531079542532491931480523)
            ·
              refine ⟨796619313798737897220785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 531079542532491931480523 796619313798737897220785)
              ·
                refine ⟨597464485349053422915589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 796619313798737897220785 597464485349053422915589)
                ·
                  refine ⟨112024591002947516796673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 597464485349053422915589 112024591002947516796673)
                  ·
                    rfl

theorem cell20_245438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_245438 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_245438 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_245438 prefixEnd_245438 := by exact prefixLift 245438
  have htrace : WordTrace (prefixWord ++ tailWord_245438) baseStart_245438 baseEnd_245438 := by
    simpa [prefixWord, tailWord_245438, baseEnd_245438] using wordTrace_append hprefix tailTrace_245438
  have hstable : (prefixWord ++ tailWord_245438).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245438).length < 2 ^ (prefixWord ++ tailWord_245438).sum := by decide
  have hdescent : baseEnd_245438 < baseStart_245438 := by decide
  rcases family_descends (prefixWord ++ tailWord_245438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245466 : List Nat := [3, 1, 1, 2, 2, 4, 7]
def baseStart_245466 : Nat := 118140960795 + 245466 * 2 ^ 59
def prefixEnd_245466 : Nat := 4983230072969 + 3 ^ 40 * 245466 * 2
def baseEnd_245466 : Nat := 12448596773989318207025

theorem tailTrace_245466 : CollatzResearch.WordTrace tailWord_245466 prefixEnd_245466 12448596773989318207025 := by
  unfold tailWord_245466
  simp only [CollatzResearch.WordTrace]
  refine ⟨2238220132181519775077063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5968587019150719400205501 2238220132181519775077063)
  ·
    refine ⟨3357330198272279662615595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2238220132181519775077063 3357330198272279662615595)
    ·
      refine ⟨5035995297408419493923393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3357330198272279662615595 5035995297408419493923393)
      ·
        refine ⟨3776996473056314620442545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5035995297408419493923393 3776996473056314620442545)
        ·
          refine ⟨2832747354792235965331909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3776996473056314620442545 2832747354792235965331909)
          ·
            refine ⟨531140129023544243499733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2832747354792235965331909 531140129023544243499733)
            ·
              refine ⟨12448596773989318207025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 531140129023544243499733 12448596773989318207025)
              ·
                rfl

theorem cell20_245466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 7].length) (baseStart_245466 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_245466 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_245466 prefixEnd_245466 := by exact prefixLift 245466
  have htrace : WordTrace (prefixWord ++ tailWord_245466) baseStart_245466 baseEnd_245466 := by
    simpa [prefixWord, tailWord_245466, baseEnd_245466] using wordTrace_append hprefix tailTrace_245466
  have hstable : (prefixWord ++ tailWord_245466).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245466).length < 2 ^ (prefixWord ++ tailWord_245466).sum := by decide
  have hdescent : baseEnd_245466 < baseStart_245466 := by decide
  rcases family_descends (prefixWord ++ tailWord_245466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245476 : List Nat := [2, 3, 1, 1, 1, 3, 1, 6, 2]
def baseStart_245476 : Nat := 118140960795 + 245476 * 2 ^ 59
def prefixEnd_245476 : Nat := 4983230072969 + 3 ^ 40 * 245476 * 2
def baseEnd_245476 : Nat := 112041935238388273529851

theorem tailTrace_245476 : CollatzResearch.WordTrace tailWord_245476 prefixEnd_245476 112041935238388273529851 := by
  unfold tailWord_245476
  simp only [CollatzResearch.WordTrace]
  refine ⟨4476622629344925404086141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5968830172459900538781521 4476622629344925404086141)
  ·
    refine ⟨1678733486004347026532303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4476622629344925404086141 1678733486004347026532303)
    ·
      refine ⟨2518100229006520539798455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1678733486004347026532303 2518100229006520539798455)
      ·
        refine ⟨3777150343509780809697683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2518100229006520539798455 3777150343509780809697683)
        ·
          refine ⟨5665725515264671214546525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3777150343509780809697683 5665725515264671214546525)
          ·
            refine ⟨2124647068224251705454947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5665725515264671214546525 2124647068224251705454947)
            ·
              refine ⟨3186970602336377558182421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2124647068224251705454947 3186970602336377558182421)
              ·
                refine ⟨149389246984517698039801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3186970602336377558182421 149389246984517698039801)
                ·
                  refine ⟨112041935238388273529851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 149389246984517698039801 112041935238388273529851)
                  ·
                    rfl

theorem cell20_245476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 6, 2].length) (baseStart_245476 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_245476 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_245476 prefixEnd_245476 := by exact prefixLift 245476
  have htrace : WordTrace (prefixWord ++ tailWord_245476) baseStart_245476 baseEnd_245476 := by
    simpa [prefixWord, tailWord_245476, baseEnd_245476] using wordTrace_append hprefix tailTrace_245476
  have hstable : (prefixWord ++ tailWord_245476).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245476).length < 2 ^ (prefixWord ++ tailWord_245476).sum := by decide
  have hdescent : baseEnd_245476 < baseStart_245476 := by decide
  rcases family_descends (prefixWord ++ tailWord_245476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245580 : List Nat := [2, 2, 1, 3, 4, 8]
def baseStart_245580 : Nat := 118140960795 + 245580 * 2 ^ 59
def prefixEnd_245580 : Nat := 4983230072969 + 3 ^ 40 * 245580 * 2
def baseEnd_245580 : Nat := 4151459395267634594917

theorem tailTrace_245580 : CollatzResearch.WordTrace tailWord_245580 prefixEnd_245580 4151459395267634594917 := by
  unfold tailWord_245580
  simp only [CollatzResearch.WordTrace]
  refine ⟨4478519225156538284979097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5971358966875384379972129 4478519225156538284979097)
  ·
    refine ⟨3358889418867403713734323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4478519225156538284979097 3358889418867403713734323)
    ·
      refine ⟨5038334128301105570601485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3358889418867403713734323 5038334128301105570601485)
      ·
        refine ⟨1889375298112914588975557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5038334128301105570601485 1889375298112914588975557)
        ·
          refine ⟨354257868396171485432917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1889375298112914588975557 354257868396171485432917)
          ·
            refine ⟨4151459395267634594917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 354257868396171485432917 4151459395267634594917)
            ·
              rfl

theorem cell20_245580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 8].length) (baseStart_245580 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_245580 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_245580 prefixEnd_245580 := by exact prefixLift 245580
  have htrace : WordTrace (prefixWord ++ tailWord_245580) baseStart_245580 baseEnd_245580 := by
    simpa [prefixWord, tailWord_245580, baseEnd_245580] using wordTrace_append hprefix tailTrace_245580
  have hstable : (prefixWord ++ tailWord_245580).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245580).length < 2 ^ (prefixWord ++ tailWord_245580).sum := by decide
  have hdescent : baseEnd_245580 < baseStart_245580 := by decide
  rcases family_descends (prefixWord ++ tailWord_245580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245586 : List Nat := [3, 2, 2, 1, 1, 5, 2, 2, 2]
def baseStart_245586 : Nat := 118140960795 + 245586 * 2 ^ 59
def prefixEnd_245586 : Nat := 4983230072969 + 3 ^ 40 * 245586 * 2
def baseEnd_245586 : Nat := 112092142235716779862735

theorem tailTrace_245586 : CollatzResearch.WordTrace tailWord_245586 prefixEnd_245586 112092142235716779862735 := by
  unfold tailWord_245586
  simp only [CollatzResearch.WordTrace]
  refine ⟨2239314322072834898669153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5971504858860893063117741 2239314322072834898669153)
  ·
    refine ⟨1679485741554626174001865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2239314322072834898669153 1679485741554626174001865)
    ·
      refine ⟨1259614306165969630501399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1679485741554626174001865 1259614306165969630501399)
      ·
        refine ⟨1889421459248954445752099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1259614306165969630501399 1889421459248954445752099)
        ·
          refine ⟨2834132188873431668628149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1889421459248954445752099 2834132188873431668628149)
          ·
            refine ⟨265699892706884218933889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2834132188873431668628149 265699892706884218933889)
            ·
              refine ⟨199274919530163164200417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 265699892706884218933889 199274919530163164200417)
              ·
                refine ⟨149456189647622373150313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 199274919530163164200417 149456189647622373150313)
                ·
                  refine ⟨112092142235716779862735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 149456189647622373150313 112092142235716779862735)
                  ·
                    rfl

theorem cell20_245586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 2, 2, 2].length) (baseStart_245586 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_245586 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_245586 prefixEnd_245586 := by exact prefixLift 245586
  have htrace : WordTrace (prefixWord ++ tailWord_245586) baseStart_245586 baseEnd_245586 := by
    simpa [prefixWord, tailWord_245586, baseEnd_245586] using wordTrace_append hprefix tailTrace_245586
  have hstable : (prefixWord ++ tailWord_245586).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245586).length < 2 ^ (prefixWord ++ tailWord_245586).sum := by decide
  have hdescent : baseEnd_245586 < baseStart_245586 := by decide
  rcases family_descends (prefixWord ++ tailWord_245586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245614 : List Nat := [4, 1, 2, 3, 1, 2, 3, 4]
def baseStart_245614 : Nat := 118140960795 + 245614 * 2 ^ 59
def prefixEnd_245614 : Nat := 4983230072969 + 3 ^ 40 * 245614 * 2
def baseEnd_245614 : Nat := 37368307399557708976429

theorem tailTrace_245614 : CollatzResearch.WordTrace tailWord_245614 prefixEnd_245614 37368307399557708976429 := by
  unfold tailWord_245614
  simp only [CollatzResearch.WordTrace]
  refine ⟨1119784816523737547086987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5972185688126600251130597 1119784816523737547086987)
  ·
    refine ⟨1679677224785606320630481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1119784816523737547086987 1679677224785606320630481)
    ·
      refine ⟨1259757918589204740472861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1679677224785606320630481 1259757918589204740472861)
      ·
        refine ⟨472409219470951777677323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1259757918589204740472861 472409219470951777677323)
        ·
          refine ⟨708613829206427666515985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 472409219470951777677323 708613829206427666515985)
          ·
            refine ⟨531460371904820749886989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 708613829206427666515985 531460371904820749886989)
            ·
              refine ⟨199297639464307781207621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 531460371904820749886989 199297639464307781207621)
              ·
                refine ⟨37368307399557708976429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 199297639464307781207621 37368307399557708976429)
                ·
                  rfl

theorem cell20_245614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 3, 4].length) (baseStart_245614 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_245614 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_245614 prefixEnd_245614 := by exact prefixLift 245614
  have htrace : WordTrace (prefixWord ++ tailWord_245614) baseStart_245614 baseEnd_245614 := by
    simpa [prefixWord, tailWord_245614, baseEnd_245614] using wordTrace_append hprefix tailTrace_245614
  have hstable : (prefixWord ++ tailWord_245614).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245614).length < 2 ^ (prefixWord ++ tailWord_245614).sum := by decide
  have hdescent : baseEnd_245614 < baseStart_245614 := by decide
  rcases family_descends (prefixWord ++ tailWord_245614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245625 : List Nat := [1, 2, 1, 3, 2, 2, 2, 2, 5]
def baseStart_245625 : Nat := 118140960795 + 245625 * 2 ^ 59
def prefixEnd_245625 : Nat := 4983230072969 + 3 ^ 40 * 245625 * 2
def baseEnd_245625 : Nat := 112109942898405977562575

theorem tailTrace_245625 : CollatzResearch.WordTrace tailWord_245625 prefixEnd_245625 112109942898405977562575 := by
  unfold tailWord_245625
  simp only [CollatzResearch.WordTrace]
  refine ⟨8958679735150049255346329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5972453156766699503564219 8958679735150049255346329)
  ·
    refine ⟨6719009801362536941509747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8958679735150049255346329 6719009801362536941509747)
    ·
      refine ⟨10078514702043805412264621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6719009801362536941509747 10078514702043805412264621)
      ·
        refine ⟨3779443013266427029599233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10078514702043805412264621 3779443013266427029599233)
        ·
          refine ⟨2834582259949820272199425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3779443013266427029599233 2834582259949820272199425)
          ·
            refine ⟨2125936694962365204149569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2834582259949820272199425 2125936694962365204149569)
            ·
              refine ⟨1594452521221773903112177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2125936694962365204149569 1594452521221773903112177)
              ·
                refine ⟨1195839390916330427334133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1594452521221773903112177 1195839390916330427334133)
                ·
                  refine ⟨112109942898405977562575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1195839390916330427334133 112109942898405977562575)
                  ·
                    rfl

theorem cell20_245625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2, 5].length) (baseStart_245625 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_245625 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_245625 prefixEnd_245625 := by exact prefixLift 245625
  have htrace : WordTrace (prefixWord ++ tailWord_245625) baseStart_245625 baseEnd_245625 := by
    simpa [prefixWord, tailWord_245625, baseEnd_245625] using wordTrace_append hprefix tailTrace_245625
  have hstable : (prefixWord ++ tailWord_245625).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245625).length < 2 ^ (prefixWord ++ tailWord_245625).sum := by decide
  have hdescent : baseEnd_245625 < baseStart_245625 := by decide
  rcases family_descends (prefixWord ++ tailWord_245625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245632 : List Nat := [2, 1, 1, 2, 1, 2, 3, 2, 6]
def baseStart_245632 : Nat := 118140960795 + 245632 * 2 ^ 59
def prefixEnd_245632 : Nat := 4983230072969 + 3 ^ 40 * 245632 * 2
def baseEnd_245632 : Nat := 112113137889145064329213

theorem tailTrace_245632 : CollatzResearch.WordTrace tailWord_245632 prefixEnd_245632 112113137889145064329213 := by
  unfold tailWord_245632
  simp only [CollatzResearch.WordTrace]
  refine ⟨4479467523062344725425575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5972623364083126300567433 4479467523062344725425575)
  ·
    refine ⟨6719201284593517088138363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4479467523062344725425575 6719201284593517088138363)
    ·
      refine ⟨10078801926890275632207545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6719201284593517088138363 10078801926890275632207545)
      ·
        refine ⟨7559101445167706724155659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10078801926890275632207545 7559101445167706724155659)
        ·
          refine ⟨11338652167751560086233489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7559101445167706724155659 11338652167751560086233489)
          ·
            refine ⟨8503989125813670064675117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11338652167751560086233489 8503989125813670064675117)
            ·
              refine ⟨3188995922180126274253169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8503989125813670064675117 3188995922180126274253169)
              ·
                refine ⟨2391746941635094705689877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3188995922180126274253169 2391746941635094705689877)
                ·
                  refine ⟨112113137889145064329213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2391746941635094705689877 112113137889145064329213)
                  ·
                    rfl

theorem cell20_245632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 6].length) (baseStart_245632 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_245632 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_245632 prefixEnd_245632 := by exact prefixLift 245632
  have htrace : WordTrace (prefixWord ++ tailWord_245632) baseStart_245632 baseEnd_245632 := by
    simpa [prefixWord, tailWord_245632, baseEnd_245632] using wordTrace_append hprefix tailTrace_245632
  have hstable : (prefixWord ++ tailWord_245632).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245632).length < 2 ^ (prefixWord ++ tailWord_245632).sum := by decide
  have hdescent : baseEnd_245632 < baseStart_245632 := by decide
  rcases family_descends (prefixWord ++ tailWord_245632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245694 : List Nat := [4, 2, 1, 1, 1, 3, 8]
def baseStart_245694 : Nat := 118140960795 + 245694 * 2 ^ 59
def prefixEnd_245694 : Nat := 4983230072969 + 3 ^ 40 * 245694 * 2
def baseEnd_245694 : Nat := 12460159597616489362477

theorem tailTrace_245694 : CollatzResearch.WordTrace tailWord_245694 prefixEnd_245694 12460159597616489362477 := by
  unfold tailWord_245694
  simp only [CollatzResearch.WordTrace]
  refine ⟨1120149546487509254951017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5974130914600049359738757 1120149546487509254951017)
  ·
    refine ⟨840112159865631941213263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1120149546487509254951017 840112159865631941213263)
    ·
      refine ⟨1260168239798447911819895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 840112159865631941213263 1260168239798447911819895)
      ·
        refine ⟨1890252359697671867729843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1260168239798447911819895 1890252359697671867729843)
        ·
          refine ⟨2835378539546507801594765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1890252359697671867729843 2835378539546507801594765)
          ·
            refine ⟨1063266952329940425598037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2835378539546507801594765 1063266952329940425598037)
            ·
              refine ⟨12460159597616489362477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1063266952329940425598037 12460159597616489362477)
              ·
                rfl

theorem cell20_245694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 8].length) (baseStart_245694 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_245694 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_245694 prefixEnd_245694 := by exact prefixLift 245694
  have htrace : WordTrace (prefixWord ++ tailWord_245694) baseStart_245694 baseEnd_245694 := by
    simpa [prefixWord, tailWord_245694, baseEnd_245694] using wordTrace_append hprefix tailTrace_245694
  have hstable : (prefixWord ++ tailWord_245694).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245694).length < 2 ^ (prefixWord ++ tailWord_245694).sum := by decide
  have hdescent : baseEnd_245694 < baseStart_245694 := by decide
  rcases family_descends (prefixWord ++ tailWord_245694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245704 : List Nat := [2, 1, 3, 1, 4, 3, 1, 1, 4]
def baseStart_245704 : Nat := 118140960795 + 245704 * 2 ^ 59
def prefixEnd_245704 : Nat := 4983230072969 + 3 ^ 40 * 245704 * 2
def baseEnd_245704 : Nat := 112146000651032813928919

theorem tailTrace_245704 : CollatzResearch.WordTrace tailWord_245704 prefixEnd_245704 112146000651032813928919 := by
  unfold tailWord_245704
  simp only [CollatzResearch.WordTrace]
  refine ⟨4480780550931922873736083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5974374067909230498314777 4480780550931922873736083)
  ·
    refine ⟨6721170826397884310604125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4480780550931922873736083 6721170826397884310604125)
    ·
      refine ⟨2520439059899206616476547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6721170826397884310604125 2520439059899206616476547)
      ·
        refine ⟨3780658589848809924714821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2520439059899206616476547 3780658589848809924714821)
        ·
          refine ⟨708873485596651860884029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3780658589848809924714821 708873485596651860884029)
          ·
            refine ⟨265827557098744447831511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 708873485596651860884029 265827557098744447831511)
            ·
              refine ⟨398741335648116671747267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265827557098744447831511 398741335648116671747267)
              ·
                refine ⟨598112003472175007620901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 398741335648116671747267 598112003472175007620901)
                ·
                  refine ⟨112146000651032813928919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 598112003472175007620901 112146000651032813928919)
                  ·
                    rfl

theorem cell20_245704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 1, 4].length) (baseStart_245704 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_245704 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_245704 prefixEnd_245704 := by exact prefixLift 245704
  have htrace : WordTrace (prefixWord ++ tailWord_245704) baseStart_245704 baseEnd_245704 := by
    simpa [prefixWord, tailWord_245704, baseEnd_245704] using wordTrace_append hprefix tailTrace_245704
  have hstable : (prefixWord ++ tailWord_245704).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245704).length < 2 ^ (prefixWord ++ tailWord_245704).sum := by decide
  have hdescent : baseEnd_245704 < baseStart_245704 := by decide
  rcases family_descends (prefixWord ++ tailWord_245704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245753 : List Nat := [1, 2, 1, 3, 1, 12]
def baseStart_245753 : Nat := 118140960795 + 245753 * 2 ^ 59
def prefixEnd_245753 : Nat := 4983230072969 + 3 ^ 40 * 245753 * 2
def baseEnd_245753 : Nat := 4154383910600237825755

theorem tailTrace_245753 : CollatzResearch.WordTrace tailWord_245753 prefixEnd_245753 4154383910600237825755 := by
  unfold tailWord_245753
  simp only [CollatzResearch.WordTrace]
  refine ⟨8963348278686327116005913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5975565519124218077337275 8963348278686327116005913)
  ·
    refine ⟨6722511209014745337004435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8963348278686327116005913 6722511209014745337004435)
    ·
      refine ⟨10083766813522118005506653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6722511209014745337004435 10083766813522118005506653)
      ·
        refine ⟨3781412555070794252064995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10083766813522118005506653 3781412555070794252064995)
        ·
          refine ⟨5672118832606191378097493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3781412555070794252064995 5672118832606191378097493)
          ·
            refine ⟨4154383910600237825755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 5672118832606191378097493 4154383910600237825755)
            ·
              rfl

theorem cell20_245753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 12].length) (baseStart_245753 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_245753 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_245753 prefixEnd_245753 := by exact prefixLift 245753
  have htrace : WordTrace (prefixWord ++ tailWord_245753) baseStart_245753 baseEnd_245753 := by
    simpa [prefixWord, tailWord_245753, baseEnd_245753] using wordTrace_append hprefix tailTrace_245753
  have hstable : (prefixWord ++ tailWord_245753).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245753).length < 2 ^ (prefixWord ++ tailWord_245753).sum := by decide
  have hdescent : baseEnd_245753 < baseStart_245753 := by decide
  rcases family_descends (prefixWord ++ tailWord_245753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245756 : List Nat := [2, 2, 2, 1, 2, 2, 4, 2, 3]
def baseStart_245756 : Nat := 118140960795 + 245756 * 2 ^ 59
def prefixEnd_245756 : Nat := 4983230072969 + 3 ^ 40 * 245756 * 2
def baseEnd_245756 : Nat := 112169734867951744195373

theorem tailTrace_245756 : CollatzResearch.WordTrace tailWord_245756 prefixEnd_245756 112169734867951744195373 := by
  unfold tailWord_245756
  simp only [CollatzResearch.WordTrace]
  refine ⟨4481728848837729314182561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5975638465116972418910081 4481728848837729314182561)
  ·
    refine ⟨3361296636628296985636921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4481728848837729314182561 3361296636628296985636921)
    ·
      refine ⟨2520972477471222739227691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3361296636628296985636921 2520972477471222739227691)
      ·
        refine ⟨3781458716206834108841537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2520972477471222739227691 3781458716206834108841537)
        ·
          refine ⟨2836094037155125581631153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3781458716206834108841537 2836094037155125581631153)
          ·
            refine ⟨2127070527866344186223365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2836094037155125581631153 2127070527866344186223365)
            ·
              refine ⟨398825723974939534916881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2127070527866344186223365 398825723974939534916881)
              ·
                refine ⟨299119292981204651187661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 398825723974939534916881 299119292981204651187661)
                ·
                  refine ⟨112169734867951744195373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 299119292981204651187661 112169734867951744195373)
                  ·
                    rfl

theorem cell20_245756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 2, 3].length) (baseStart_245756 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_245756 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_245756 prefixEnd_245756 := by exact prefixLift 245756
  have htrace : WordTrace (prefixWord ++ tailWord_245756) baseStart_245756 baseEnd_245756 := by
    simpa [prefixWord, tailWord_245756, baseEnd_245756] using wordTrace_append hprefix tailTrace_245756
  have hstable : (prefixWord ++ tailWord_245756).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245756).length < 2 ^ (prefixWord ++ tailWord_245756).sum := by decide
  have hdescent : baseEnd_245756 < baseStart_245756 := by decide
  rcases family_descends (prefixWord ++ tailWord_245756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245829 : List Nat := [1, 3, 1, 1, 1, 3, 1, 9]
def baseStart_245829 : Nat := 118140960795 + 245829 * 2 ^ 59
def prefixEnd_245829 : Nat := 4983230072969 + 3 ^ 40 * 245829 * 2
def baseEnd_245829 : Nat := 37401018019029311587247

theorem tailTrace_245829 : CollatzResearch.WordTrace tailWord_245829 prefixEnd_245829 37401018019029311587247 := by
  unfold tailWord_245829
  simp only [CollatzResearch.WordTrace]
  refine ⟨8966120226410992095772541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5977413484273994730515027 8966120226410992095772541)
  ·
    refine ⟨3362295084904122035914703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8966120226410992095772541 3362295084904122035914703)
    ·
      refine ⟨5043442627356183053872055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3362295084904122035914703 5043442627356183053872055)
      ·
        refine ⟨7565163941034274580808083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5043442627356183053872055 7565163941034274580808083)
        ·
          refine ⟨11347745911551411871212125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7565163941034274580808083 11347745911551411871212125)
          ·
            refine ⟨4255404716831779451704547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11347745911551411871212125 4255404716831779451704547)
            ·
              refine ⟨6383107075247669177556821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4255404716831779451704547 6383107075247669177556821)
              ·
                refine ⟨37401018019029311587247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6383107075247669177556821 37401018019029311587247)
                ·
                  rfl

theorem cell20_245829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 9].length) (baseStart_245829 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_245829 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_245829 prefixEnd_245829 := by exact prefixLift 245829
  have htrace : WordTrace (prefixWord ++ tailWord_245829) baseStart_245829 baseEnd_245829 := by
    simpa [prefixWord, tailWord_245829, baseEnd_245829] using wordTrace_append hprefix tailTrace_245829
  have hstable : (prefixWord ++ tailWord_245829).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245829).length < 2 ^ (prefixWord ++ tailWord_245829).sum := by decide
  have hdescent : baseEnd_245829 < baseStart_245829 := by decide
  rcases family_descends (prefixWord ++ tailWord_245829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245842 : List Nat := [3, 2, 2, 1, 4, 2, 2, 4]
def baseStart_245842 : Nat := 118140960795 + 245842 * 2 ^ 59
def prefixEnd_245842 : Nat := 4983230072969 + 3 ^ 40 * 245842 * 2
def baseEnd_245842 : Nat := 37402995870439222442785

theorem tailTrace_245842 : CollatzResearch.WordTrace tailWord_245842 prefixEnd_245842 37402995870439222442785 := by
  unfold tailWord_245842
  simp only [CollatzResearch.WordTrace]
  refine ⟨2241648593840973828998945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5977729583575930210663853 2241648593840973828998945)
  ·
    refine ⟨1681236445380730371749209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2241648593840973828998945 1681236445380730371749209)
    ·
      refine ⟨1260927334035547778811907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1681236445380730371749209 1260927334035547778811907)
      ·
        refine ⟨1891391001053321668217861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1260927334035547778811907 1891391001053321668217861)
        ·
          refine ⟨354635812697497812790849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1891391001053321668217861 354635812697497812790849)
          ·
            refine ⟨265976859523123359593137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 354635812697497812790849 265976859523123359593137)
            ·
              refine ⟨199482644642342519694853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 265976859523123359593137 199482644642342519694853)
              ·
                refine ⟨37402995870439222442785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 199482644642342519694853 37402995870439222442785)
                ·
                  rfl

theorem cell20_245842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 2, 4].length) (baseStart_245842 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_245842 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_245842 prefixEnd_245842 := by exact prefixLift 245842
  have htrace : WordTrace (prefixWord ++ tailWord_245842) baseStart_245842 baseEnd_245842 := by
    simpa [prefixWord, tailWord_245842, baseEnd_245842] using wordTrace_append hprefix tailTrace_245842
  have hstable : (prefixWord ++ tailWord_245842).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245842).length < 2 ^ (prefixWord ++ tailWord_245842).sum := by decide
  have hdescent : baseEnd_245842 < baseStart_245842 := by decide
  rcases family_descends (prefixWord ++ tailWord_245842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245856 : List Nat := [2, 1, 1, 3, 2, 3, 3, 3, 2]
def baseStart_245856 : Nat := 118140960795 + 245856 * 2 ^ 59
def prefixEnd_245856 : Nat := 4983230072969 + 3 ^ 40 * 245856 * 2
def baseEnd_245856 : Nat := 112215377592795840861631

theorem tailTrace_245856 : CollatzResearch.WordTrace tailWord_245856 prefixEnd_245856 112215377592795840861631 := by
  unfold tailWord_245856
  simp only [CollatzResearch.WordTrace]
  refine ⟨4483552498656587853502711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5978069998208783804670281 4483552498656587853502711)
  ·
    refine ⟨6725328747984881780254067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4483552498656587853502711 6725328747984881780254067)
    ·
      refine ⟨10087993121977322670381101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6725328747984881780254067 10087993121977322670381101)
      ·
        refine ⟨3782997420741496001392913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10087993121977322670381101 3782997420741496001392913)
        ·
          refine ⟨2837248065556122001044685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3782997420741496001392913 2837248065556122001044685)
          ·
            refine ⟨1063968024583545750391757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2837248065556122001044685 1063968024583545750391757)
            ·
              refine ⟨398988009218829656396909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1063968024583545750391757 398988009218829656396909)
              ·
                refine ⟨149620503457061121148841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 398988009218829656396909 149620503457061121148841)
                ·
                  refine ⟨112215377592795840861631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 149620503457061121148841 112215377592795840861631)
                  ·
                    rfl

theorem cell20_245856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 3, 2].length) (baseStart_245856 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_245856 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_245856 prefixEnd_245856 := by exact prefixLift 245856
  have htrace : WordTrace (prefixWord ++ tailWord_245856) baseStart_245856 baseEnd_245856 := by
    simpa [prefixWord, tailWord_245856, baseEnd_245856] using wordTrace_append hprefix tailTrace_245856
  have hstable : (prefixWord ++ tailWord_245856).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245856).length < 2 ^ (prefixWord ++ tailWord_245856).sum := by decide
  have hdescent : baseEnd_245856 < baseStart_245856 := by decide
  rcases family_descends (prefixWord ++ tailWord_245856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245860 : List Nat := [2, 3, 1, 1, 2, 1, 2, 2, 6]
def baseStart_245860 : Nat := 118140960795 + 245860 * 2 ^ 59
def prefixEnd_245860 : Nat := 4983230072969 + 3 ^ 40 * 245860 * 2
def baseEnd_245860 : Nat := 112217203301789604728281

theorem tailTrace_245860 : CollatzResearch.WordTrace tailWord_245860 prefixEnd_245860 112217203301789604728281 := by
  unfold tailWord_245860
  simp only [CollatzResearch.WordTrace]
  refine ⟨4483625444649342195075517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5978167259532456260100689 4483625444649342195075517)
  ·
    refine ⟨1681359541743503323153319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4483625444649342195075517 1681359541743503323153319)
    ·
      refine ⟨2522039312615254984729979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1681359541743503323153319 2522039312615254984729979)
      ·
        refine ⟨3783058968922882477094969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2522039312615254984729979 3783058968922882477094969)
        ·
          refine ⟨2837294226692161857821227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3783058968922882477094969 2837294226692161857821227)
          ·
            refine ⟨4255941340038242786731841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2837294226692161857821227 4255941340038242786731841)
            ·
              refine ⟨3191956005028682090048881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4255941340038242786731841 3191956005028682090048881)
              ·
                refine ⟨2393967003771511567536661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3191956005028682090048881 2393967003771511567536661)
                ·
                  refine ⟨112217203301789604728281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2393967003771511567536661 112217203301789604728281)
                  ·
                    rfl

theorem cell20_245860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_245860 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_245860 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_245860 prefixEnd_245860 := by exact prefixLift 245860
  have htrace : WordTrace (prefixWord ++ tailWord_245860) baseStart_245860 baseEnd_245860 := by
    simpa [prefixWord, tailWord_245860, baseEnd_245860] using wordTrace_append hprefix tailTrace_245860
  have hstable : (prefixWord ++ tailWord_245860).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245860).length < 2 ^ (prefixWord ++ tailWord_245860).sum := by decide
  have hdescent : baseEnd_245860 < baseStart_245860 := by decide
  rcases family_descends (prefixWord ++ tailWord_245860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245870 : List Nat := [4, 1, 2, 2, 1, 1, 2, 4, 3]
def baseStart_245870 : Nat := 118140960795 + 245870 * 2 ^ 59
def prefixEnd_245870 : Nat := 4983230072969 + 3 ^ 40 * 245870 * 2
def baseEnd_245870 : Nat := 112221767574274014394907

theorem tailTrace_245870 : CollatzResearch.WordTrace tailWord_245870 prefixEnd_245870 112221767574274014394907 := by
  unfold tailWord_245870
  simp only [CollatzResearch.WordTrace]
  refine ⟨1120951952407807012251883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5978410412841637398676709 1120951952407807012251883)
  ·
    refine ⟨1681427928611710518377825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1120951952407807012251883 1681427928611710518377825)
    ·
      refine ⟨1261070946458782888783369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1681427928611710518377825 1261070946458782888783369)
      ·
        refine ⟨945803209844087166587527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1261070946458782888783369 945803209844087166587527)
        ·
          refine ⟨1418704814766130749881291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 945803209844087166587527 1418704814766130749881291)
          ·
            refine ⟨2128057222149196124821937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1418704814766130749881291 2128057222149196124821937)
            ·
              refine ⟨1596042916611897093616453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2128057222149196124821937 1596042916611897093616453)
              ·
                refine ⟨299258046864730705053085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1596042916611897093616453 299258046864730705053085)
                ·
                  refine ⟨112221767574274014394907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 299258046864730705053085 112221767574274014394907)
                  ·
                    rfl

theorem cell20_245870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 4, 3].length) (baseStart_245870 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_245870 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_245870 prefixEnd_245870 := by exact prefixLift 245870
  have htrace : WordTrace (prefixWord ++ tailWord_245870) baseStart_245870 baseEnd_245870 := by
    simpa [prefixWord, tailWord_245870, baseEnd_245870] using wordTrace_append hprefix tailTrace_245870
  have hstable : (prefixWord ++ tailWord_245870).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245870).length < 2 ^ (prefixWord ++ tailWord_245870).sum := by decide
  have hdescent : baseEnd_245870 < baseStart_245870 := by decide
  rcases family_descends (prefixWord ++ tailWord_245870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245884 : List Nat := [2, 2, 2, 1, 1, 5, 2, 5]
def baseStart_245884 : Nat := 118140960795 + 245884 * 2 ^ 59
def prefixEnd_245884 : Nat := 4983230072969 + 3 ^ 40 * 245884 * 2
def baseEnd_245884 : Nat := 37409385851917395976061

theorem tailTrace_245884 : CollatzResearch.WordTrace tailWord_245884 prefixEnd_245884 37409385851917395976061 := by
  unfold tailWord_245884
  simp only [CollatzResearch.WordTrace]
  refine ⟨4484063120605868244512353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5978750827474490992683137 4484063120605868244512353)
  ·
    refine ⟨3363047340454401183384265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4484063120605868244512353 3363047340454401183384265)
    ·
      refine ⟨2522285505340800887538199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3363047340454401183384265 2522285505340800887538199)
      ·
        refine ⟨3783428258011201331307299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2522285505340800887538199 3783428258011201331307299)
        ·
          refine ⟨5675142387016801996960949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3783428258011201331307299 5675142387016801996960949)
          ·
            refine ⟨532044598782825187215089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5675142387016801996960949 532044598782825187215089)
            ·
              refine ⟨399033449087118890411317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 532044598782825187215089 399033449087118890411317)
              ·
                refine ⟨37409385851917395976061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 399033449087118890411317 37409385851917395976061)
                ·
                  rfl

theorem cell20_245884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 5].length) (baseStart_245884 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_245884 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_245884 prefixEnd_245884 := by exact prefixLift 245884
  have htrace : WordTrace (prefixWord ++ tailWord_245884) baseStart_245884 baseEnd_245884 := by
    simpa [prefixWord, tailWord_245884, baseEnd_245884] using wordTrace_append hprefix tailTrace_245884
  have hstable : (prefixWord ++ tailWord_245884).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245884).length < 2 ^ (prefixWord ++ tailWord_245884).sum := by decide
  have hdescent : baseEnd_245884 < baseStart_245884 := by decide
  rcases family_descends (prefixWord ++ tailWord_245884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245922 : List Nat := [3, 3, 1, 3, 1, 9]
def baseStart_245922 : Nat := 118140960795 + 245922 * 2 ^ 59
def prefixEnd_245922 : Nat := 4983230072969 + 3 ^ 40 * 245922 * 2
def baseEnd_245922 : Nat := 4157240807081220172643

theorem tailTrace_245922 : CollatzResearch.WordTrace tailWord_245922 prefixEnd_245922 4157240807081220172643 := by
  unfold tailWord_245922
  simp only [CollatzResearch.WordTrace]
  refine ⟨2242378053768517244727005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5979674810049379319272013 2242378053768517244727005)
  ·
    refine ⟨840891770163193966772627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2242378053768517244727005 840891770163193966772627)
    ·
      refine ⟨1261337655244790950158941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 840891770163193966772627 1261337655244790950158941)
      ·
        refine ⟨473001620716796606309603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1261337655244790950158941 473001620716796606309603)
        ·
          refine ⟨709502431075194909464405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473001620716796606309603 709502431075194909464405)
          ·
            refine ⟨4157240807081220172643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 709502431075194909464405 4157240807081220172643)
            ·
              rfl

theorem cell20_245922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 9].length) (baseStart_245922 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_245922 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_245922 prefixEnd_245922 := by exact prefixLift 245922
  have htrace : WordTrace (prefixWord ++ tailWord_245922) baseStart_245922 baseEnd_245922 := by
    simpa [prefixWord, tailWord_245922, baseEnd_245922] using wordTrace_append hprefix tailTrace_245922
  have hstable : (prefixWord ++ tailWord_245922).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245922).length < 2 ^ (prefixWord ++ tailWord_245922).sum := by decide
  have hdescent : baseEnd_245922 < baseStart_245922 := by decide
  rcases family_descends (prefixWord ++ tailWord_245922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245970 : List Nat := [3, 2, 2, 2, 1, 2, 1, 5, 2]
def baseStart_245970 : Nat := 118140960795 + 245970 * 2 ^ 59
def prefixEnd_245970 : Nat := 4983230072969 + 3 ^ 40 * 245970 * 2
def baseEnd_245970 : Nat := 112267410299118111061165

theorem tailTrace_245970 : CollatzResearch.WordTrace tailWord_245970 prefixEnd_245970 112267410299118111061165 := by
  unfold tailWord_245970
  simp only [CollatzResearch.WordTrace]
  refine ⟨2242815729725043294163841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5980841945933448784436909 2242815729725043294163841)
  ·
    refine ⟨1682111797293782470622881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2242815729725043294163841 1682111797293782470622881)
    ·
      refine ⟨1261583847970336852967161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1682111797293782470622881 1261583847970336852967161)
      ·
        refine ⟨946187885977752639725371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1261583847970336852967161 946187885977752639725371)
        ·
          refine ⟨1419281828966628959588057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 946187885977752639725371 1419281828966628959588057)
          ·
            refine ⟨1064461371724971719691043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1419281828966628959588057 1064461371724971719691043)
            ·
              refine ⟨1596692057587457579536565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1064461371724971719691043 1596692057587457579536565)
              ·
                refine ⟨149689880398824148081553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1596692057587457579536565 149689880398824148081553)
                ·
                  refine ⟨112267410299118111061165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 149689880398824148081553 112267410299118111061165)
                  ·
                    rfl

theorem cell20_245970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 5, 2].length) (baseStart_245970 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_245970 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_245970 prefixEnd_245970 := by exact prefixLift 245970
  have htrace : WordTrace (prefixWord ++ tailWord_245970) baseStart_245970 baseEnd_245970 := by
    simpa [prefixWord, tailWord_245970, baseEnd_245970] using wordTrace_append hprefix tailTrace_245970
  have hstable : (prefixWord ++ tailWord_245970).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245970).length < 2 ^ (prefixWord ++ tailWord_245970).sum := by decide
  have hdescent : baseEnd_245970 < baseStart_245970 := by decide
  rcases family_descends (prefixWord ++ tailWord_245970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_245991 : List Nat := [1, 1, 5, 3, 1, 1, 1, 3, 4]
def baseStart_245991 : Nat := 118140960795 + 245991 * 2 ^ 59
def prefixEnd_245991 : Nat := 4983230072969 + 3 ^ 40 * 245991 * 2
def baseEnd_245991 : Nat := 112276995271335371361079

theorem tailTrace_245991 : CollatzResearch.WordTrace tailWord_245991 prefixEnd_245991 112276995271335371361079 := by
  unfold tailWord_245991
  simp only [CollatzResearch.WordTrace]
  refine ⟨8972028851824093763169827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5981352567882729175446551 8972028851824093763169827)
  ·
    refine ⟨13458043277736140644754741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8972028851824093763169827 13458043277736140644754741)
    ·
      refine ⟨1261691557287763185445757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13458043277736140644754741 1261691557287763185445757)
      ·
        refine ⟨473134333982911194542159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1261691557287763185445757 473134333982911194542159)
        ·
          refine ⟨709701500974366791813239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473134333982911194542159 709701500974366791813239)
          ·
            refine ⟨1064552251461550187719859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 709701500974366791813239 1064552251461550187719859)
            ·
              refine ⟨1596828377192325281579789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1064552251461550187719859 1596828377192325281579789)
              ·
                refine ⟨598810641447121980592421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1596828377192325281579789 598810641447121980592421)
                ·
                  refine ⟨112276995271335371361079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 598810641447121980592421 112276995271335371361079)
                  ·
                    rfl

theorem cell20_245991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 3, 4].length) (baseStart_245991 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_245991 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_245991 prefixEnd_245991 := by exact prefixLift 245991
  have htrace : WordTrace (prefixWord ++ tailWord_245991) baseStart_245991 baseEnd_245991 := by
    simpa [prefixWord, tailWord_245991, baseEnd_245991] using wordTrace_append hprefix tailTrace_245991
  have hstable : (prefixWord ++ tailWord_245991).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_245991).length < 2 ^ (prefixWord ++ tailWord_245991).sum := by decide
  have hdescent : baseEnd_245991 < baseStart_245991 := by decide
  rcases family_descends (prefixWord ++ tailWord_245991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246019 : List Nat := [1, 1, 1, 3, 2, 3, 3, 6]
def baseStart_246019 : Nat := 118140960795 + 246019 * 2 ^ 59
def prefixEnd_246019 : Nat := 4983230072969 + 3 ^ 40 * 246019 * 2
def baseEnd_246019 : Nat := 37429925078097239475877

theorem tailTrace_246019 : CollatzResearch.WordTrace tailWord_246019 prefixEnd_246019 37429925078097239475877 := by
  unfold tailWord_246019
  simp only [CollatzResearch.WordTrace]
  refine ⟨8973050095722654545189111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5982033397148436363459407 8973050095722654545189111)
  ·
    refine ⟨13459575143583981817783667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8973050095722654545189111 13459575143583981817783667)
    ·
      refine ⟨20189362715375972726675501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13459575143583981817783667 20189362715375972726675501)
      ·
        refine ⟨7571011018265989772503313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20189362715375972726675501 7571011018265989772503313)
        ·
          refine ⟨5678258263699492329377485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7571011018265989772503313 5678258263699492329377485)
          ·
            refine ⟨2129346848887309623516557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5678258263699492329377485 2129346848887309623516557)
            ·
              refine ⟨798505068332741108818709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2129346848887309623516557 798505068332741108818709)
              ·
                refine ⟨37429925078097239475877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 798505068332741108818709 37429925078097239475877)
                ·
                  rfl

theorem cell20_246019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 6].length) (baseStart_246019 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_246019 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_246019 prefixEnd_246019 := by exact prefixLift 246019
  have htrace : WordTrace (prefixWord ++ tailWord_246019) baseStart_246019 baseEnd_246019 := by
    simpa [prefixWord, tailWord_246019, baseEnd_246019] using wordTrace_append hprefix tailTrace_246019
  have hstable : (prefixWord ++ tailWord_246019).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246019).length < 2 ^ (prefixWord ++ tailWord_246019).sum := by decide
  have hdescent : baseEnd_246019 < baseStart_246019 := by decide
  rcases family_descends (prefixWord ++ tailWord_246019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246056 : List Nat := [2, 1, 5, 1, 3, 2, 2, 1, 3]
def baseStart_246056 : Nat := 118140960795 + 246056 * 2 ^ 59
def prefixEnd_246056 : Nat := 4983230072969 + 3 ^ 40 * 246056 * 2
def baseEnd_246056 : Nat := 112306663042484034194147

theorem tailTrace_246056 : CollatzResearch.WordTrace tailWord_246056 prefixEnd_246056 112306663042484034194147 := by
  unfold tailWord_246056
  simp only [CollatzResearch.WordTrace]
  refine ⟨4487199798294304932143011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5982933064392406576190681 4487199798294304932143011)
  ·
    refine ⟨6730799697441457398214517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4487199798294304932143011 6730799697441457398214517)
    ·
      refine ⟨631012471635136631082611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6730799697441457398214517 631012471635136631082611)
      ·
        refine ⟨946518707452704946623917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 631012471635136631082611 946518707452704946623917)
        ·
          refine ⟨354944515294764354983969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 946518707452704946623917 354944515294764354983969)
          ·
            refine ⟨266208386471073266237977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 354944515294764354983969 266208386471073266237977)
            ·
              refine ⟨199656289853304949678483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 266208386471073266237977 199656289853304949678483)
              ·
                refine ⟨299484434779957424517725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199656289853304949678483 299484434779957424517725)
                ·
                  refine ⟨112306663042484034194147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 299484434779957424517725 112306663042484034194147)
                  ·
                    rfl

theorem cell20_246056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 2, 1, 3].length) (baseStart_246056 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_246056 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_246056 prefixEnd_246056 := by exact prefixLift 246056
  have htrace : WordTrace (prefixWord ++ tailWord_246056) baseStart_246056 baseEnd_246056 := by
    simpa [prefixWord, tailWord_246056, baseEnd_246056] using wordTrace_append hprefix tailTrace_246056
  have hstable : (prefixWord ++ tailWord_246056).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246056).length < 2 ^ (prefixWord ++ tailWord_246056).sum := by decide
  have hdescent : baseEnd_246056 < baseStart_246056 := by decide
  rcases family_descends (prefixWord ++ tailWord_246056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246060 : List Nat := [2, 2, 1, 1, 1, 3, 6, 1, 3]
def baseStart_246060 : Nat := 118140960795 + 246060 * 2 ^ 59
def prefixEnd_246060 : Nat := 4983230072969 + 3 ^ 40 * 246060 * 2
def baseEnd_246060 : Nat := 112308488751477798060797

theorem tailTrace_246060 : CollatzResearch.WordTrace tailWord_246060 prefixEnd_246060 112308488751477798060797 := by
  unfold tailWord_246060
  simp only [CollatzResearch.WordTrace]
  refine ⟨4487272744287059273715817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5983030325716079031621089 4487272744287059273715817)
  ·
    refine ⟨3365454558215294455286863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4487272744287059273715817 3365454558215294455286863)
    ·
      refine ⟨5048181837322941682930295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3365454558215294455286863 5048181837322941682930295)
      ·
        refine ⟨7572272755984412524395443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5048181837322941682930295 7572272755984412524395443)
        ·
          refine ⟨11358409133976618786593165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7572272755984412524395443 11358409133976618786593165)
          ·
            refine ⟨4259403425241232044972437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11358409133976618786593165 4259403425241232044972437)
            ·
              refine ⟨199659535558182752108083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4259403425241232044972437 199659535558182752108083)
              ·
                refine ⟨299489303337274128162125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199659535558182752108083 299489303337274128162125)
                ·
                  refine ⟨112308488751477798060797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 299489303337274128162125 112308488751477798060797)
                  ·
                    rfl

theorem cell20_246060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 3].length) (baseStart_246060 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_246060 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_246060 prefixEnd_246060 := by exact prefixLift 246060
  have htrace : WordTrace (prefixWord ++ tailWord_246060) baseStart_246060 baseEnd_246060 := by
    simpa [prefixWord, tailWord_246060, baseEnd_246060] using wordTrace_append hprefix tailTrace_246060
  have hstable : (prefixWord ++ tailWord_246060).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246060).length < 2 ^ (prefixWord ++ tailWord_246060).sum := by decide
  have hdescent : baseEnd_246060 < baseStart_246060 := by decide
  rcases family_descends (prefixWord ++ tailWord_246060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246064 : List Nat := [2, 1, 1, 1, 2, 2, 2, 2, 7]
def baseStart_246064 : Nat := 118140960795 + 246064 * 2 ^ 59
def prefixEnd_246064 : Nat := 4983230072969 + 3 ^ 40 * 246064 * 2
def baseEnd_246064 : Nat := 112310314460471561927447

theorem tailTrace_246064 : CollatzResearch.WordTrace tailWord_246064 prefixEnd_246064 112310314460471561927447 := by
  unfold tailWord_246064
  simp only [CollatzResearch.WordTrace]
  refine ⟨4487345690279813615288623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5983127587039751487051497 4487345690279813615288623)
  ·
    refine ⟨6731018535419720422932935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4487345690279813615288623 6731018535419720422932935)
    ·
      refine ⟨10096527803129580634399403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6731018535419720422932935 10096527803129580634399403)
      ·
        refine ⟨15144791704694370951599105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10096527803129580634399403 15144791704694370951599105)
        ·
          refine ⟨11358593778520778213699329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15144791704694370951599105 11358593778520778213699329)
          ·
            refine ⟨8518945333890583660274497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11358593778520778213699329 8518945333890583660274497)
            ·
              refine ⟨6389209000417937745205873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8518945333890583660274497 6389209000417937745205873)
              ·
                refine ⟨4791906750313453308904405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6389209000417937745205873 4791906750313453308904405)
                ·
                  refine ⟨112310314460471561927447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4791906750313453308904405 112310314460471561927447)
                  ·
                    rfl

theorem cell20_246064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 7].length) (baseStart_246064 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_246064 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_246064 prefixEnd_246064 := by exact prefixLift 246064
  have htrace : WordTrace (prefixWord ++ tailWord_246064) baseStart_246064 baseEnd_246064 := by
    simpa [prefixWord, tailWord_246064, baseEnd_246064] using wordTrace_append hprefix tailTrace_246064
  have hstable : (prefixWord ++ tailWord_246064).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246064).length < 2 ^ (prefixWord ++ tailWord_246064).sum := by decide
  have hdescent : baseEnd_246064 < baseStart_246064 := by decide
  rcases family_descends (prefixWord ++ tailWord_246064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246108 : List Nat := [2, 2, 4, 3, 1, 2, 1, 5]
def baseStart_246108 : Nat := 118140960795 + 246108 * 2 ^ 59
def prefixEnd_246108 : Nat := 4983230072969 + 3 ^ 40 * 246108 * 2
def baseEnd_246108 : Nat := 37443465753134321486867

theorem tailTrace_246108 : CollatzResearch.WordTrace tailWord_246108 prefixEnd_246108 37443465753134321486867 := by
  unfold tailWord_246108
  simp only [CollatzResearch.WordTrace]
  refine ⟨4488148096200111372589489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5984197461600148496785985 4488148096200111372589489)
  ·
    refine ⟨3366111072150083529442117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4488148096200111372589489 3366111072150083529442117)
    ·
      refine ⟨631145826028140661770397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3366111072150083529442117 631145826028140661770397)
      ·
        refine ⟨236679684760552748163899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 631145826028140661770397 236679684760552748163899)
        ·
          refine ⟨355019527140829122245849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236679684760552748163899 355019527140829122245849)
          ·
            refine ⟨266264645355621841684387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 355019527140829122245849 266264645355621841684387)
            ·
              refine ⟨399396968033432762526581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266264645355621841684387 399396968033432762526581)
              ·
                refine ⟨37443465753134321486867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 399396968033432762526581 37443465753134321486867)
                ·
                  rfl

theorem cell20_246108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 5].length) (baseStart_246108 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_246108 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_246108 prefixEnd_246108 := by exact prefixLift 246108
  have htrace : WordTrace (prefixWord ++ tailWord_246108) baseStart_246108 baseEnd_246108 := by
    simpa [prefixWord, tailWord_246108, baseEnd_246108] using wordTrace_append hprefix tailTrace_246108
  have hstable : (prefixWord ++ tailWord_246108).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246108).length < 2 ^ (prefixWord ++ tailWord_246108).sum := by decide
  have hdescent : baseEnd_246108 < baseStart_246108 := by decide
  rcases family_descends (prefixWord ++ tailWord_246108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246166 : List Nat := [5, 3, 1, 2, 1, 1, 3, 1, 3]
def baseStart_246166 : Nat := 118140960795 + 246166 * 2 ^ 59
def prefixEnd_246166 : Nat := 4983230072969 + 3 ^ 40 * 246166 * 2
def baseEnd_246166 : Nat := 112356870039812540527031

theorem tailTrace_246166 : CollatzResearch.WordTrace tailWord_246166 prefixEnd_246166 112356870039812540527031 := by
  unfold tailWord_246166
  simp only [CollatzResearch.WordTrace]
  refine ⟨561150726636881165674397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5985607750793399100526901 561150726636881165674397)
  ·
    refine ⟨210431522488830437127899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 561150726636881165674397 210431522488830437127899)
    ·
      refine ⟨315647283733245655691849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210431522488830437127899 315647283733245655691849)
      ·
        refine ⟨236735462799934241768887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315647283733245655691849 236735462799934241768887)
        ·
          refine ⟨355103194199901362653331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236735462799934241768887 355103194199901362653331)
          ·
            refine ⟨532654791299852043979997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355103194199901362653331 532654791299852043979997)
            ·
              refine ⟨199745546737444516492499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 532654791299852043979997 199745546737444516492499)
              ·
                refine ⟨299618320106166774738749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199745546737444516492499 299618320106166774738749)
                ·
                  refine ⟨112356870039812540527031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 299618320106166774738749 112356870039812540527031)
                  ·
                    rfl

theorem cell20_246166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_246166 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_246166 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_246166 prefixEnd_246166 := by exact prefixLift 246166
  have htrace : WordTrace (prefixWord ++ tailWord_246166) baseStart_246166 baseEnd_246166 := by
    simpa [prefixWord, tailWord_246166, baseEnd_246166] using wordTrace_append hprefix tailTrace_246166
  have hstable : (prefixWord ++ tailWord_246166).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246166).length < 2 ^ (prefixWord ++ tailWord_246166).sum := by decide
  have hdescent : baseEnd_246166 < baseStart_246166 := by decide
  rcases family_descends (prefixWord ++ tailWord_246166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246184 : List Nat := [2, 1, 6, 1, 1, 3, 2, 4]
def baseStart_246184 : Nat := 118140960795 + 246184 * 2 ^ 59
def prefixEnd_246184 : Nat := 4983230072969 + 3 ^ 40 * 246184 * 2
def baseEnd_246184 : Nat := 37455028576761492642319

theorem tailTrace_246184 : CollatzResearch.WordTrace tailWord_246184 prefixEnd_246184 37455028576761492642319 := by
  unfold tailWord_246184
  simp only [CollatzResearch.WordTrace]
  refine ⟨4489534070062443862472803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5986045426749925149963737 4489534070062443862472803)
  ·
    refine ⟨6734301105093665793709205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4489534070062443862472803 6734301105093665793709205)
    ·
      refine ⟨315670364301265584080119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 6734301105093665793709205 315670364301265584080119)
      ·
        refine ⟨473505546451898376120179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315670364301265584080119 473505546451898376120179)
        ·
          refine ⟨710258319677847564180269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473505546451898376120179 710258319677847564180269)
          ·
            refine ⟨266346869879192836567601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 710258319677847564180269 266346869879192836567601)
            ·
              refine ⟨199760152409394627425701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 266346869879192836567601 199760152409394627425701)
              ·
                refine ⟨37455028576761492642319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 199760152409394627425701 37455028576761492642319)
                ·
                  rfl

theorem cell20_246184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 2, 4].length) (baseStart_246184 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_246184 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_246184 prefixEnd_246184 := by exact prefixLift 246184
  have htrace : WordTrace (prefixWord ++ tailWord_246184) baseStart_246184 baseEnd_246184 := by
    simpa [prefixWord, tailWord_246184, baseEnd_246184] using wordTrace_append hprefix tailTrace_246184
  have hstable : (prefixWord ++ tailWord_246184).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246184).length < 2 ^ (prefixWord ++ tailWord_246184).sum := by decide
  have hdescent : baseEnd_246184 < baseStart_246184 := by decide
  rcases family_descends (prefixWord ++ tailWord_246184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246229 : List Nat := [1, 3, 2, 3, 1, 4, 2, 1, 3]
def baseStart_246229 : Nat := 118140960795 + 246229 * 2 ^ 59
def prefixEnd_246229 : Nat := 4983230072969 + 3 ^ 40 * 246229 * 2
def baseEnd_246229 : Nat := 112385624956464321426773

theorem tailTrace_246229 : CollatzResearch.WordTrace tailWord_246229 prefixEnd_246229 112385624956464321426773 := by
  unfold tailWord_246229
  simp only [CollatzResearch.WordTrace]
  refine ⟨8980709424961860410333741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5987139616641240273555827 8980709424961860410333741)
  ·
    refine ⟨3367766034360697653875153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8980709424961860410333741 3367766034360697653875153)
    ·
      refine ⟨2525824525770523240406365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3367766034360697653875153 2525824525770523240406365)
      ·
        refine ⟨947184197163946215152387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2525824525770523240406365 947184197163946215152387)
        ·
          refine ⟨1420776295745919322728581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 947184197163946215152387 1420776295745919322728581)
          ·
            refine ⟨266395555452359873011609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1420776295745919322728581 266395555452359873011609)
            ·
              refine ⟨199796666589269904758707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 266395555452359873011609 199796666589269904758707)
              ·
                refine ⟨299694999883904857138061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199796666589269904758707 299694999883904857138061)
                ·
                  refine ⟨112385624956464321426773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 299694999883904857138061 112385624956464321426773)
                  ·
                    rfl

theorem cell20_246229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 2, 1, 3].length) (baseStart_246229 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_246229 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_246229 prefixEnd_246229 := by exact prefixLift 246229
  have htrace : WordTrace (prefixWord ++ tailWord_246229) baseStart_246229 baseEnd_246229 := by
    simpa [prefixWord, tailWord_246229, baseEnd_246229] using wordTrace_append hprefix tailTrace_246229
  have hstable : (prefixWord ++ tailWord_246229).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246229).length < 2 ^ (prefixWord ++ tailWord_246229).sum := by decide
  have hdescent : baseEnd_246229 < baseStart_246229 := by decide
  rcases family_descends (prefixWord ++ tailWord_246229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246233 : List Nat := [1, 2, 1, 2, 4, 1, 3, 3, 3]
def baseStart_246233 : Nat := 118140960795 + 246233 * 2 ^ 59
def prefixEnd_246233 : Nat := 4983230072969 + 3 ^ 40 * 246233 * 2
def baseEnd_246233 : Nat := 112387450665458085293423

theorem tailTrace_246233 : CollatzResearch.WordTrace tailWord_246233 prefixEnd_246233 112387450665458085293423 := by
  unfold tailWord_246233
  simp only [CollatzResearch.WordTrace]
  refine ⟨8980855316947369093479353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5987236877964912728986235 8980855316947369093479353)
  ·
    refine ⟨6735641487710526820109515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8980855316947369093479353 6735641487710526820109515)
    ·
      refine ⟨10103462231565790230164273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6735641487710526820109515 10103462231565790230164273)
      ·
        refine ⟨7577596673674342672623205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10103462231565790230164273 7577596673674342672623205)
        ·
          refine ⟨1420799376313939251116851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7577596673674342672623205 1420799376313939251116851)
          ·
            refine ⟨2131199064470908876675277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1420799376313939251116851 2131199064470908876675277)
            ·
              refine ⟨799199649176590828753229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2131199064470908876675277 799199649176590828753229)
              ·
                refine ⟨299699868441221560782461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 799199649176590828753229 299699868441221560782461)
                ·
                  refine ⟨112387450665458085293423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 299699868441221560782461 112387450665458085293423)
                  ·
                    rfl

theorem cell20_246233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 3, 3].length) (baseStart_246233 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_246233 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_246233 prefixEnd_246233 := by exact prefixLift 246233
  have htrace : WordTrace (prefixWord ++ tailWord_246233) baseStart_246233 baseEnd_246233 := by
    simpa [prefixWord, tailWord_246233, baseEnd_246233] using wordTrace_append hprefix tailTrace_246233
  have hstable : (prefixWord ++ tailWord_246233).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246233).length < 2 ^ (prefixWord ++ tailWord_246233).sum := by decide
  have hdescent : baseEnd_246233 < baseStart_246233 := by decide
  rcases family_descends (prefixWord ++ tailWord_246233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246247 : List Nat := [1, 1, 5, 2, 1, 1, 1, 8]
def baseStart_246247 : Nat := 118140960795 + 246247 * 2 ^ 59
def prefixEnd_246247 : Nat := 4983230072969 + 3 ^ 40 * 246247 * 2
def baseEnd_246247 : Nat := 37464613548978752942233

theorem tailTrace_246247 : CollatzResearch.WordTrace tailWord_246247 prefixEnd_246247 37464613548978752942233 := by
  unfold tailWord_246247
  simp only [CollatzResearch.WordTrace]
  refine ⟨8981365938896649484488995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5987577292597766322992663 8981365938896649484488995)
  ·
    refine ⟨13472048908344974226733493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8981365938896649484488995 13472048908344974226733493)
    ·
      refine ⟨1263004585157341333756265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13472048908344974226733493 1263004585157341333756265)
      ·
        refine ⟨947253438868006000317199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1263004585157341333756265 947253438868006000317199)
        ·
          refine ⟨1420880158302009000475799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 947253438868006000317199 1420880158302009000475799)
          ·
            refine ⟨2131320237453013500713699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1420880158302009000475799 2131320237453013500713699)
            ·
              refine ⟨3196980356179520251070549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2131320237453013500713699 3196980356179520251070549)
              ·
                refine ⟨37464613548978752942233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3196980356179520251070549 37464613548978752942233)
                ·
                  rfl

theorem cell20_246247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 8].length) (baseStart_246247 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_246247 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_246247 prefixEnd_246247 := by exact prefixLift 246247
  have htrace : WordTrace (prefixWord ++ tailWord_246247) baseStart_246247 baseEnd_246247 := by
    simpa [prefixWord, tailWord_246247, baseEnd_246247] using wordTrace_append hprefix tailTrace_246247
  have hstable : (prefixWord ++ tailWord_246247).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246247).length < 2 ^ (prefixWord ++ tailWord_246247).sum := by decide
  have hdescent : baseEnd_246247 < baseStart_246247 := by decide
  rcases family_descends (prefixWord ++ tailWord_246247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246257 : List Nat := [1, 2, 2, 2, 3, 1, 2, 5, 2]
def baseStart_246257 : Nat := 118140960795 + 246257 * 2 ^ 59
def prefixEnd_246257 : Nat := 4983230072969 + 3 ^ 40 * 246257 * 2
def baseEnd_246257 : Nat := 112398404919420668493325

theorem tailTrace_246257 : CollatzResearch.WordTrace tailWord_246257 prefixEnd_246257 112398404919420668493325 := by
  unfold tailWord_246257
  simp only [CollatzResearch.WordTrace]
  refine ⟨8981730668860421192353025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5987820445906947461568683 8981730668860421192353025)
  ·
    refine ⟨6736298001645315894264769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8981730668860421192353025 6736298001645315894264769)
    ·
      refine ⟨5052223501233986920698577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6736298001645315894264769 5052223501233986920698577)
      ·
        refine ⟨3789167625925490190523933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5052223501233986920698577 3789167625925490190523933)
        ·
          refine ⟨1420937859722058821446475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3789167625925490190523933 1420937859722058821446475)
          ·
            refine ⟨2131406789583088232169713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1420937859722058821446475 2131406789583088232169713)
            ·
              refine ⟨1598555092187316174127285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2131406789583088232169713 1598555092187316174127285)
              ·
                refine ⟨149864539892560891324433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1598555092187316174127285 149864539892560891324433)
                ·
                  refine ⟨112398404919420668493325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 149864539892560891324433 112398404919420668493325)
                  ·
                    rfl

theorem cell20_246257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 5, 2].length) (baseStart_246257 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_246257 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_246257 prefixEnd_246257 := by exact prefixLift 246257
  have htrace : WordTrace (prefixWord ++ tailWord_246257) baseStart_246257 baseEnd_246257 := by
    simpa [prefixWord, tailWord_246257, baseEnd_246257] using wordTrace_append hprefix tailTrace_246257
  have hstable : (prefixWord ++ tailWord_246257).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246257).length < 2 ^ (prefixWord ++ tailWord_246257).sum := by decide
  have hdescent : baseEnd_246257 < baseStart_246257 := by decide
  rcases family_descends (prefixWord ++ tailWord_246257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246271 : List Nat := [1, 1, 2, 2, 1, 2, 6, 2, 3]
def baseStart_246271 : Nat := 118140960795 + 246271 * 2 ^ 59
def prefixEnd_246271 : Nat := 4983230072969 + 3 ^ 40 * 246271 * 2
def baseEnd_246271 : Nat := 112404794900898842026601

theorem tailTrace_246271 : CollatzResearch.WordTrace tailWord_246271 prefixEnd_246271 112404794900898842026601 := by
  unfold tailWord_246271
  simp only [CollatzResearch.WordTrace]
  refine ⟨8982241290809701583362667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5988160860539801055575111 8982241290809701583362667)
  ·
    refine ⟨13473361936214552375044001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8982241290809701583362667 13473361936214552375044001)
    ·
      refine ⟨10105021452160914281283001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13473361936214552375044001 10105021452160914281283001)
      ·
        refine ⟨7578766089120685710962251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10105021452160914281283001 7578766089120685710962251)
        ·
          refine ⟨11368149133681028566443377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7578766089120685710962251 11368149133681028566443377)
          ·
            refine ⟨8526111850260771424832533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11368149133681028566443377 8526111850260771424832533)
            ·
              refine ⟨399661492980973660539025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8526111850260771424832533 399661492980973660539025)
              ·
                refine ⟨299746119735730245404269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 399661492980973660539025 299746119735730245404269)
                ·
                  refine ⟨112404794900898842026601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 299746119735730245404269 112404794900898842026601)
                  ·
                    rfl

theorem cell20_246271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 2, 3].length) (baseStart_246271 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_246271 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_246271 prefixEnd_246271 := by exact prefixLift 246271
  have htrace : WordTrace (prefixWord ++ tailWord_246271) baseStart_246271 baseEnd_246271 := by
    simpa [prefixWord, tailWord_246271, baseEnd_246271] using wordTrace_append hprefix tailTrace_246271
  have hstable : (prefixWord ++ tailWord_246271).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246271).length < 2 ^ (prefixWord ++ tailWord_246271).sum := by decide
  have hdescent : baseEnd_246271 < baseStart_246271 := by decide
  rcases family_descends (prefixWord ++ tailWord_246271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246312 : List Nat := [2, 1, 5, 2, 1, 1, 1, 5, 2]
def baseStart_246312 : Nat := 118140960795 + 246312 * 2 ^ 59
def prefixEnd_246312 : Nat := 4983230072969 + 3 ^ 40 * 246312 * 2
def baseEnd_246312 : Nat := 112423508418084921659767

theorem tailTrace_246312 : CollatzResearch.WordTrace tailWord_246312 prefixEnd_246312 112423508418084921659767 := by
  unfold tailWord_246312
  simp only [CollatzResearch.WordTrace]
  refine ⟨4491868341830582792802595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5989157789107443723736793 4491868341830582792802595)
  ·
    refine ⟨6737802512745874189203893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4491868341830582792802595 6737802512745874189203893)
    ·
      refine ⟨631668985569925705237865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6737802512745874189203893 631668985569925705237865)
      ·
        refine ⟨473751739177444278928399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 631668985569925705237865 473751739177444278928399)
        ·
          refine ⟨710627608766166418392599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473751739177444278928399 710627608766166418392599)
          ·
            refine ⟨1065941413149249627588899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 710627608766166418392599 1065941413149249627588899)
            ·
              refine ⟨1598912119723874441383349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1065941413149249627588899 1598912119723874441383349)
              ·
                refine ⟨149898011224113228879689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1598912119723874441383349 149898011224113228879689)
                ·
                  refine ⟨112423508418084921659767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 149898011224113228879689 112423508418084921659767)
                  ·
                    rfl

theorem cell20_246312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 5, 2].length) (baseStart_246312 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_246312 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_246312 prefixEnd_246312 := by exact prefixLift 246312
  have htrace : WordTrace (prefixWord ++ tailWord_246312) baseStart_246312 baseEnd_246312 := by
    simpa [prefixWord, tailWord_246312, baseEnd_246312] using wordTrace_append hprefix tailTrace_246312
  have hstable : (prefixWord ++ tailWord_246312).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246312).length < 2 ^ (prefixWord ++ tailWord_246312).sum := by decide
  have hdescent : baseEnd_246312 < baseStart_246312 := by decide
  rcases family_descends (prefixWord ++ tailWord_246312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246326 : List Nat := [5, 1, 2, 1, 2, 2, 1, 1, 5]
def baseStart_246326 : Nat := 118140960795 + 246326 * 2 ^ 59
def prefixEnd_246326 : Nat := 4983230072969 + 3 ^ 40 * 246326 * 2
def baseEnd_246326 : Nat := 112429898399563095193043

theorem tailTrace_246326 : CollatzResearch.WordTrace tailWord_246326 prefixEnd_246326 112429898399563095193043 := by
  unfold tailWord_246326
  simp only [CollatzResearch.WordTrace]
  refine ⟨561515456600652873538427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5989498203740297317743221 561515456600652873538427)
  ·
    refine ⟨842273184900979310307641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 561515456600652873538427 842273184900979310307641)
    ·
      refine ⟨631704888675734482730731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 842273184900979310307641 631704888675734482730731)
      ·
        refine ⟨947557333013601724096097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 631704888675734482730731 947557333013601724096097)
        ·
          refine ⟨710667999760201293072073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 947557333013601724096097 710667999760201293072073)
          ·
            refine ⟨533000999820150969804055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 710667999760201293072073 533000999820150969804055)
            ·
              refine ⟨799501499730226454706083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 533000999820150969804055 799501499730226454706083)
              ·
                refine ⟨1199252249595339682059125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 799501499730226454706083 1199252249595339682059125)
                ·
                  refine ⟨112429898399563095193043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1199252249595339682059125 112429898399563095193043)
                  ·
                    rfl

theorem cell20_246326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_246326 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_246326 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_246326 prefixEnd_246326 := by exact prefixLift 246326
  have htrace : WordTrace (prefixWord ++ tailWord_246326) baseStart_246326 baseEnd_246326 := by
    simpa [prefixWord, tailWord_246326, baseEnd_246326] using wordTrace_append hprefix tailTrace_246326
  have hstable : (prefixWord ++ tailWord_246326).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246326).length < 2 ^ (prefixWord ++ tailWord_246326).sum := by decide
  have hdescent : baseEnd_246326 < baseStart_246326 := by decide
  rcases family_descends (prefixWord ++ tailWord_246326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246333 : List Nat := [1, 4, 1, 3, 2, 2, 2, 1, 4]
def baseStart_246333 : Nat := 118140960795 + 246333 * 2 ^ 59
def prefixEnd_246333 : Nat := 4983230072969 + 3 ^ 40 * 246333 * 2
def baseEnd_246333 : Nat := 112433093390302181959681

theorem tailTrace_246333 : CollatzResearch.WordTrace tailWord_246333 prefixEnd_246333 112433093390302181959681 := by
  unfold tailWord_246333
  simp only [CollatzResearch.WordTrace]
  refine ⟨8984502616585086172119653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5989668411056724114746435 8984502616585086172119653)
  ·
    refine ⟨1684594240609703657272435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8984502616585086172119653 1684594240609703657272435)
    ·
      refine ⟨2526891360914555485908653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1684594240609703657272435 2526891360914555485908653)
      ·
        refine ⟨947584260342958307215745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2526891360914555485908653 947584260342958307215745)
        ·
          refine ⟨710688195257218730411809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 947584260342958307215745 710688195257218730411809)
          ·
            refine ⟨533016146442914047808857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 710688195257218730411809 533016146442914047808857)
            ·
              refine ⟨399762109832185535856643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 533016146442914047808857 399762109832185535856643)
              ·
                refine ⟨599643164748278303784965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 399762109832185535856643 599643164748278303784965)
                ·
                  refine ⟨112433093390302181959681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 599643164748278303784965 112433093390302181959681)
                  ·
                    rfl

theorem cell20_246333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_246333 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_246333 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_246333 prefixEnd_246333 := by exact prefixLift 246333
  have htrace : WordTrace (prefixWord ++ tailWord_246333) baseStart_246333 baseEnd_246333 := by
    simpa [prefixWord, tailWord_246333, baseEnd_246333] using wordTrace_append hprefix tailTrace_246333
  have hstable : (prefixWord ++ tailWord_246333).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246333).length < 2 ^ (prefixWord ++ tailWord_246333).sum := by decide
  have hdescent : baseEnd_246333 < baseStart_246333 := by decide
  rcases family_descends (prefixWord ++ tailWord_246333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246354 : List Nat := [3, 2, 2, 1, 2, 1, 1, 4, 4]
def baseStart_246354 : Nat := 118140960795 + 246354 * 2 ^ 59
def prefixEnd_246354 : Nat := 4983230072969 + 3 ^ 40 * 246354 * 2
def baseEnd_246354 : Nat := 112442678362519442259595

theorem tailTrace_246354 : CollatzResearch.WordTrace tailWord_246354 prefixEnd_246354 112442678362519442259595 := by
  unfold tailWord_246354
  simp only [CollatzResearch.WordTrace]
  refine ⟨2246317137377251689658529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5990179033006004505756077 2246317137377251689658529)
  ·
    refine ⟨1684737853032938767243897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2246317137377251689658529 1684737853032938767243897)
    ·
      refine ⟨1263553389774704075432923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1684737853032938767243897 1263553389774704075432923)
      ·
        refine ⟨1895330084662056113149385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1263553389774704075432923 1895330084662056113149385)
        ·
          refine ⟨1421497563496542084862039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1895330084662056113149385 1421497563496542084862039)
          ·
            refine ⟨2132246345244813127293059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1421497563496542084862039 2132246345244813127293059)
            ·
              refine ⟨3198369517867219690939589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2132246345244813127293059 3198369517867219690939589)
              ·
                refine ⟨599694284600103692051173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3198369517867219690939589 599694284600103692051173)
                ·
                  refine ⟨112442678362519442259595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 599694284600103692051173 112442678362519442259595)
                  ·
                    rfl

theorem cell20_246354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_246354 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_246354 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_246354 prefixEnd_246354 := by exact prefixLift 246354
  have htrace : WordTrace (prefixWord ++ tailWord_246354) baseStart_246354 baseEnd_246354 := by
    simpa [prefixWord, tailWord_246354, baseEnd_246354] using wordTrace_append hprefix tailTrace_246354
  have hstable : (prefixWord ++ tailWord_246354).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246354).length < 2 ^ (prefixWord ++ tailWord_246354).sum := by decide
  have hdescent : baseEnd_246354 < baseStart_246354 := by decide
  rcases family_descends (prefixWord ++ tailWord_246354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246368 : List Nat := [2, 1, 1, 3, 2, 1, 3, 2, 5]
def baseStart_246368 : Nat := 118140960795 + 246368 * 2 ^ 59
def prefixEnd_246368 : Nat := 4983230072969 + 3 ^ 40 * 246368 * 2
def baseEnd_246368 : Nat := 112449068343997615792871

theorem tailTrace_246368 : CollatzResearch.WordTrace tailWord_246368 prefixEnd_246368 112449068343997615792871 := by
  unfold tailWord_246368
  simp only [CollatzResearch.WordTrace]
  refine ⟨4492889585729143574821879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5990519447638858099762505 4492889585729143574821879)
  ·
    refine ⟨6739334378593715362232819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4492889585729143574821879 6739334378593715362232819)
    ·
      refine ⟨10109001567890573043349229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6739334378593715362232819 10109001567890573043349229)
      ·
        refine ⟨3790875587958964891255961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10109001567890573043349229 3790875587958964891255961)
        ·
          refine ⟨2843156690969223668441971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3790875587958964891255961 2843156690969223668441971)
          ·
            refine ⟨4264735036453835502662957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2843156690969223668441971 4264735036453835502662957)
            ·
              refine ⟨1599275638670188313498609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4264735036453835502662957 1599275638670188313498609)
              ·
                refine ⟨1199456729002641235123957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1599275638670188313498609 1199456729002641235123957)
                ·
                  refine ⟨112449068343997615792871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1199456729002641235123957 112449068343997615792871)
                  ·
                    rfl

theorem cell20_246368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2, 5].length) (baseStart_246368 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_246368 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_246368 prefixEnd_246368 := by exact prefixLift 246368
  have htrace : WordTrace (prefixWord ++ tailWord_246368) baseStart_246368 baseEnd_246368 := by
    simpa [prefixWord, tailWord_246368, baseEnd_246368] using wordTrace_append hprefix tailTrace_246368
  have hstable : (prefixWord ++ tailWord_246368).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246368).length < 2 ^ (prefixWord ++ tailWord_246368).sum := by decide
  have hdescent : baseEnd_246368 < baseStart_246368 := by decide
  rcases family_descends (prefixWord ++ tailWord_246368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246439 : List Nat := [1, 1, 6, 3, 2, 1, 2, 2, 2]
def baseStart_246439 : Nat := 118140960795 + 246439 * 2 ^ 59
def prefixEnd_246439 : Nat := 4983230072969 + 3 ^ 40 * 246439 * 2
def baseEnd_246439 : Nat := 112481474678636924425915

theorem tailTrace_246439 : CollatzResearch.WordTrace tailWord_246439 prefixEnd_246439 112481474678636924425915 := by
  unfold tailWord_246439
  simp only [CollatzResearch.WordTrace]
  refine ⟨8988368754201066275478371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5992245836134044183652247 8988368754201066275478371)
  ·
    refine ⟨13482553131301599413217557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8988368754201066275478371 13482553131301599413217557)
    ·
      refine ⟨631994678029762472494573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 13482553131301599413217557 631994678029762472494573)
      ·
        refine ⟨236998004261160927185465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 631994678029762472494573 236998004261160927185465)
        ·
          refine ⟨177748503195870695389099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236998004261160927185465 177748503195870695389099)
          ·
            refine ⟨266622754793806043083649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177748503195870695389099 266622754793806043083649)
            ·
              refine ⟨199967066095354532312737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 266622754793806043083649 199967066095354532312737)
              ·
                refine ⟨149975299571515899234553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 199967066095354532312737 149975299571515899234553)
                ·
                  refine ⟨112481474678636924425915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 149975299571515899234553 112481474678636924425915)
                  ·
                    rfl

theorem cell20_246439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 2, 2, 2].length) (baseStart_246439 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_246439 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_246439 prefixEnd_246439 := by exact prefixLift 246439
  have htrace : WordTrace (prefixWord ++ tailWord_246439) baseStart_246439 baseEnd_246439 := by
    simpa [prefixWord, tailWord_246439, baseEnd_246439] using wordTrace_append hprefix tailTrace_246439
  have hstable : (prefixWord ++ tailWord_246439).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246439).length < 2 ^ (prefixWord ++ tailWord_246439).sum := by decide
  have hdescent : baseEnd_246439 < baseStart_246439 := by decide
  rcases family_descends (prefixWord ++ tailWord_246439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246447 : List Nat := [1, 1, 2, 1, 2, 6, 1, 4, 2]
def baseStart_246447 : Nat := 118140960795 + 246447 * 2 ^ 59
def prefixEnd_246447 : Nat := 4983230072969 + 3 ^ 40 * 246447 * 2
def baseEnd_246447 : Nat := 112485126096624452159215

theorem tailTrace_246447 : CollatzResearch.WordTrace tailWord_246447 prefixEnd_246447 112485126096624452159215 := by
  unfold tailWord_246447
  simp only [CollatzResearch.WordTrace]
  refine ⟨8988660538172083641769595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5992440358781389094513063 8988660538172083641769595)
  ·
    refine ⟨13482990807258125462654393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8988660538172083641769595 13482990807258125462654393)
    ·
      refine ⟨10112243105443594096990795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13482990807258125462654393 10112243105443594096990795)
      ·
        refine ⟨15168364658165391145486193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10112243105443594096990795 15168364658165391145486193)
        ·
          refine ⟨11376273493624043359114645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15168364658165391145486193 11376273493624043359114645)
          ·
            refine ⟨533262820013627032458499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 11376273493624043359114645 533262820013627032458499)
            ·
              refine ⟨799894230020440548687749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 533262820013627032458499 799894230020440548687749)
              ·
                refine ⟨149980168128832602878953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 799894230020440548687749 149980168128832602878953)
                ·
                  refine ⟨112485126096624452159215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 149980168128832602878953 112485126096624452159215)
                  ·
                    rfl

theorem cell20_246447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 4, 2].length) (baseStart_246447 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_246447 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_246447 prefixEnd_246447 := by exact prefixLift 246447
  have htrace : WordTrace (prefixWord ++ tailWord_246447) baseStart_246447 baseEnd_246447 := by
    simpa [prefixWord, tailWord_246447, baseEnd_246447] using wordTrace_append hprefix tailTrace_246447
  have hstable : (prefixWord ++ tailWord_246447).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246447).length < 2 ^ (prefixWord ++ tailWord_246447).sum := by decide
  have hdescent : baseEnd_246447 < baseStart_246447 := by decide
  rcases family_descends (prefixWord ++ tailWord_246447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246461 : List Nat := [1, 4, 1, 2, 1, 3, 2, 3, 3]
def baseStart_246461 : Nat := 118140960795 + 246461 * 2 ^ 59
def prefixEnd_246461 : Nat := 4983230072969 + 3 ^ 40 * 246461 * 2
def baseEnd_246461 : Nat := 112491516078102625692491

theorem tailTrace_246461 : CollatzResearch.WordTrace tailWord_246461 prefixEnd_246461 112491516078102625692491 := by
  unfold tailWord_246461
  simp only [CollatzResearch.WordTrace]
  refine ⟨8989171160121364032779237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5992780773414242688519491 8989171160121364032779237)
  ·
    refine ⟨1685469592522755756146107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8989171160121364032779237 1685469592522755756146107)
    ·
      refine ⟨2528204388784133634219161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1685469592522755756146107 2528204388784133634219161)
      ·
        refine ⟨1896153291588100225664371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2528204388784133634219161 1896153291588100225664371)
        ·
          refine ⟨2844229937382150338496557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1896153291588100225664371 2844229937382150338496557)
          ·
            refine ⟨1066586226518306376936209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2844229937382150338496557 1066586226518306376936209)
            ·
              refine ⟨799939669888729782702157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1066586226518306376936209 799939669888729782702157)
              ·
                refine ⟨299977376208273668513309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 799939669888729782702157 299977376208273668513309)
                ·
                  refine ⟨112491516078102625692491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 299977376208273668513309 112491516078102625692491)
                  ·
                    rfl

theorem cell20_246461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 3, 3].length) (baseStart_246461 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_246461 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_246461 prefixEnd_246461 := by exact prefixLift 246461
  have htrace : WordTrace (prefixWord ++ tailWord_246461) baseStart_246461 baseEnd_246461 := by
    simpa [prefixWord, tailWord_246461, baseEnd_246461] using wordTrace_append hprefix tailTrace_246461
  have hstable : (prefixWord ++ tailWord_246461).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246461).length < 2 ^ (prefixWord ++ tailWord_246461).sum := by decide
  have hdescent : baseEnd_246461 < baseStart_246461 := by decide
  rcases family_descends (prefixWord ++ tailWord_246461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246468 : List Nat := [2, 3, 3, 1, 1, 2, 1, 1, 6]
def baseStart_246468 : Nat := 118140960795 + 246468 * 2 ^ 59
def prefixEnd_246468 : Nat := 4983230072969 + 3 ^ 40 * 246468 * 2
def baseEnd_246468 : Nat := 112494711068841712459129

theorem tailTrace_246468 : CollatzResearch.WordTrace tailWord_246468 prefixEnd_246468 112494711068841712459129 := by
  unfold tailWord_246468
  simp only [CollatzResearch.WordTrace]
  refine ⟨4494713235548002114142029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5992950980730669485522705 4494713235548002114142029)
  ·
    refine ⟨1685517463330500792803261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4494713235548002114142029 1685517463330500792803261)
    ·
      refine ⟨632069048748937797301223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1685517463330500792803261 632069048748937797301223)
      ·
        refine ⟨948103573123406695951835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 632069048748937797301223 948103573123406695951835)
        ·
          refine ⟨1422155359685110043927753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 948103573123406695951835 1422155359685110043927753)
          ·
            refine ⟨1066616519763832532945815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1422155359685110043927753 1066616519763832532945815)
            ·
              refine ⟨1599924779645748799418723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1066616519763832532945815 1599924779645748799418723)
              ·
                refine ⟨2399887169468623199128085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1599924779645748799418723 2399887169468623199128085)
                ·
                  refine ⟨112494711068841712459129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2399887169468623199128085 112494711068841712459129)
                  ·
                    rfl

theorem cell20_246468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_246468 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_246468 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_246468 prefixEnd_246468 := by exact prefixLift 246468
  have htrace : WordTrace (prefixWord ++ tailWord_246468) baseStart_246468 baseEnd_246468 := by
    simpa [prefixWord, tailWord_246468, baseEnd_246468] using wordTrace_append hprefix tailTrace_246468
  have hstable : (prefixWord ++ tailWord_246468).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246468).length < 2 ^ (prefixWord ++ tailWord_246468).sum := by decide
  have hdescent : baseEnd_246468 < baseStart_246468 := by decide
  rcases family_descends (prefixWord ++ tailWord_246468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246489 : List Nat := [1, 2, 1, 2, 3, 2, 1, 2, 6]
def baseStart_246489 : Nat := 118140960795 + 246489 * 2 ^ 59
def prefixEnd_246489 : Nat := 4983230072969 + 3 ^ 40 * 246489 * 2
def baseEnd_246489 : Nat := 112504296041058972759043

theorem tailTrace_246489 : CollatzResearch.WordTrace tailWord_246489 prefixEnd_246489 112504296041058972759043 := by
  unfold tailWord_246489
  simp only [CollatzResearch.WordTrace]
  refine ⟨8990192404019924814798521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5993461602679949876532347 8990192404019924814798521)
  ·
    refine ⟨6742644303014943611098891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8990192404019924814798521 6742644303014943611098891)
    ·
      refine ⟨10113966454522415416648337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6742644303014943611098891 10113966454522415416648337)
      ·
        refine ⟨7585474840891811562486253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10113966454522415416648337 7585474840891811562486253)
        ·
          refine ⟨2844553065334429335932345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7585474840891811562486253 2844553065334429335932345)
          ·
            refine ⟨2133414799000822001949259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2844553065334429335932345 2133414799000822001949259)
            ·
              refine ⟨3200122198501233002923889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2133414799000822001949259 3200122198501233002923889)
              ·
                refine ⟨2400091648875924752192917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3200122198501233002923889 2400091648875924752192917)
                ·
                  refine ⟨112504296041058972759043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2400091648875924752192917 112504296041058972759043)
                  ·
                    rfl

theorem cell20_246489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 6].length) (baseStart_246489 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_246489 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_246489 prefixEnd_246489 := by exact prefixLift 246489
  have htrace : WordTrace (prefixWord ++ tailWord_246489) baseStart_246489 baseEnd_246489 := by
    simpa [prefixWord, tailWord_246489, baseEnd_246489] using wordTrace_append hprefix tailTrace_246489
  have hstable : (prefixWord ++ tailWord_246489).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246489).length < 2 ^ (prefixWord ++ tailWord_246489).sum := by decide
  have hdescent : baseEnd_246489 < baseStart_246489 := by decide
  rcases family_descends (prefixWord ++ tailWord_246489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246492 : List Nat := [2, 2, 5, 1, 1, 2, 7]
def baseStart_246492 : Nat := 118140960795 + 246492 * 2 ^ 59
def prefixEnd_246492 : Nat := 4983230072969 + 3 ^ 40 * 246492 * 2
def baseEnd_246492 : Nat := 12500629480311588406559

theorem tailTrace_246492 : CollatzResearch.WordTrace tailWord_246492 prefixEnd_246492 12500629480311588406559 := by
  unfold tailWord_246492
  simp only [CollatzResearch.WordTrace]
  refine ⟨4495150911504528163578865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5993534548672704218105153 4495150911504528163578865)
  ·
    refine ⟨3371363183628396122684149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4495150911504528163578865 3371363183628396122684149)
    ·
      refine ⟨316065298465162136501639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3371363183628396122684149 316065298465162136501639)
      ·
        refine ⟨474097947697743204752459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316065298465162136501639 474097947697743204752459)
        ·
          refine ⟨711146921546614807128689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 474097947697743204752459 711146921546614807128689)
          ·
            refine ⟨533360191159961105346517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 711146921546614807128689 533360191159961105346517)
            ·
              refine ⟨12500629480311588406559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 533360191159961105346517 12500629480311588406559)
              ·
                rfl

theorem cell20_246492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 7].length) (baseStart_246492 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_246492 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_246492 prefixEnd_246492 := by exact prefixLift 246492
  have htrace : WordTrace (prefixWord ++ tailWord_246492) baseStart_246492 baseEnd_246492 := by
    simpa [prefixWord, tailWord_246492, baseEnd_246492] using wordTrace_append hprefix tailTrace_246492
  have hstable : (prefixWord ++ tailWord_246492).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246492).length < 2 ^ (prefixWord ++ tailWord_246492).sum := by decide
  have hdescent : baseEnd_246492 < baseStart_246492 := by decide
  rcases family_descends (prefixWord ++ tailWord_246492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246499 : List Nat := [1, 1, 1, 7, 1, 2, 1, 1, 5]
def baseStart_246499 : Nat := 118140960795 + 246499 * 2 ^ 59
def prefixEnd_246499 : Nat := 4983230072969 + 3 ^ 40 * 246499 * 2
def baseEnd_246499 : Nat := 112508860313543382425669

theorem tailTrace_246499 : CollatzResearch.WordTrace tailWord_246499 prefixEnd_246499 112508860313543382425669 := by
  unfold tailWord_246499
  simp only [CollatzResearch.WordTrace]
  refine ⟨8990557133983696522662551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5993704755989131015108367 8990557133983696522662551)
  ·
    refine ⟨13485835700975544783993827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8990557133983696522662551 13485835700975544783993827)
    ·
      refine ⟨20228753551463317175990741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13485835700975544783993827 20228753551463317175990741)
      ·
        refine ⟨474111411362421496312283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 20228753551463317175990741 474111411362421496312283)
        ·
          refine ⟨711167117043632244468425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 474111411362421496312283 711167117043632244468425)
          ·
            refine ⟨533375337782724183351319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 711167117043632244468425 533375337782724183351319)
            ·
              refine ⟨800063006674086275026979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 533375337782724183351319 800063006674086275026979)
              ·
                refine ⟨1200094510011129412540469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 800063006674086275026979 1200094510011129412540469)
                ·
                  refine ⟨112508860313543382425669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1200094510011129412540469 112508860313543382425669)
                  ·
                    rfl

theorem cell20_246499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 1, 5].length) (baseStart_246499 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_246499 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_246499 prefixEnd_246499 := by exact prefixLift 246499
  have htrace : WordTrace (prefixWord ++ tailWord_246499) baseStart_246499 baseEnd_246499 := by
    simpa [prefixWord, tailWord_246499, baseEnd_246499] using wordTrace_append hprefix tailTrace_246499
  have hstable : (prefixWord ++ tailWord_246499).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246499).length < 2 ^ (prefixWord ++ tailWord_246499).sum := by decide
  have hdescent : baseEnd_246499 < baseStart_246499 := by decide
  rcases family_descends (prefixWord ++ tailWord_246499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246530 : List Nat := [3, 4, 1, 1, 1, 3, 1, 6]
def baseStart_246530 : Nat := 118140960795 + 246530 * 2 ^ 59
def prefixEnd_246530 : Nat := 4983230072969 + 3 ^ 40 * 246530 * 2
def baseEnd_246530 : Nat := 37507669852748350797403

theorem tailTrace_246530 : CollatzResearch.WordTrace tailWord_246530 prefixEnd_246530 37507669852748350797403 := by
  unfold tailWord_246530
  simp only [CollatzResearch.WordTrace]
  refine ⟨2247921949217847204260261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5994458531247592544694029 2247921949217847204260261)
  ·
    refine ⟨421485365478346350798799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2247921949217847204260261 421485365478346350798799)
    ·
      refine ⟨632228048217519526198199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421485365478346350798799 632228048217519526198199)
      ·
        refine ⟨948342072326279289297299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 632228048217519526198199 948342072326279289297299)
        ·
          refine ⟨1422513108489418933945949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 948342072326279289297299 1422513108489418933945949)
          ·
            refine ⟨533442415683532100229731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1422513108489418933945949 533442415683532100229731)
            ·
              refine ⟨800163623525298150344597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 533442415683532100229731 800163623525298150344597)
              ·
                refine ⟨37507669852748350797403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 800163623525298150344597 37507669852748350797403)
                ·
                  rfl

theorem cell20_246530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 6].length) (baseStart_246530 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_246530 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_246530 prefixEnd_246530 := by exact prefixLift 246530
  have htrace : WordTrace (prefixWord ++ tailWord_246530) baseStart_246530 baseEnd_246530 := by
    simpa [prefixWord, tailWord_246530, baseEnd_246530] using wordTrace_append hprefix tailTrace_246530
  have hstable : (prefixWord ++ tailWord_246530).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246530).length < 2 ^ (prefixWord ++ tailWord_246530).sum := by decide
  have hdescent : baseEnd_246530 < baseStart_246530 := by decide
  rcases family_descends (prefixWord ++ tailWord_246530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246557 : List Nat := [1, 4, 2, 4, 2, 1, 1, 1, 4]
def baseStart_246557 : Nat := 118140960795 + 246557 * 2 ^ 59
def prefixEnd_246557 : Nat := 4983230072969 + 3 ^ 40 * 246557 * 2
def baseEnd_246557 : Nat := 112535333093952958492099

theorem tailTrace_246557 : CollatzResearch.WordTrace tailWord_246557 prefixEnd_246557 112535333093952958492099 := by
  unfold tailWord_246557
  simp only [CollatzResearch.WordTrace]
  refine ⟨8992672567773572428273925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5995115045182381618849283 8992672567773572428273925)
  ·
    refine ⟨1686126106457544830301361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8992672567773572428273925 1686126106457544830301361)
    ·
      refine ⟨1264594579843158622726021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1686126106457544830301361 1264594579843158622726021)
      ·
        refine ⟨237111483720592241761129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1264594579843158622726021 237111483720592241761129)
        ·
          refine ⟨177833612790444181320847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 237111483720592241761129 177833612790444181320847)
          ·
            refine ⟨266750419185666271981271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177833612790444181320847 266750419185666271981271)
            ·
              refine ⟨400125628778499407971907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266750419185666271981271 400125628778499407971907)
              ·
                refine ⟨600188443167749111957861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 400125628778499407971907 600188443167749111957861)
                ·
                  refine ⟨112535333093952958492099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 600188443167749111957861 112535333093952958492099)
                  ·
                    rfl

theorem cell20_246557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 1, 4].length) (baseStart_246557 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_246557 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_246557 prefixEnd_246557 := by exact prefixLift 246557
  have htrace : WordTrace (prefixWord ++ tailWord_246557) baseStart_246557 baseEnd_246557 := by
    simpa [prefixWord, tailWord_246557, baseEnd_246557] using wordTrace_append hprefix tailTrace_246557
  have hstable : (prefixWord ++ tailWord_246557).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246557).length < 2 ^ (prefixWord ++ tailWord_246557).sum := by decide
  have hdescent : baseEnd_246557 < baseStart_246557 := by decide
  rcases family_descends (prefixWord ++ tailWord_246557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246612 : List Nat := [2, 4, 1, 1, 5, 1, 2, 2, 2]
def baseStart_246612 : Nat := 118140960795 + 246612 * 2 ^ 59
def prefixEnd_246612 : Nat := 4983230072969 + 3 ^ 40 * 246612 * 2
def baseEnd_246612 : Nat := 112560436592617211658541

theorem tailTrace_246612 : CollatzResearch.WordTrace tailWord_246612 prefixEnd_246612 112560436592617211658541 := by
  unfold tailWord_246612
  simp only [CollatzResearch.WordTrace]
  refine ⟨4497339291287158410763045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5996452388382877881017393 4497339291287158410763045)
  ·
    refine ⟨843251117116342202018071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4497339291287158410763045 843251117116342202018071)
    ·
      refine ⟨1264876675674513303027107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 843251117116342202018071 1264876675674513303027107)
      ·
        refine ⟨1897315013511769954540661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1264876675674513303027107 1897315013511769954540661)
        ·
          refine ⟨177873282516728433238187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1897315013511769954540661 177873282516728433238187)
          ·
            refine ⟨266809923775092649857281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177873282516728433238187 266809923775092649857281)
            ·
              refine ⟨200107442831319487392961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 266809923775092649857281 200107442831319487392961)
              ·
                refine ⟨150080582123489615544721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 200107442831319487392961 150080582123489615544721)
                ·
                  refine ⟨112560436592617211658541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150080582123489615544721 112560436592617211658541)
                  ·
                    rfl

theorem cell20_246612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 2, 2, 2].length) (baseStart_246612 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_246612 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_246612 prefixEnd_246612 := by exact prefixLift 246612
  have htrace : WordTrace (prefixWord ++ tailWord_246612) baseStart_246612 baseEnd_246612 := by
    simpa [prefixWord, tailWord_246612, baseEnd_246612] using wordTrace_append hprefix tailTrace_246612
  have hstable : (prefixWord ++ tailWord_246612).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246612).length < 2 ^ (prefixWord ++ tailWord_246612).sum := by decide
  have hdescent : baseEnd_246612 < baseStart_246612 := by decide
  rcases family_descends (prefixWord ++ tailWord_246612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246613 : List Nat := [1, 3, 2, 2, 2, 1, 4, 2, 3]
def baseStart_246613 : Nat := 118140960795 + 246613 * 2 ^ 59
def prefixEnd_246613 : Nat := 4983230072969 + 3 ^ 40 * 246613 * 2
def baseEnd_246613 : Nat := 112560893019865652625203

theorem tailTrace_246613 : CollatzResearch.WordTrace tailWord_246613 prefixEnd_246613 112560893019865652625203 := by
  unfold tailWord_246613
  simp only [CollatzResearch.WordTrace]
  refine ⟨8994715055570693992312493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5996476703713795994874995 8994715055570693992312493)
  ·
    refine ⟨3373018145839010247117185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8994715055570693992312493 3373018145839010247117185)
    ·
      refine ⟨2529763609379257685337889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3373018145839010247117185 2529763609379257685337889)
      ·
        refine ⟨1897322707034443264003417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2529763609379257685337889 1897322707034443264003417)
        ·
          refine ⟨1422992030275832448002563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1897322707034443264003417 1422992030275832448002563)
          ·
            refine ⟨2134488045413748672003845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1422992030275832448002563 2134488045413748672003845)
            ·
              refine ⟨400216508515077876000721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2134488045413748672003845 400216508515077876000721)
              ·
                refine ⟨300162381386308407000541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 400216508515077876000721 300162381386308407000541)
                ·
                  refine ⟨112560893019865652625203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 300162381386308407000541 112560893019865652625203)
                  ·
                    rfl

theorem cell20_246613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 2, 3].length) (baseStart_246613 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_246613 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_246613 prefixEnd_246613 := by exact prefixLift 246613
  have htrace : WordTrace (prefixWord ++ tailWord_246613) baseStart_246613 baseEnd_246613 := by
    simpa [prefixWord, tailWord_246613, baseEnd_246613] using wordTrace_append hprefix tailTrace_246613
  have hstable : (prefixWord ++ tailWord_246613).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246613).length < 2 ^ (prefixWord ++ tailWord_246613).sum := by decide
  have hdescent : baseEnd_246613 < baseStart_246613 := by decide
  rcases family_descends (prefixWord ++ tailWord_246613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246627 : List Nat := [1, 1, 1, 5, 3, 1, 3, 5]
def baseStart_246627 : Nat := 118140960795 + 246627 * 2 ^ 59
def prefixEnd_246627 : Nat := 4983230072969 + 3 ^ 40 * 246627 * 2
def baseEnd_246627 : Nat := 37522427667114608719493

theorem tailTrace_246627 : CollatzResearch.WordTrace tailWord_246627 prefixEnd_246627 37522427667114608719493 := by
  unfold tailWord_246627
  simp only [CollatzResearch.WordTrace]
  refine ⟨8995225677519974383322135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5996817118346649588881423 8995225677519974383322135)
  ·
    refine ⟨13492838516279961574983203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8995225677519974383322135 13492838516279961574983203)
    ·
      refine ⟨20239257774419942362474805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13492838516279961574983203 20239257774419942362474805)
      ·
        refine ⟨1897430416351869596482013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20239257774419942362474805 1897430416351869596482013)
        ·
          refine ⟨711536406131951098680755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1897430416351869596482013 711536406131951098680755)
          ·
            refine ⟨1067304609197926648021133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 711536406131951098680755 1067304609197926648021133)
            ·
              refine ⟨400239228449222493007925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1067304609197926648021133 400239228449222493007925)
              ·
                refine ⟨37522427667114608719493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 400239228449222493007925 37522427667114608719493)
                ·
                  rfl

theorem cell20_246627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 5].length) (baseStart_246627 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_246627 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_246627 prefixEnd_246627 := by exact prefixLift 246627
  have htrace : WordTrace (prefixWord ++ tailWord_246627) baseStart_246627 baseEnd_246627 := by
    simpa [prefixWord, tailWord_246627, baseEnd_246627] using wordTrace_append hprefix tailTrace_246627
  have hstable : (prefixWord ++ tailWord_246627).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246627).length < 2 ^ (prefixWord ++ tailWord_246627).sum := by decide
  have hdescent : baseEnd_246627 < baseStart_246627 := by decide
  rcases family_descends (prefixWord ++ tailWord_246627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246641 : List Nat := [1, 2, 2, 2, 1, 4, 1, 1, 6]
def baseStart_246641 : Nat := 118140960795 + 246641 * 2 ^ 59
def prefixEnd_246641 : Nat := 4983230072969 + 3 ^ 40 * 246641 * 2
def baseEnd_246641 : Nat := 112573672982821999691755

theorem tailTrace_246641 : CollatzResearch.WordTrace tailWord_246641 prefixEnd_246641 112573672982821999691755 := by
  unfold tailWord_246641
  simp only [CollatzResearch.WordTrace]
  refine ⟨8995736299469254774331777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5997157532979503182887851 8995736299469254774331777)
  ·
    refine ⟨6746802224601941080748833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8995736299469254774331777 6746802224601941080748833)
    ·
      refine ⟨5060101668451455810561625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6746802224601941080748833 5060101668451455810561625)
      ·
        refine ⟨3795076251338591857921219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5060101668451455810561625 3795076251338591857921219)
        ·
          refine ⟨5692614377007887786881829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3795076251338591857921219 5692614377007887786881829)
          ·
            refine ⟨1067365195688978960040343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5692614377007887786881829 1067365195688978960040343)
            ·
              refine ⟨1601047793533468440060515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1067365195688978960040343 1601047793533468440060515)
              ·
                refine ⟨2401571690300202660090773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1601047793533468440060515 2401571690300202660090773)
                ·
                  refine ⟨112573672982821999691755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2401571690300202660090773 112573672982821999691755)
                  ·
                    rfl

theorem cell20_246641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 6].length) (baseStart_246641 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_246641 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_246641 prefixEnd_246641 := by exact prefixLift 246641
  have htrace : WordTrace (prefixWord ++ tailWord_246641) baseStart_246641 baseEnd_246641 := by
    simpa [prefixWord, tailWord_246641, baseEnd_246641] using wordTrace_append hprefix tailTrace_246641
  have hstable : (prefixWord ++ tailWord_246641).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246641).length < 2 ^ (prefixWord ++ tailWord_246641).sum := by decide
  have hdescent : baseEnd_246641 < baseStart_246641 := by decide
  rcases family_descends (prefixWord ++ tailWord_246641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246713 : List Nat := [1, 2, 1, 4, 2, 2, 3, 3, 2]
def baseStart_246713 : Nat := 118140960795 + 246713 * 2 ^ 59
def prefixEnd_246713 : Nat := 4983230072969 + 3 ^ 40 * 246713 * 2
def baseEnd_246713 : Nat := 112606535744709749291461

theorem tailTrace_246713 : CollatzResearch.WordTrace tailWord_246713 prefixEnd_246713 112606535744709749291461 := by
  unfold tailWord_246713
  simp only [CollatzResearch.WordTrace]
  refine ⟨8998362355208411070952793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5998908236805607380635195 8998362355208411070952793)
  ·
    refine ⟨6748771766406308303214595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8998362355208411070952793 6748771766406308303214595)
    ·
      refine ⟨10123157649609462454821893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6748771766406308303214595 10123157649609462454821893)
      ·
        refine ⟨1898092059301774210279105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10123157649609462454821893 1898092059301774210279105)
        ·
          refine ⟨1423569044476330657709329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1898092059301774210279105 1423569044476330657709329)
          ·
            refine ⟨1067676783357247993281997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1423569044476330657709329 1067676783357247993281997)
            ·
              refine ⟨400378793758967997480749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1067676783357247993281997 400378793758967997480749)
              ·
                refine ⟨150142047659612999055281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 400378793758967997480749 150142047659612999055281)
                ·
                  refine ⟨112606535744709749291461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150142047659612999055281 112606535744709749291461)
                  ·
                    rfl

theorem cell20_246713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 3, 2].length) (baseStart_246713 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_246713 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_246713 prefixEnd_246713 := by exact prefixLift 246713
  have htrace : WordTrace (prefixWord ++ tailWord_246713) baseStart_246713 baseEnd_246713 := by
    simpa [prefixWord, tailWord_246713, baseEnd_246713] using wordTrace_append hprefix tailTrace_246713
  have hstable : (prefixWord ++ tailWord_246713).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246713).length < 2 ^ (prefixWord ++ tailWord_246713).sum := by decide
  have hdescent : baseEnd_246713 < baseStart_246713 := by decide
  rcases family_descends (prefixWord ++ tailWord_246713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246734 : List Nat := [4, 1, 1, 1, 2, 3, 3, 1, 4]
def baseStart_246734 : Nat := 118140960795 + 246734 * 2 ^ 59
def prefixEnd_246734 : Nat := 4983230072969 + 3 ^ 40 * 246734 * 2
def baseEnd_246734 : Nat := 112616120716927009591375

theorem tailTrace_246734 : CollatzResearch.WordTrace tailWord_246734 prefixEnd_246734 112616120716927009591375 := by
  unfold tailWord_246734
  simp only [CollatzResearch.WordTrace]
  refine ⟨1124891036016541457183407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5999418858754887771644837 1124891036016541457183407)
  ·
    refine ⟨1687336554024812185775111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1124891036016541457183407 1687336554024812185775111)
    ·
      refine ⟨2531004831037218278662667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1687336554024812185775111 2531004831037218278662667)
      ·
        refine ⟨3796507246555827417994001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2531004831037218278662667 3796507246555827417994001)
        ·
          refine ⟨2847380434916870563495501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3796507246555827417994001 2847380434916870563495501)
          ·
            refine ⟨1067767663093826461310813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2847380434916870563495501 1067767663093826461310813)
            ·
              refine ⟨400412873660184922991555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1067767663093826461310813 400412873660184922991555)
              ·
                refine ⟨600619310490277384487333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 400412873660184922991555 600619310490277384487333)
                ·
                  refine ⟨112616120716927009591375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 600619310490277384487333 112616120716927009591375)
                  ·
                    rfl

theorem cell20_246734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_246734 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_246734 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_246734 prefixEnd_246734 := by exact prefixLift 246734
  have htrace : WordTrace (prefixWord ++ tailWord_246734) baseStart_246734 baseEnd_246734 := by
    simpa [prefixWord, tailWord_246734, baseEnd_246734] using wordTrace_append hprefix tailTrace_246734
  have hstable : (prefixWord ++ tailWord_246734).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246734).length < 2 ^ (prefixWord ++ tailWord_246734).sum := by decide
  have hdescent : baseEnd_246734 < baseStart_246734 := by decide
  rcases family_descends (prefixWord ++ tailWord_246734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246744 : List Nat := [2, 1, 2, 2, 2, 5, 2, 1, 3]
def baseStart_246744 : Nat := 118140960795 + 246744 * 2 ^ 59
def prefixEnd_246744 : Nat := 4983230072969 + 3 ^ 40 * 246744 * 2
def baseEnd_246744 : Nat := 112620684989411419258001

theorem tailTrace_246744 : CollatzResearch.WordTrace tailWord_246744 prefixEnd_246744 112620684989411419258001 := by
  unfold tailWord_246744
  simp only [CollatzResearch.WordTrace]
  refine ⟨4499746509048051682665643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5999662012064068910220857 4499746509048051682665643)
  ·
    refine ⟨6749619763572077523998465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4499746509048051682665643 6749619763572077523998465)
    ·
      refine ⟨5062214822679058142998849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6749619763572077523998465 5062214822679058142998849)
      ·
        refine ⟨3796661117009293607249137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5062214822679058142998849 3796661117009293607249137)
        ·
          refine ⟨2847495837756970205436853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3796661117009293607249137 2847495837756970205436853)
          ·
            refine ⟨266952734789715956759705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2847495837756970205436853 266952734789715956759705)
            ·
              refine ⟨200214551092286967569779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 266952734789715956759705 200214551092286967569779)
              ·
                refine ⟨300321826638430451354669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200214551092286967569779 300321826638430451354669)
                ·
                  refine ⟨112620684989411419258001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 300321826638430451354669 112620684989411419258001)
                  ·
                    rfl

theorem cell20_246744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 2, 1, 3].length) (baseStart_246744 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_246744 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_246744 prefixEnd_246744 := by exact prefixLift 246744
  have htrace : WordTrace (prefixWord ++ tailWord_246744) baseStart_246744 baseEnd_246744 := by
    simpa [prefixWord, tailWord_246744, baseEnd_246744] using wordTrace_append hprefix tailTrace_246744
  have hstable : (prefixWord ++ tailWord_246744).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246744).length < 2 ^ (prefixWord ++ tailWord_246744).sum := by decide
  have hdescent : baseEnd_246744 < baseStart_246744 := by decide
  rcases family_descends (prefixWord ++ tailWord_246744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246755 : List Nat := [1, 1, 1, 6, 1, 1, 2, 1, 6]
def baseStart_246755 : Nat := 118140960795 + 246755 * 2 ^ 59
def prefixEnd_246755 : Nat := 4983230072969 + 3 ^ 40 * 246755 * 2
def baseEnd_246755 : Nat := 112625705689144269891289

theorem tailTrace_246755 : CollatzResearch.WordTrace tailWord_246755 prefixEnd_246755 112625705689144269891289 := by
  unfold tailWord_246755
  simp only [CollatzResearch.WordTrace]
  refine ⟨8999894221056252243981719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5999929480704168162654479 8999894221056252243981719)
  ·
    refine ⟨13499841331584378365972579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8999894221056252243981719 13499841331584378365972579)
    ·
      refine ⟨20249761997376567548958869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13499841331584378365972579 20249761997376567548958869)
      ·
        refine ⟨949207593627026603857447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 20249761997376567548958869 949207593627026603857447)
        ·
          refine ⟨1423811390440539905786171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 949207593627026603857447 1423811390440539905786171)
          ·
            refine ⟨2135717085660809858679257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1423811390440539905786171 2135717085660809858679257)
            ·
              refine ⟨1601787814245607394009443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2135717085660809858679257 1601787814245607394009443)
              ·
                refine ⟨2402681721368411091014165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1601787814245607394009443 2402681721368411091014165)
                ·
                  refine ⟨112625705689144269891289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2402681721368411091014165 112625705689144269891289)
                  ·
                    rfl

theorem cell20_246755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 6].length) (baseStart_246755 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_246755 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_246755 prefixEnd_246755 := by exact prefixLift 246755
  have htrace : WordTrace (prefixWord ++ tailWord_246755) baseStart_246755 baseEnd_246755 := by
    simpa [prefixWord, tailWord_246755, baseEnd_246755] using wordTrace_append hprefix tailTrace_246755
  have hstable : (prefixWord ++ tailWord_246755).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246755).length < 2 ^ (prefixWord ++ tailWord_246755).sum := by decide
  have hdescent : baseEnd_246755 < baseStart_246755 := by decide
  rcases family_descends (prefixWord ++ tailWord_246755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246841 : List Nat := [1, 2, 1, 5, 2, 1, 3, 2, 3]
def baseStart_246841 : Nat := 118140960795 + 246841 * 2 ^ 59
def prefixEnd_246841 : Nat := 4983230072969 + 3 ^ 40 * 246841 * 2
def baseEnd_246841 : Nat := 112664958432510193024271

theorem tailTrace_246841 : CollatzResearch.WordTrace tailWord_246841 prefixEnd_246841 112664958432510193024271 := by
  unfold tailWord_246841
  simp only [CollatzResearch.WordTrace]
  refine ⟨9003030898744688931612377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6002020599163125954408251 9003030898744688931612377)
  ·
    refine ⟨6752273174058516698709283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9003030898744688931612377 6752273174058516698709283)
    ·
      refine ⟨10128409761087775048063925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6752273174058516698709283 10128409761087775048063925)
      ·
        refine ⟨949538415101978910755993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10128409761087775048063925 949538415101978910755993)
        ·
          refine ⟨712153811326484183066995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 949538415101978910755993 712153811326484183066995)
          ·
            refine ⟨1068230716989726274600493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 712153811326484183066995 1068230716989726274600493)
            ·
              refine ⟨400586518871147352975185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1068230716989726274600493 400586518871147352975185)
              ·
                refine ⟨300439889153360514731389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 400586518871147352975185 300439889153360514731389)
                ·
                  refine ⟨112664958432510193024271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 300439889153360514731389 112664958432510193024271)
                  ·
                    rfl

theorem cell20_246841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 2, 3].length) (baseStart_246841 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_246841 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_246841 prefixEnd_246841 := by exact prefixLift 246841
  have htrace : WordTrace (prefixWord ++ tailWord_246841) baseStart_246841 baseEnd_246841 := by
    simpa [prefixWord, tailWord_246841, baseEnd_246841] using wordTrace_append hprefix tailTrace_246841
  have hstable : (prefixWord ++ tailWord_246841).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246841).length < 2 ^ (prefixWord ++ tailWord_246841).sum := by decide
  have hdescent : baseEnd_246841 < baseStart_246841 := by decide
  rcases family_descends (prefixWord ++ tailWord_246841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246848 : List Nat := [2, 1, 1, 2, 2, 3, 1, 6, 2]
def baseStart_246848 : Nat := 118140960795 + 246848 * 2 ^ 59
def prefixEnd_246848 : Nat := 4983230072969 + 3 ^ 40 * 246848 * 2
def baseEnd_246848 : Nat := 112668153423249279790909

theorem tailTrace_246848 : CollatzResearch.WordTrace tailWord_246848 prefixEnd_246848 112668153423249279790909 := by
  unfold tailWord_246848
  simp only [CollatzResearch.WordTrace]
  refine ⟨4501643104859664563558599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6002190806479552751411465 4501643104859664563558599)
  ·
    refine ⟨6752464657289496845337899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4501643104859664563558599 6752464657289496845337899)
    ·
      refine ⟨10128696985934245268006849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6752464657289496845337899 10128696985934245268006849)
      ·
        refine ⟨7596522739450683951005137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10128696985934245268006849 7596522739450683951005137)
        ·
          refine ⟨5697392054588012963253853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7596522739450683951005137 5697392054588012963253853)
          ·
            refine ⟨2136522020470504861220195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5697392054588012963253853 2136522020470504861220195)
            ·
              refine ⟨3204783030705757291830293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2136522020470504861220195 3204783030705757291830293)
              ·
                refine ⟨150224204564332373054545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3204783030705757291830293 150224204564332373054545)
                ·
                  refine ⟨112668153423249279790909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150224204564332373054545 112668153423249279790909)
                  ·
                    rfl

theorem cell20_246848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 6, 2].length) (baseStart_246848 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_246848 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_246848 prefixEnd_246848 := by exact prefixLift 246848
  have htrace : WordTrace (prefixWord ++ tailWord_246848) baseStart_246848 baseEnd_246848 := by
    simpa [prefixWord, tailWord_246848, baseEnd_246848] using wordTrace_append hprefix tailTrace_246848
  have hstable : (prefixWord ++ tailWord_246848).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246848).length < 2 ^ (prefixWord ++ tailWord_246848).sum := by decide
  have hdescent : baseEnd_246848 < baseStart_246848 := by decide
  rcases family_descends (prefixWord ++ tailWord_246848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246869 : List Nat := [1, 3, 2, 2, 1, 2, 1, 4, 4]
def baseStart_246869 : Nat := 118140960795 + 246869 * 2 ^ 59
def prefixEnd_246869 : Nat := 4983230072969 + 3 ^ 40 * 246869 * 2
def baseEnd_246869 : Nat := 112677738395466540090823

theorem tailTrace_246869 : CollatzResearch.WordTrace tailWord_246869 prefixEnd_246869 112677738395466540090823 := by
  unfold tailWord_246869
  simp only [CollatzResearch.WordTrace]
  refine ⟨9004052142643249713631661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6002701428428833142421107 9004052142643249713631661)
  ·
    refine ⟨3376519553491218642611873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9004052142643249713631661 3376519553491218642611873)
    ·
      refine ⟨2532389665118413981958905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3376519553491218642611873 2532389665118413981958905)
      ·
        refine ⟨1899292248838810486469179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2532389665118413981958905 1899292248838810486469179)
        ·
          refine ⟨2848938373258215729703769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1899292248838810486469179 2848938373258215729703769)
          ·
            refine ⟨2136703779943661797277827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2848938373258215729703769 2136703779943661797277827)
            ·
              refine ⟨3205055669915492695916741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2136703779943661797277827 3205055669915492695916741)
              ·
                refine ⟨600947938109154880484389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3205055669915492695916741 600947938109154880484389)
                ·
                  refine ⟨112677738395466540090823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 600947938109154880484389 112677738395466540090823)
                  ·
                    rfl

theorem cell20_246869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 4, 4].length) (baseStart_246869 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_246869 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_246869 prefixEnd_246869 := by exact prefixLift 246869
  have htrace : WordTrace (prefixWord ++ tailWord_246869) baseStart_246869 baseEnd_246869 := by
    simpa [prefixWord, tailWord_246869, baseEnd_246869] using wordTrace_append hprefix tailTrace_246869
  have hstable : (prefixWord ++ tailWord_246869).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246869).length < 2 ^ (prefixWord ++ tailWord_246869).sum := by decide
  have hdescent : baseEnd_246869 < baseStart_246869 := by decide
  rcases family_descends (prefixWord ++ tailWord_246869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246878 : List Nat := [4, 4, 1, 1, 1, 3, 1, 3, 2]
def baseStart_246878 : Nat := 118140960795 + 246878 * 2 ^ 59
def prefixEnd_246878 : Nat := 4983230072969 + 3 ^ 40 * 246878 * 2
def baseEnd_246878 : Nat := 112681846240702508790787

theorem tailTrace_246878 : CollatzResearch.WordTrace tailWord_246878 prefixEnd_246878 112681846240702508790787 := by
  unfold tailWord_246878
  simp only [CollatzResearch.WordTrace]
  refine ⟨1125547549951330531338661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6002920266407096167139525 1125547549951330531338661)
  ·
    refine ⟨211040165615874474625999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1125547549951330531338661 211040165615874474625999)
    ·
      refine ⟨316560248423811711938999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211040165615874474625999 316560248423811711938999)
      ·
        refine ⟨474840372635717567908499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316560248423811711938999 474840372635717567908499)
        ·
          refine ⟨712260558953576351862749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 474840372635717567908499 712260558953576351862749)
          ·
            refine ⟨267097709607591131948531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 712260558953576351862749 267097709607591131948531)
            ·
              refine ⟨400646564411386697922797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267097709607591131948531 400646564411386697922797)
              ·
                refine ⟨150242461654270011721049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 400646564411386697922797 150242461654270011721049)
                ·
                  refine ⟨112681846240702508790787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150242461654270011721049 112681846240702508790787)
                  ·
                    rfl

theorem cell20_246878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_246878 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_246878 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_246878 prefixEnd_246878 := by exact prefixLift 246878
  have htrace : WordTrace (prefixWord ++ tailWord_246878) baseStart_246878 baseEnd_246878 := by
    simpa [prefixWord, tailWord_246878, baseEnd_246878] using wordTrace_append hprefix tailTrace_246878
  have hstable : (prefixWord ++ tailWord_246878).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246878).length < 2 ^ (prefixWord ++ tailWord_246878).sum := by decide
  have hdescent : baseEnd_246878 < baseStart_246878 := by decide
  rcases family_descends (prefixWord ++ tailWord_246878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246882 : List Nat := [3, 3, 2, 2, 1, 1, 3, 3, 2]
def baseStart_246882 : Nat := 118140960795 + 246882 * 2 ^ 59
def prefixEnd_246882 : Nat := 4983230072969 + 3 ^ 40 * 246882 * 2
def baseEnd_246882 : Nat := 112683671949696272657437

theorem tailTrace_246882 : CollatzResearch.WordTrace tailWord_246882 prefixEnd_246882 112683671949696272657437 := by
  unfold tailWord_246882
  simp only [CollatzResearch.WordTrace]
  refine ⟨2251131572899038233463725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6003017527730768622569933 2251131572899038233463725)
  ·
    refine ⟨844174339837139337548897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2251131572899038233463725 844174339837139337548897)
    ·
      refine ⟨633130754877854503161673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 844174339837139337548897 633130754877854503161673)
      ·
        refine ⟨474848066158390877371255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 633130754877854503161673 474848066158390877371255)
        ·
          refine ⟨712272099237586316056883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 474848066158390877371255 712272099237586316056883)
          ·
            refine ⟨1068408148856379474085325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 712272099237586316056883 1068408148856379474085325)
            ·
              refine ⟨400653055821142302781997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1068408148856379474085325 400653055821142302781997)
              ·
                refine ⟨150244895932928363543249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 400653055821142302781997 150244895932928363543249)
                ·
                  refine ⟨112683671949696272657437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150244895932928363543249 112683671949696272657437)
                  ·
                    rfl

theorem cell20_246882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 3, 2].length) (baseStart_246882 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_246882 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_246882 prefixEnd_246882 := by exact prefixLift 246882
  have htrace : WordTrace (prefixWord ++ tailWord_246882) baseStart_246882 baseEnd_246882 := by
    simpa [prefixWord, tailWord_246882, baseEnd_246882] using wordTrace_append hprefix tailTrace_246882
  have hstable : (prefixWord ++ tailWord_246882).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246882).length < 2 ^ (prefixWord ++ tailWord_246882).sum := by decide
  have hdescent : baseEnd_246882 < baseStart_246882 := by decide
  rcases family_descends (prefixWord ++ tailWord_246882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246893 : List Nat := [1, 5, 1, 1, 2, 4, 6]
def baseStart_246893 : Nat := 118140960795 + 246893 * 2 ^ 59
def prefixEnd_246893 : Nat := 4983230072969 + 3 ^ 40 * 246893 * 2
def baseEnd_246893 : Nat := 12520965849936569254525

theorem tailTrace_246893 : CollatzResearch.WordTrace tailWord_246893 prefixEnd_246893 12520965849936569254525 := by
  unfold tailWord_246893
  simp only [CollatzResearch.WordTrace]
  refine ⟨9004927494556301812505333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6003284996370867875003555 9004927494556301812505333)
  ·
    refine ⟨844211952614653294922375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9004927494556301812505333 844211952614653294922375)
    ·
      refine ⟨1266317928921979942383563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 844211952614653294922375 1266317928921979942383563)
      ·
        refine ⟨1899476893382969913575345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1266317928921979942383563 1899476893382969913575345)
        ·
          refine ⟨1424607670037227435181509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1899476893382969913575345 1424607670037227435181509)
          ·
            refine ⟨267113938131980144096533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1424607670037227435181509 267113938131980144096533)
            ·
              refine ⟨12520965849936569254525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 267113938131980144096533 12520965849936569254525)
              ·
                rfl

theorem cell20_246893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 6].length) (baseStart_246893 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_246893 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_246893 prefixEnd_246893 := by exact prefixLift 246893
  have htrace : WordTrace (prefixWord ++ tailWord_246893) baseStart_246893 baseEnd_246893 := by
    simpa [prefixWord, tailWord_246893, baseEnd_246893] using wordTrace_append hprefix tailTrace_246893
  have hstable : (prefixWord ++ tailWord_246893).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246893).length < 2 ^ (prefixWord ++ tailWord_246893).sum := by decide
  have hdescent : baseEnd_246893 < baseStart_246893 := by decide
  rcases family_descends (prefixWord ++ tailWord_246893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246903 : List Nat := [1, 1, 3, 1, 1, 4, 5, 2, 2]
def baseStart_246903 : Nat := 118140960795 + 246903 * 2 ^ 59
def prefixEnd_246903 : Nat := 4983230072969 + 3 ^ 40 * 246903 * 2
def baseEnd_246903 : Nat := 112693256921913532957351

theorem tailTrace_246903 : CollatzResearch.WordTrace tailWord_246903 prefixEnd_246903 112693256921913532957351 := by
  unfold tailWord_246903
  simp only [CollatzResearch.WordTrace]
  refine ⟨9005292224520073520369363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6003528149680049013579575 9005292224520073520369363)
  ·
    refine ⟨13507938336780110280554045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9005292224520073520369363 13507938336780110280554045)
    ·
      refine ⟨5065476876292541355207767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13507938336780110280554045 5065476876292541355207767)
      ·
        refine ⟨7598215314438812032811651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5065476876292541355207767 7598215314438812032811651)
        ·
          refine ⟨11397322971658218049217477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7598215314438812032811651 11397322971658218049217477)
          ·
            refine ⟨2136998057185915884228277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11397322971658218049217477 2136998057185915884228277)
            ·
              refine ⟨200343567861179614146401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2136998057185915884228277 200343567861179614146401)
              ·
                refine ⟨150257675895884710609801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 200343567861179614146401 150257675895884710609801)
                ·
                  refine ⟨112693256921913532957351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150257675895884710609801 112693256921913532957351)
                  ·
                    rfl

theorem cell20_246903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 5, 2, 2].length) (baseStart_246903 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_246903 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_246903 prefixEnd_246903 := by exact prefixLift 246903
  have htrace : WordTrace (prefixWord ++ tailWord_246903) baseStart_246903 baseEnd_246903 := by
    simpa [prefixWord, tailWord_246903, baseEnd_246903] using wordTrace_append hprefix tailTrace_246903
  have hstable : (prefixWord ++ tailWord_246903).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246903).length < 2 ^ (prefixWord ++ tailWord_246903).sum := by decide
  have hdescent : baseEnd_246903 < baseStart_246903 := by decide
  rcases family_descends (prefixWord ++ tailWord_246903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246917 : List Nat := [1, 3, 1, 1, 6, 1, 1, 3, 3]
def baseStart_246917 : Nat := 118140960795 + 246917 * 2 ^ 59
def prefixEnd_246917 : Nat := 4983230072969 + 3 ^ 40 * 246917 * 2
def baseEnd_246917 : Nat := 112699646903391706490627

theorem tailTrace_246917 : CollatzResearch.WordTrace tailWord_246917 prefixEnd_246917 112699646903391706490627 := by
  unfold tailWord_246917
  simp only [CollatzResearch.WordTrace]
  refine ⟨9005802846469353911379005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6003868564312902607586003 9005802846469353911379005)
  ·
    refine ⟨3377176067426007716767127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9005802846469353911379005 3377176067426007716767127)
    ·
      refine ⟨5065764101139011575150691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3377176067426007716767127 5065764101139011575150691)
      ·
        refine ⟨7598646151708517362726037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5065764101139011575150691 7598646151708517362726037)
        ·
          refine ⟨356186538361336751377783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7598646151708517362726037 356186538361336751377783)
          ·
            refine ⟨534279807542005127066675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356186538361336751377783 534279807542005127066675)
            ·
              refine ⟨801419711313007690600013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 534279807542005127066675 801419711313007690600013)
              ·
                refine ⟨300532391742377883975005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 801419711313007690600013 300532391742377883975005)
                ·
                  refine ⟨112699646903391706490627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 300532391742377883975005 112699646903391706490627)
                  ·
                    rfl

theorem cell20_246917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 3, 3].length) (baseStart_246917 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_246917 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_246917 prefixEnd_246917 := by exact prefixLift 246917
  have htrace : WordTrace (prefixWord ++ tailWord_246917) baseStart_246917 baseEnd_246917 := by
    simpa [prefixWord, tailWord_246917, baseEnd_246917] using wordTrace_append hprefix tailTrace_246917
  have hstable : (prefixWord ++ tailWord_246917).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246917).length < 2 ^ (prefixWord ++ tailWord_246917).sum := by decide
  have hdescent : baseEnd_246917 < baseStart_246917 := by decide
  rcases family_descends (prefixWord ++ tailWord_246917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246959 : List Nat := [1, 1, 2, 1, 2, 3, 2, 3, 5]
def baseStart_246959 : Nat := 118140960795 + 246959 * 2 ^ 59
def prefixEnd_246959 : Nat := 4983230072969 + 3 ^ 40 * 246959 * 2
def baseEnd_246959 : Nat := 112718816847826227090455

theorem tailTrace_246959 : CollatzResearch.WordTrace tailWord_246959 prefixEnd_246959 112718816847826227090455 := by
  unfold tailWord_246959
  simp only [CollatzResearch.WordTrace]
  refine ⟨9007334712317195084407931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6004889808211463389605287 9007334712317195084407931)
  ·
    refine ⟨13511002068475792626611897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9007334712317195084407931 13511002068475792626611897)
    ·
      refine ⟨10133251551356844469958923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13511002068475792626611897 10133251551356844469958923)
      ·
        refine ⟨15199877327035266704938385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10133251551356844469958923 15199877327035266704938385)
        ·
          refine ⟨11399907995276450028703789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15199877327035266704938385 11399907995276450028703789)
          ·
            refine ⟨4274965498228668760763921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11399907995276450028703789 4274965498228668760763921)
            ·
              refine ⟨3206224123671501570572941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4274965498228668760763921 3206224123671501570572941)
              ·
                refine ⟨1202334046376813088964853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3206224123671501570572941 1202334046376813088964853)
                ·
                  refine ⟨112718816847826227090455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1202334046376813088964853 112718816847826227090455)
                  ·
                    rfl

theorem cell20_246959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3, 5].length) (baseStart_246959 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_246959 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_246959 prefixEnd_246959 := by exact prefixLift 246959
  have htrace : WordTrace (prefixWord ++ tailWord_246959) baseStart_246959 baseEnd_246959 := by
    simpa [prefixWord, tailWord_246959, baseEnd_246959] using wordTrace_append hprefix tailTrace_246959
  have hstable : (prefixWord ++ tailWord_246959).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246959).length < 2 ^ (prefixWord ++ tailWord_246959).sum := by decide
  have hdescent : baseEnd_246959 < baseStart_246959 := by decide
  rcases family_descends (prefixWord ++ tailWord_246959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_246969 : List Nat := [1, 2, 1, 4, 1, 5, 1, 5]
def baseStart_246969 : Nat := 118140960795 + 246969 * 2 ^ 59
def prefixEnd_246969 : Nat := 4983230072969 + 3 ^ 40 * 246969 * 2
def baseEnd_246969 : Nat := 37574460373436878919027

theorem tailTrace_246969 : CollatzResearch.WordTrace tailWord_246969 prefixEnd_246969 37574460373436878919027 := by
  unfold tailWord_246969
  simp only [CollatzResearch.WordTrace]
  refine ⟨9007699442280966792271961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6005132961520644528181307 9007699442280966792271961)
  ·
    refine ⟨6755774581710725094203971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9007699442280966792271961 6755774581710725094203971)
    ·
      refine ⟨10133661872566087641305957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6755774581710725094203971 10133661872566087641305957)
      ·
        refine ⟨1900061601106141432744867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10133661872566087641305957 1900061601106141432744867)
        ·
          refine ⟨2850092401659212149117301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1900061601106141432744867 2850092401659212149117301)
          ·
            refine ⟨267196162655551138979747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2850092401659212149117301 267196162655551138979747)
            ·
              refine ⟨400794243983326708469621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267196162655551138979747 400794243983326708469621)
              ·
                refine ⟨37574460373436878919027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 400794243983326708469621 37574460373436878919027)
                ·
                  rfl

theorem cell20_246969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 5].length) (baseStart_246969 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_246969 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_246969 prefixEnd_246969 := by exact prefixLift 246969
  have htrace : WordTrace (prefixWord ++ tailWord_246969) baseStart_246969 baseEnd_246969 := by
    simpa [prefixWord, tailWord_246969, baseEnd_246969] using wordTrace_append hprefix tailTrace_246969
  have hstable : (prefixWord ++ tailWord_246969).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_246969).length < 2 ^ (prefixWord ++ tailWord_246969).sum := by decide
  have hdescent : baseEnd_246969 < baseStart_246969 := by decide
  rcases family_descends (prefixWord ++ tailWord_246969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247038 : List Nat := [4, 2, 2, 1, 1, 2, 2, 2, 4]
def baseStart_247038 : Nat := 118140960795 + 247038 * 2 ^ 59
def prefixEnd_247038 : Nat := 4983230072969 + 3 ^ 40 * 247038 * 2
def baseEnd_247038 : Nat := 112754874600453063456799

theorem tailTrace_247038 : CollatzResearch.WordTrace tailWord_247038 prefixEnd_247038 112754874600453063456799 := by
  unfold tailWord_247038
  simp only [CollatzResearch.WordTrace]
  refine ⟨1126277009878873947066721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6006810719353994384355845 1126277009878873947066721)
  ·
    refine ⟨844707757409155460300041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1126277009878873947066721 844707757409155460300041)
    ·
      refine ⟨633530818056866595225031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 844707757409155460300041 633530818056866595225031)
      ·
        refine ⟨950296227085299892837547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 633530818056866595225031 950296227085299892837547)
        ·
          refine ⟨1425444340627949839256321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 950296227085299892837547 1425444340627949839256321)
          ·
            refine ⟨1069083255470962379442241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1425444340627949839256321 1069083255470962379442241)
            ·
              refine ⟨801812441603221784581681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1069083255470962379442241 801812441603221784581681)
              ·
                refine ⟨601359331202416338436261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 801812441603221784581681 601359331202416338436261)
                ·
                  refine ⟨112754874600453063456799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 601359331202416338436261 112754874600453063456799)
                  ·
                    rfl

theorem cell20_247038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_247038 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_247038 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_247038 prefixEnd_247038 := by exact prefixLift 247038
  have htrace : WordTrace (prefixWord ++ tailWord_247038) baseStart_247038 baseEnd_247038 := by
    simpa [prefixWord, tailWord_247038, baseEnd_247038] using wordTrace_append hprefix tailTrace_247038
  have hstable : (prefixWord ++ tailWord_247038).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247038).length < 2 ^ (prefixWord ++ tailWord_247038).sum := by decide
  have hdescent : baseEnd_247038 < baseStart_247038 := by decide
  rcases family_descends (prefixWord ++ tailWord_247038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247066 : List Nat := [3, 1, 1, 3, 3, 1, 8]
def baseStart_247066 : Nat := 118140960795 + 247066 * 2 ^ 59
def prefixEnd_247066 : Nat := 4983230072969 + 3 ^ 40 * 247066 * 2
def baseEnd_247066 : Nat := 12529739395934378947039

theorem tailTrace_247066 : CollatzResearch.WordTrace tailWord_247066 prefixEnd_247066 12529739395934378947039 := by
  unfold tailWord_247066
  simp only [CollatzResearch.WordTrace]
  refine ⟨2252809330732388089638263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6007491548619701572368701 2252809330732388089638263)
  ·
    refine ⟨3379213996098582134457395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2252809330732388089638263 3379213996098582134457395)
    ·
      refine ⟨5068820994147873201686093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3379213996098582134457395 5068820994147873201686093)
      ·
        refine ⟨1900807872805452450632285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5068820994147873201686093 1900807872805452450632285)
        ·
          refine ⟨712802952302044668987107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1900807872805452450632285 712802952302044668987107)
          ·
            refine ⟨1069204428453067003480661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 712802952302044668987107 1069204428453067003480661)
            ·
              refine ⟨12529739395934378947039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1069204428453067003480661 12529739395934378947039)
              ·
                rfl

theorem cell20_247066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 8].length) (baseStart_247066 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_247066 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_247066 prefixEnd_247066 := by exact prefixLift 247066
  have htrace : WordTrace (prefixWord ++ tailWord_247066) baseStart_247066 baseEnd_247066 := by
    simpa [prefixWord, tailWord_247066, baseEnd_247066] using wordTrace_append hprefix tailTrace_247066
  have hstable : (prefixWord ++ tailWord_247066).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247066).length < 2 ^ (prefixWord ++ tailWord_247066).sum := by decide
  have hdescent : baseEnd_247066 < baseStart_247066 := by decide
  rcases family_descends (prefixWord ++ tailWord_247066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247072 : List Nat := [2, 1, 1, 5, 3, 1, 3, 2, 2]
def baseStart_247072 : Nat := 118140960795 + 247072 * 2 ^ 59
def prefixEnd_247072 : Nat := 4983230072969 + 3 ^ 40 * 247072 * 2
def baseEnd_247072 : Nat := 112770393126900056323327

theorem tailTrace_247072 : CollatzResearch.WordTrace tailWord_247072 prefixEnd_247072 112770393126900056323327 := by
  unfold tailWord_247072
  simp only [CollatzResearch.WordTrace]
  refine ⟨4505728080453907691635735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6007637440605210255514313 4505728080453907691635735)
  ·
    refine ⟨6758592120680861537453603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4505728080453907691635735 6758592120680861537453603)
    ·
      refine ⟨10137888181021292306180405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6758592120680861537453603 10137888181021292306180405)
      ·
        refine ⟨950427016970746153704413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10137888181021292306180405 950427016970746153704413)
        ·
          refine ⟨356410131364029807639155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 950427016970746153704413 356410131364029807639155)
          ·
            refine ⟨534615197046044711458733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356410131364029807639155 534615197046044711458733)
            ·
              refine ⟨200480698892266766797025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 534615197046044711458733 200480698892266766797025)
              ·
                refine ⟨150360524169200075097769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 200480698892266766797025 150360524169200075097769)
                ·
                  refine ⟨112770393126900056323327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150360524169200075097769 112770393126900056323327)
                  ·
                    rfl

theorem cell20_247072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 3, 2, 2].length) (baseStart_247072 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_247072 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_247072 prefixEnd_247072 := by exact prefixLift 247072
  have htrace : WordTrace (prefixWord ++ tailWord_247072) baseStart_247072 baseEnd_247072 := by
    simpa [prefixWord, tailWord_247072, baseEnd_247072] using wordTrace_append hprefix tailTrace_247072
  have hstable : (prefixWord ++ tailWord_247072).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247072).length < 2 ^ (prefixWord ++ tailWord_247072).sum := by decide
  have hdescent : baseEnd_247072 < baseStart_247072 := by decide
  rcases family_descends (prefixWord ++ tailWord_247072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247128 : List Nat := [2, 1, 2, 2, 1, 1, 6, 2, 3]
def baseStart_247128 : Nat := 118140960795 + 247128 * 2 ^ 59
def prefixEnd_247128 : Nat := 4983230072969 + 3 ^ 40 * 247128 * 2
def baseEnd_247128 : Nat := 112795953052812750456431

theorem tailTrace_247128 : CollatzResearch.WordTrace tailWord_247128 prefixEnd_247128 112795953052812750456431 := by
  unfold tailWord_247128
  simp only [CollatzResearch.WordTrace]
  refine ⟨4506749324352468473655019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6008999099136624631540025 4506749324352468473655019)
  ·
    refine ⟨6760123986528702710482529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4506749324352468473655019 6760123986528702710482529)
    ·
      refine ⟨5070092989896527032861897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6760123986528702710482529 5070092989896527032861897)
      ·
        refine ⟨3802569742422395274646423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5070092989896527032861897 3802569742422395274646423)
        ·
          refine ⟨5703854613633592911969635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3802569742422395274646423 5703854613633592911969635)
          ·
            refine ⟨8555781920450389367954453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5703854613633592911969635 8555781920450389367954453)
            ·
              refine ⟨401052277521112001622865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8555781920450389367954453 401052277521112001622865)
              ·
                refine ⟨300789208140834001217149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 401052277521112001622865 300789208140834001217149)
                ·
                  refine ⟨112795953052812750456431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 300789208140834001217149 112795953052812750456431)
                  ·
                    rfl

theorem cell20_247128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 2, 3].length) (baseStart_247128 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_247128 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_247128 prefixEnd_247128 := by exact prefixLift 247128
  have htrace : WordTrace (prefixWord ++ tailWord_247128) baseStart_247128 baseEnd_247128 := by
    simpa [prefixWord, tailWord_247128, baseEnd_247128] using wordTrace_append hprefix tailTrace_247128
  have hstable : (prefixWord ++ tailWord_247128).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247128).length < 2 ^ (prefixWord ++ tailWord_247128).sum := by decide
  have hdescent : baseEnd_247128 < baseStart_247128 := by decide
  rcases family_descends (prefixWord ++ tailWord_247128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247232 : List Nat := [2, 1, 1, 2, 3, 1, 2, 2, 6]
def baseStart_247232 : Nat := 118140960795 + 247232 * 2 ^ 59
def prefixEnd_247232 : Nat := 4983230072969 + 3 ^ 40 * 247232 * 2
def baseEnd_247232 : Nat := 112843421486650610989339

theorem tailTrace_247232 : CollatzResearch.WordTrace tailWord_247232 prefixEnd_247232 112843421486650610989339 := by
  unfold tailWord_247232
  simp only [CollatzResearch.WordTrace]
  refine ⟨4508645920164081354547975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6011527893552108472730633 4508645920164081354547975)
  ·
    refine ⟨6762968880246122031821963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4508645920164081354547975 6762968880246122031821963)
    ·
      refine ⟨10144453320369183047732945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6762968880246122031821963 10144453320369183047732945)
      ·
        refine ⟨7608339990276887285799709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10144453320369183047732945 7608339990276887285799709)
        ·
          refine ⟨2853127496353832732174891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7608339990276887285799709 2853127496353832732174891)
          ·
            refine ⟨4279691244530749098262337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2853127496353832732174891 4279691244530749098262337)
            ·
              refine ⟨3209768433398061823696753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4279691244530749098262337 3209768433398061823696753)
              ·
                refine ⟨2407326325048546367772565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3209768433398061823696753 2407326325048546367772565)
                ·
                  refine ⟨112843421486650610989339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2407326325048546367772565 112843421486650610989339)
                  ·
                    rfl

theorem cell20_247232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 6].length) (baseStart_247232 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_247232 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_247232 prefixEnd_247232 := by exact prefixLift 247232
  have htrace : WordTrace (prefixWord ++ tailWord_247232) baseStart_247232 baseEnd_247232 := by
    simpa [prefixWord, tailWord_247232, baseEnd_247232] using wordTrace_append hprefix tailTrace_247232
  have hstable : (prefixWord ++ tailWord_247232).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247232).length < 2 ^ (prefixWord ++ tailWord_247232).sum := by decide
  have hdescent : baseEnd_247232 < baseStart_247232 := by decide
  rcases family_descends (prefixWord ++ tailWord_247232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247297 : List Nat := [1, 2, 4, 1, 4, 1, 2, 2, 3]
def baseStart_247297 : Nat := 118140960795 + 247297 * 2 ^ 59
def prefixEnd_247297 : Nat := 4983230072969 + 3 ^ 40 * 247297 * 2
def baseEnd_247297 : Nat := 112873089257799273822407

theorem tailTrace_247297 : CollatzResearch.WordTrace tailWord_247297 prefixEnd_247297 112873089257799273822407 := by
  unfold tailWord_247297
  simp only [CollatzResearch.WordTrace]
  refine ⟨9019662585092678810212145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6013108390061785873474763 9019662585092678810212145)
  ·
    refine ⟨6764746938819509107659109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9019662585092678810212145 6764746938819509107659109)
    ·
      refine ⟨1268390051028657957686083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6764746938819509107659109 1268390051028657957686083)
      ·
        refine ⟨1902585076542986936529125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1268390051028657957686083 1902585076542986936529125)
        ·
          refine ⟨356734701851810050599211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1902585076542986936529125 356734701851810050599211)
          ·
            refine ⟨535102052777715075898817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356734701851810050599211 535102052777715075898817)
            ·
              refine ⟨401326539583286306924113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 535102052777715075898817 401326539583286306924113)
              ·
                refine ⟨300994904687464730193085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 401326539583286306924113 300994904687464730193085)
                ·
                  refine ⟨112873089257799273822407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 300994904687464730193085 112873089257799273822407)
                  ·
                    rfl

theorem cell20_247297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 2, 3].length) (baseStart_247297 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_247297 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_247297 prefixEnd_247297 := by exact prefixLift 247297
  have htrace : WordTrace (prefixWord ++ tailWord_247297) baseStart_247297 baseEnd_247297 := by
    simpa [prefixWord, tailWord_247297, baseEnd_247297] using wordTrace_append hprefix tailTrace_247297
  have hstable : (prefixWord ++ tailWord_247297).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247297).length < 2 ^ (prefixWord ++ tailWord_247297).sum := by decide
  have hdescent : baseEnd_247297 < baseStart_247297 := by decide
  rcases family_descends (prefixWord ++ tailWord_247297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247325 : List Nat := [1, 4, 2, 2, 1, 1, 3, 2, 4]
def baseStart_247325 : Nat := 118140960795 + 247325 * 2 ^ 59
def prefixEnd_247325 : Nat := 4983230072969 + 3 ^ 40 * 247325 * 2
def baseEnd_247325 : Nat := 112885869220755620888959

theorem tailTrace_247325 : CollatzResearch.WordTrace tailWord_247325 prefixEnd_247325 112885869220755620888959 := by
  unfold tailWord_247325
  simp only [CollatzResearch.WordTrace]
  refine ⟨9020683828991239592231429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6013789219327493061487619 9020683828991239592231429)
  ·
    refine ⟨1691378217935857423543393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9020683828991239592231429 1691378217935857423543393)
    ·
      refine ⟨1268533663451893067657545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1691378217935857423543393 1268533663451893067657545)
      ·
        refine ⟨951400247588919800743159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1268533663451893067657545 951400247588919800743159)
        ·
          refine ⟨1427100371383379701114739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 951400247588919800743159 1427100371383379701114739)
          ·
            refine ⟨2140650557075069551672109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1427100371383379701114739 2140650557075069551672109)
            ·
              refine ⟨802743958903151081877041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2140650557075069551672109 802743958903151081877041)
              ·
                refine ⟨602057969177363311407781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 802743958903151081877041 602057969177363311407781)
                ·
                  refine ⟨112885869220755620888959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 602057969177363311407781 112885869220755620888959)
                  ·
                    rfl

theorem cell20_247325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_247325 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_247325 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_247325 prefixEnd_247325 := by exact prefixLift 247325
  have htrace : WordTrace (prefixWord ++ tailWord_247325) baseStart_247325 baseEnd_247325 := by
    simpa [prefixWord, tailWord_247325, baseEnd_247325] using wordTrace_append hprefix tailTrace_247325
  have hstable : (prefixWord ++ tailWord_247325).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247325).length < 2 ^ (prefixWord ++ tailWord_247325).sum := by decide
  have hdescent : baseEnd_247325 < baseStart_247325 := by decide
  rcases family_descends (prefixWord ++ tailWord_247325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247346 : List Nat := [3, 2, 1, 1, 2, 1, 1, 1, 8]
def baseStart_247346 : Nat := 118140960795 + 247346 * 2 ^ 59
def prefixEnd_247346 : Nat := 4983230072969 + 3 ^ 40 * 247346 * 2
def baseEnd_247346 : Nat := 112895454192972881188873

theorem tailTrace_247346 : CollatzResearch.WordTrace tailWord_247346 prefixEnd_247346 112895454192972881188873 := by
  unfold tailWord_247346
  simp only [CollatzResearch.WordTrace]
  refine ⟨2255362440478790044686473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6014299841276773452497261 2255362440478790044686473)
  ·
    refine ⟨1691521830359092533514855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2255362440478790044686473 1691521830359092533514855)
    ·
      refine ⟨2537282745538638800272283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1691521830359092533514855 2537282745538638800272283)
      ·
        refine ⟨3805924118307958200408425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2537282745538638800272283 3805924118307958200408425)
        ·
          refine ⟨2854443088730968650306319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3805924118307958200408425 2854443088730968650306319)
          ·
            refine ⟨4281664633096452975459479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2854443088730968650306319 4281664633096452975459479)
            ·
              refine ⟨6422496949644679463189219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4281664633096452975459479 6422496949644679463189219)
              ·
                refine ⟨9633745424467019194783829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6422496949644679463189219 9633745424467019194783829)
                ·
                  refine ⟨112895454192972881188873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9633745424467019194783829 112895454192972881188873)
                  ·
                    rfl

theorem cell20_247346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_247346 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_247346 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_247346 prefixEnd_247346 := by exact prefixLift 247346
  have htrace : WordTrace (prefixWord ++ tailWord_247346) baseStart_247346 baseEnd_247346 := by
    simpa [prefixWord, tailWord_247346, baseEnd_247346] using wordTrace_append hprefix tailTrace_247346
  have hstable : (prefixWord ++ tailWord_247346).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247346).length < 2 ^ (prefixWord ++ tailWord_247346).sum := by decide
  have hdescent : baseEnd_247346 < baseStart_247346 := by decide
  rcases family_descends (prefixWord ++ tailWord_247346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247356 : List Nat := [2, 2, 2, 2, 4, 1, 1, 1, 5]
def baseStart_247356 : Nat := 118140960795 + 247356 * 2 ^ 59
def prefixEnd_247356 : Nat := 4983230072969 + 3 ^ 40 * 247356 * 2
def baseEnd_247356 : Nat := 112900018465457290855499

theorem tailTrace_247356 : CollatzResearch.WordTrace tailWord_247356 prefixEnd_247356 112900018465457290855499 := by
  unfold tailWord_247356
  simp only [CollatzResearch.WordTrace]
  refine ⟨4510907245939465943304961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6014542994585954591073281 4510907245939465943304961)
  ·
    refine ⟨3383180434454599457478721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4510907245939465943304961 3383180434454599457478721)
    ·
      refine ⟨2537385325840949593109041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3383180434454599457478721 2537385325840949593109041)
      ·
        refine ⟨1903038994380712194831781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2537385325840949593109041 1903038994380712194831781)
        ·
          refine ⟨356819811446383536530959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1903038994380712194831781 356819811446383536530959)
          ·
            refine ⟨535229717169575304796439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356819811446383536530959 535229717169575304796439)
            ·
              refine ⟨802844575754362957194659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 535229717169575304796439 802844575754362957194659)
              ·
                refine ⟨1204266863631544435791989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 802844575754362957194659 1204266863631544435791989)
                ·
                  refine ⟨112900018465457290855499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1204266863631544435791989 112900018465457290855499)
                  ·
                    rfl

theorem cell20_247356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 1, 5].length) (baseStart_247356 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_247356 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_247356 prefixEnd_247356 := by exact prefixLift 247356
  have htrace : WordTrace (prefixWord ++ tailWord_247356) baseStart_247356 baseEnd_247356 := by
    simpa [prefixWord, tailWord_247356, baseEnd_247356] using wordTrace_append hprefix tailTrace_247356
  have hstable : (prefixWord ++ tailWord_247356).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247356).length < 2 ^ (prefixWord ++ tailWord_247356).sum := by decide
  have hdescent : baseEnd_247356 < baseStart_247356 := by decide
  rcases family_descends (prefixWord ++ tailWord_247356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247397 : List Nat := [1, 3, 1, 3, 3, 3, 1, 3, 2]
def baseStart_247397 : Nat := 118140960795 + 247397 * 2 ^ 59
def prefixEnd_247397 : Nat := 4983230072969 + 3 ^ 40 * 247397 * 2
def baseEnd_247397 : Nat := 112918731982643370488665

theorem tailTrace_247397 : CollatzResearch.WordTrace tailWord_247397 prefixEnd_247397 112918731982643370488665 := by
  unfold tailWord_247397
  simp only [CollatzResearch.WordTrace]
  refine ⟨9023309884730395888852445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6015539923153597259234963 9023309884730395888852445)
  ·
    refine ⟨3383741206773898458319667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9023309884730395888852445 3383741206773898458319667)
    ·
      refine ⟨5075611810160847687479501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3383741206773898458319667 5075611810160847687479501)
      ·
        refine ⟨1903354428810317882804813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5075611810160847687479501 1903354428810317882804813)
        ·
          refine ⟨713757910803869206051805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1903354428810317882804813 713757910803869206051805)
          ·
            refine ⟨267659216551450952269427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 713757910803869206051805 267659216551450952269427)
            ·
              refine ⟨401488824827176428404141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267659216551450952269427 401488824827176428404141)
              ·
                refine ⟨150558309310191160651553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 401488824827176428404141 150558309310191160651553)
                ·
                  refine ⟨112918731982643370488665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150558309310191160651553 112918731982643370488665)
                  ·
                    rfl

theorem cell20_247397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 3, 2].length) (baseStart_247397 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_247397 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_247397 prefixEnd_247397 := by exact prefixLift 247397
  have htrace : WordTrace (prefixWord ++ tailWord_247397) baseStart_247397 baseEnd_247397 := by
    simpa [prefixWord, tailWord_247397, baseEnd_247397] using wordTrace_append hprefix tailTrace_247397
  have hstable : (prefixWord ++ tailWord_247397).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247397).length < 2 ^ (prefixWord ++ tailWord_247397).sum := by decide
  have hdescent : baseEnd_247397 < baseStart_247397 := by decide
  rcases family_descends (prefixWord ++ tailWord_247397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247408 : List Nat := [2, 1, 1, 1, 6, 3, 6]
def baseStart_247408 : Nat := 118140960795 + 247408 * 2 ^ 59
def prefixEnd_247408 : Nat := 4983230072969 + 3 ^ 40 * 247408 * 2
def baseEnd_247408 : Nat := 12547083631375135680217

theorem tailTrace_247408 : CollatzResearch.WordTrace tailWord_247408 prefixEnd_247408 12547083631375135680217 := by
  unfold tailWord_247408
  simp only [CollatzResearch.WordTrace]
  refine ⟨4511855543845272383751439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6015807391793696511668585 4511855543845272383751439)
  ·
    refine ⟨6767783315767908575627159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4511855543845272383751439 6767783315767908575627159)
    ·
      refine ⟨10151674973651862863440739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6767783315767908575627159 10151674973651862863440739)
      ·
        refine ⟨15227512460477794295161109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10151674973651862863440739 15227512460477794295161109)
        ·
          refine ⟨713789646584896607585677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15227512460477794295161109 713789646584896607585677)
          ·
            refine ⟨267671117469336227844629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 713789646584896607585677 267671117469336227844629)
            ·
              refine ⟨12547083631375135680217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 267671117469336227844629 12547083631375135680217)
              ·
                rfl

theorem cell20_247408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 6].length) (baseStart_247408 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_247408 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_247408 prefixEnd_247408 := by exact prefixLift 247408
  have htrace : WordTrace (prefixWord ++ tailWord_247408) baseStart_247408 baseEnd_247408 := by
    simpa [prefixWord, tailWord_247408, baseEnd_247408] using wordTrace_append hprefix tailTrace_247408
  have hstable : (prefixWord ++ tailWord_247408).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247408).length < 2 ^ (prefixWord ++ tailWord_247408).sum := by decide
  have hdescent : baseEnd_247408 < baseStart_247408 := by decide
  rcases family_descends (prefixWord ++ tailWord_247408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247414 : List Nat := [5, 1, 1, 2, 2, 2, 3, 2, 2]
def baseStart_247414 : Nat := 118140960795 + 247414 * 2 ^ 59
def prefixEnd_247414 : Nat := 4983230072969 + 3 ^ 40 * 247414 * 2
def baseEnd_247414 : Nat := 112926491245866866921929

theorem tailTrace_247414 : CollatzResearch.WordTrace tailWord_247414 prefixEnd_247414 112926491245866866921929 := by
  unfold tailWord_247414
  simp only [CollatzResearch.WordTrace]
  refine ⟨563995620354300487013831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6015953283779205194814197 563995620354300487013831)
  ·
    refine ⟨845993430531450730520747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 563995620354300487013831 845993430531450730520747)
    ·
      refine ⟨1268990145797176095781121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 845993430531450730520747 1268990145797176095781121)
      ·
        refine ⟨951742609347882071835841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1268990145797176095781121 951742609347882071835841)
        ·
          refine ⟨713806957010911553876881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 951742609347882071835841 713806957010911553876881)
          ·
            refine ⟨535355217758183665407661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 713806957010911553876881 535355217758183665407661)
            ·
              refine ⟨200758206659318874527873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 535355217758183665407661 200758206659318874527873)
              ·
                refine ⟨150568654994489155895905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 200758206659318874527873 150568654994489155895905)
                ·
                  refine ⟨112926491245866866921929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150568654994489155895905 112926491245866866921929)
                  ·
                    rfl

theorem cell20_247414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 3, 2, 2].length) (baseStart_247414 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_247414 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_247414 prefixEnd_247414 := by exact prefixLift 247414
  have htrace : WordTrace (prefixWord ++ tailWord_247414) baseStart_247414 baseEnd_247414 := by
    simpa [prefixWord, tailWord_247414, baseEnd_247414] using wordTrace_append hprefix tailTrace_247414
  have hstable : (prefixWord ++ tailWord_247414).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247414).length < 2 ^ (prefixWord ++ tailWord_247414).sum := by decide
  have hdescent : baseEnd_247414 < baseStart_247414 := by decide
  rcases family_descends (prefixWord ++ tailWord_247414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247415 : List Nat := [1, 1, 3, 1, 1, 3, 1, 6, 3]
def baseStart_247415 : Nat := 118140960795 + 247415 * 2 ^ 59
def prefixEnd_247415 : Nat := 4983230072969 + 3 ^ 40 * 247415 * 2
def baseEnd_247415 : Nat := 112926947673115307888591

theorem tailTrace_247415 : CollatzResearch.WordTrace tailWord_247415 prefixEnd_247415 112926947673115307888591 := by
  unfold tailWord_247415
  simp only [CollatzResearch.WordTrace]
  refine ⟨9023966398665184963007699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6015977599110123308671799 9023966398665184963007699)
  ·
    refine ⟨13535949597997777444511549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9023966398665184963007699 13535949597997777444511549)
    ·
      refine ⟨5075981099249166541691831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13535949597997777444511549 5075981099249166541691831)
      ·
        refine ⟨7613971648873749812537747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5075981099249166541691831 7613971648873749812537747)
        ·
          refine ⟨11420957473310624718806621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7613971648873749812537747 11420957473310624718806621)
          ·
            refine ⟨4282859052491484269552483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11420957473310624718806621 4282859052491484269552483)
            ·
              refine ⟨6424288578737226404328725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4282859052491484269552483 6424288578737226404328725)
              ·
                refine ⟨301138527128307487702909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6424288578737226404328725 301138527128307487702909)
                ·
                  refine ⟨112926947673115307888591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 301138527128307487702909 112926947673115307888591)
                  ·
                    rfl

theorem cell20_247415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 6, 3].length) (baseStart_247415 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_247415 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_247415 prefixEnd_247415 := by exact prefixLift 247415
  have htrace : WordTrace (prefixWord ++ tailWord_247415) baseStart_247415 baseEnd_247415 := by
    simpa [prefixWord, tailWord_247415, baseEnd_247415] using wordTrace_append hprefix tailTrace_247415
  have hstable : (prefixWord ++ tailWord_247415).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247415).length < 2 ^ (prefixWord ++ tailWord_247415).sum := by decide
  have hdescent : baseEnd_247415 < baseStart_247415 := by decide
  rcases family_descends (prefixWord ++ tailWord_247415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247428 : List Nat := [2, 3, 2, 1, 4, 2, 2, 1, 3]
def baseStart_247428 : Nat := 118140960795 + 247428 * 2 ^ 59
def prefixEnd_247428 : Nat := 4983230072969 + 3 ^ 40 * 247428 * 2
def baseEnd_247428 : Nat := 112932881227345040455205

theorem tailTrace_247428 : CollatzResearch.WordTrace tailWord_247428 prefixEnd_247428 112932881227345040455205 := by
  unfold tailWord_247428
  simp only [CollatzResearch.WordTrace]
  refine ⟨4512220273809044091615469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6016293698412058788820625 4512220273809044091615469)
  ·
    refine ⟨1692082602678391534355801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4512220273809044091615469 1692082602678391534355801)
    ·
      refine ⟨1269061952008793650766851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1692082602678391534355801 1269061952008793650766851)
      ·
        refine ⟨1903592928013190476150277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1269061952008793650766851 1903592928013190476150277)
        ·
          refine ⟨356923674002473214278177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1903592928013190476150277 356923674002473214278177)
          ·
            refine ⟨267692755501854910708633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 356923674002473214278177 267692755501854910708633)
            ·
              refine ⟨200769566626391183031475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 267692755501854910708633 200769566626391183031475)
              ·
                refine ⟨301154349939586774547213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200769566626391183031475 301154349939586774547213)
                ·
                  refine ⟨112932881227345040455205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 301154349939586774547213 112932881227345040455205)
                  ·
                    rfl

theorem cell20_247428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 2, 1, 3].length) (baseStart_247428 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_247428 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_247428 prefixEnd_247428 := by exact prefixLift 247428
  have htrace : WordTrace (prefixWord ++ tailWord_247428) baseStart_247428 baseEnd_247428 := by
    simpa [prefixWord, tailWord_247428, baseEnd_247428] using wordTrace_append hprefix tailTrace_247428
  have hstable : (prefixWord ++ tailWord_247428).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247428).length < 2 ^ (prefixWord ++ tailWord_247428).sum := by decide
  have hdescent : baseEnd_247428 < baseStart_247428 := by decide
  rcases family_descends (prefixWord ++ tailWord_247428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247484 : List Nat := [2, 2, 2, 3, 1, 2, 3, 5]
def baseStart_247484 : Nat := 118140960795 + 247484 * 2 ^ 59
def prefixEnd_247484 : Nat := 4983230072969 + 3 ^ 40 * 247484 * 2
def baseEnd_247484 : Nat := 37652813717752578196103

theorem tailTrace_247484 : CollatzResearch.WordTrace tailWord_247484 prefixEnd_247484 37652813717752578196103 := by
  unfold tailWord_247484
  simp only [CollatzResearch.WordTrace]
  refine ⟨4513241517707604873634753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6017655356943473164846337 4513241517707604873634753)
  ·
    refine ⟨3384931138280703655226065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4513241517707604873634753 3384931138280703655226065)
    ·
      refine ⟨2538698353710527741419549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3384931138280703655226065 2538698353710527741419549)
      ·
        refine ⟨952011882641447903032331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2538698353710527741419549 952011882641447903032331)
        ·
          refine ⟨1428017823962171854548497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 952011882641447903032331 1428017823962171854548497)
          ·
            refine ⟨1071013367971628890911373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1428017823962171854548497 1071013367971628890911373)
            ·
              refine ⟨401630012989360834091765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1071013367971628890911373 401630012989360834091765)
              ·
                refine ⟨37652813717752578196103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 401630012989360834091765 37652813717752578196103)
                ·
                  rfl

theorem cell20_247484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 5].length) (baseStart_247484 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_247484 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_247484 prefixEnd_247484 := by exact prefixLift 247484
  have htrace : WordTrace (prefixWord ++ tailWord_247484) baseStart_247484 baseEnd_247484 := by
    simpa [prefixWord, tailWord_247484, baseEnd_247484] using wordTrace_append hprefix tailTrace_247484
  have hstable : (prefixWord ++ tailWord_247484).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247484).length < 2 ^ (prefixWord ++ tailWord_247484).sum := by decide
  have hdescent : baseEnd_247484 < baseStart_247484 := by decide
  rcases family_descends (prefixWord ++ tailWord_247484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247490 : List Nat := [3, 5, 1, 2, 1, 1, 1, 2, 4]
def baseStart_247490 : Nat := 118140960795 + 247490 * 2 ^ 59
def prefixEnd_247490 : Nat := 4983230072969 + 3 ^ 40 * 247490 * 2
def baseEnd_247490 : Nat := 112961179716748380388285

theorem tailTrace_247490 : CollatzResearch.WordTrace tailWord_247490 prefixEnd_247490 112961179716748380388285 := by
  unfold tailWord_247490
  simp only [CollatzResearch.WordTrace]
  refine ⟨2256675468348368192996981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6017801248928981847991949 2256675468348368192996981)
  ·
    refine ⟨211563325157659518093467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2256675468348368192996981 211563325157659518093467)
    ·
      refine ⟨317344987736489277140201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211563325157659518093467 317344987736489277140201)
      ·
        refine ⟨238008740802366957855151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 317344987736489277140201 238008740802366957855151)
        ·
          refine ⟨357013111203550436782727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238008740802366957855151 357013111203550436782727)
          ·
            refine ⟨535519666805325655174091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357013111203550436782727 535519666805325655174091)
            ·
              refine ⟨803279500207988482761137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 535519666805325655174091 803279500207988482761137)
              ·
                refine ⟨602459625155991362070853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 803279500207988482761137 602459625155991362070853)
                ·
                  refine ⟨112961179716748380388285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 602459625155991362070853 112961179716748380388285)
                  ·
                    rfl

theorem cell20_247490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_247490 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_247490 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_247490 prefixEnd_247490 := by exact prefixLift 247490
  have htrace : WordTrace (prefixWord ++ tailWord_247490) baseStart_247490 baseEnd_247490 := by
    simpa [prefixWord, tailWord_247490, baseEnd_247490] using wordTrace_append hprefix tailTrace_247490
  have hstable : (prefixWord ++ tailWord_247490).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247490).length < 2 ^ (prefixWord ++ tailWord_247490).sum := by decide
  have hdescent : baseEnd_247490 < baseStart_247490 := by decide
  rcases family_descends (prefixWord ++ tailWord_247490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247558 : List Nat := [6, 2, 2, 1, 2, 1, 1, 3, 2]
def baseStart_247558 : Nat := 118140960795 + 247558 * 2 ^ 59
def prefixEnd_247558 : Nat := 4983230072969 + 3 ^ 40 * 247558 * 2
def baseEnd_247558 : Nat := 112992216769642366121341

theorem tailTrace_247558 : CollatzResearch.WordTrace tailWord_247558 prefixEnd_247558 112992216769642366121341 := by
  unfold tailWord_247558
  simp only [CollatzResearch.WordTrace]
  refine ⟨282161938660847512045729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6019454691431413590308885 282161938660847512045729)
  ·
    refine ⟨211621453995635634034297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282161938660847512045729 211621453995635634034297)
    ·
      refine ⟨158716090496726725525723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211621453995635634034297 158716090496726725525723)
      ·
        refine ⟨238074135745090088288585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158716090496726725525723 238074135745090088288585)
        ·
          refine ⟨178555601808817566216439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238074135745090088288585 178555601808817566216439)
          ·
            refine ⟨267833402713226349324659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178555601808817566216439 267833402713226349324659)
            ·
              refine ⟨401750104069839523986989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267833402713226349324659 401750104069839523986989)
              ·
                refine ⟨150656289026189821495121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 401750104069839523986989 150656289026189821495121)
                ·
                  refine ⟨112992216769642366121341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150656289026189821495121 112992216769642366121341)
                  ·
                    rfl

theorem cell20_247558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_247558 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_247558 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_247558 prefixEnd_247558 := by exact prefixLift 247558
  have htrace : WordTrace (prefixWord ++ tailWord_247558) baseStart_247558 baseEnd_247558 := by
    simpa [prefixWord, tailWord_247558, baseEnd_247558] using wordTrace_append hprefix tailTrace_247558
  have hstable : (prefixWord ++ tailWord_247558).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247558).length < 2 ^ (prefixWord ++ tailWord_247558).sum := by decide
  have hdescent : baseEnd_247558 < baseStart_247558 := by decide
  rcases family_descends (prefixWord ++ tailWord_247558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247601 : List Nat := [1, 2, 2, 3, 2, 4, 2, 1, 3]
def baseStart_247601 : Nat := 118140960795 + 247601 * 2 ^ 59
def prefixEnd_247601 : Nat := 4983230072969 + 3 ^ 40 * 247601 * 2
def baseEnd_247601 : Nat := 113011843141325327687831

theorem tailTrace_247601 : CollatzResearch.WordTrace tailWord_247601 prefixEnd_247601 113011843141325327687831 := by
  unfold tailWord_247601
  simp only [CollatzResearch.WordTrace]
  refine ⟨9030750375991338729278657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6020500250660892486185771 9030750375991338729278657)
  ·
    refine ⟨6773062781993504046958993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9030750375991338729278657 6773062781993504046958993)
    ·
      refine ⟨5079797086495128035219245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6773062781993504046958993 5079797086495128035219245)
      ·
        refine ⟨1904923907435673013207217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5079797086495128035219245 1904923907435673013207217)
        ·
          refine ⟨1428692930576754759905413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1904923907435673013207217 1428692930576754759905413)
          ·
            refine ⟨267879924483141517482265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1428692930576754759905413 267879924483141517482265)
            ·
              refine ⟨200909943362356138111699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 267879924483141517482265 200909943362356138111699)
              ·
                refine ⟨301364915043534207167549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200909943362356138111699 301364915043534207167549)
                ·
                  refine ⟨113011843141325327687831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 301364915043534207167549 113011843141325327687831)
                  ·
                    rfl

theorem cell20_247601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 2, 1, 3].length) (baseStart_247601 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_247601 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_247601 prefixEnd_247601 := by exact prefixLift 247601
  have htrace : WordTrace (prefixWord ++ tailWord_247601) baseStart_247601 baseEnd_247601 := by
    simpa [prefixWord, tailWord_247601, baseEnd_247601] using wordTrace_append hprefix tailTrace_247601
  have hstable : (prefixWord ++ tailWord_247601).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247601).length < 2 ^ (prefixWord ++ tailWord_247601).sum := by decide
  have hdescent : baseEnd_247601 < baseStart_247601 := by decide
  rcases family_descends (prefixWord ++ tailWord_247601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247612 : List Nat := [2, 2, 2, 2, 1, 1, 2, 4, 4]
def baseStart_247612 : Nat := 118140960795 + 247612 * 2 ^ 59
def prefixEnd_247612 : Nat := 4983230072969 + 3 ^ 40 * 247612 * 2
def baseEnd_247612 : Nat := 113016863841058178321119

theorem tailTrace_247612 : CollatzResearch.WordTrace tailWord_247612 prefixEnd_247612 113016863841058178321119 := by
  unfold tailWord_247612
  simp only [CollatzResearch.WordTrace]
  refine ⟨4515575789475743803964545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6020767719300991738619393 4515575789475743803964545)
  ·
    refine ⟨3386681842106807852973409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4515575789475743803964545 3386681842106807852973409)
    ·
      refine ⟨2540011381580105889730057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3386681842106807852973409 2540011381580105889730057)
      ·
        refine ⟨1905008536185079417297543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2540011381580105889730057 1905008536185079417297543)
        ·
          refine ⟨2857512804277619125946315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1905008536185079417297543 2857512804277619125946315)
          ·
            refine ⟨4286269206416428688919473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2857512804277619125946315 4286269206416428688919473)
            ·
              refine ⟨3214701904812321516689605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4286269206416428688919473 3214701904812321516689605)
              ·
                refine ⟨602756607152310284379301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3214701904812321516689605 602756607152310284379301)
                ·
                  refine ⟨113016863841058178321119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 602756607152310284379301 113016863841058178321119)
                  ·
                    rfl

theorem cell20_247612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 4, 4].length) (baseStart_247612 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_247612 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_247612 prefixEnd_247612 := by exact prefixLift 247612
  have htrace : WordTrace (prefixWord ++ tailWord_247612) baseStart_247612 baseEnd_247612 := by
    simpa [prefixWord, tailWord_247612, baseEnd_247612] using wordTrace_append hprefix tailTrace_247612
  have hstable : (prefixWord ++ tailWord_247612).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247612).length < 2 ^ (prefixWord ++ tailWord_247612).sum := by decide
  have hdescent : baseEnd_247612 < baseStart_247612 := by decide
  rcases family_descends (prefixWord ++ tailWord_247612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247619 : List Nat := [1, 1, 1, 3, 1, 5, 2, 6]
def baseStart_247619 : Nat := 118140960795 + 247619 * 2 ^ 59
def prefixEnd_247619 : Nat := 4983230072969 + 3 ^ 40 * 247619 * 2
def baseEnd_247619 : Nat := 37673352943932421695919

theorem tailTrace_247619 : CollatzResearch.WordTrace tailWord_247619 prefixEnd_247619 37673352943932421695919 := by
  unfold tailWord_247619
  simp only [CollatzResearch.WordTrace]
  refine ⟨9031406889926127803433911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6020937926617418535622607 9031406889926127803433911)
  ·
    refine ⟨13547110334889191705150867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9031406889926127803433911 13547110334889191705150867)
    ·
      refine ⟨20320665502333787557726301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13547110334889191705150867 20320665502333787557726301)
      ·
        refine ⟨7620249563375170334147363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20320665502333787557726301 7620249563375170334147363)
        ·
          refine ⟨11430374345062755501221045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7620249563375170334147363 11430374345062755501221045)
          ·
            refine ⟨1071597594849633328239473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11430374345062755501221045 1071597594849633328239473)
            ·
              refine ⟨803698196137224996179605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1071597594849633328239473 803698196137224996179605)
              ·
                refine ⟨37673352943932421695919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 803698196137224996179605 37673352943932421695919)
                ·
                  rfl

theorem cell20_247619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 6].length) (baseStart_247619 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_247619 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_247619 prefixEnd_247619 := by exact prefixLift 247619
  have htrace : WordTrace (prefixWord ++ tailWord_247619) baseStart_247619 baseEnd_247619 := by
    simpa [prefixWord, tailWord_247619, baseEnd_247619] using wordTrace_append hprefix tailTrace_247619
  have hstable : (prefixWord ++ tailWord_247619).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247619).length < 2 ^ (prefixWord ++ tailWord_247619).sum := by decide
  have hdescent : baseEnd_247619 < baseStart_247619 := by decide
  rcases family_descends (prefixWord ++ tailWord_247619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247664 : List Nat := [2, 1, 1, 1, 4, 1, 1, 2, 7]
def baseStart_247664 : Nat := 118140960795 + 247664 * 2 ^ 59
def prefixEnd_247664 : Nat := 4983230072969 + 3 ^ 40 * 247664 * 2
def baseEnd_247664 : Nat := 113040598057977108587573

theorem tailTrace_247664 : CollatzResearch.WordTrace tailWord_247664 prefixEnd_247664 113040598057977108587573 := by
  unfold tailWord_247664
  simp only [CollatzResearch.WordTrace]
  refine ⟨4516524087381550244411023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6022032116508733659214697 4516524087381550244411023)
  ·
    refine ⟨6774786131072325366616535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4516524087381550244411023 6774786131072325366616535)
    ·
      refine ⟨10162179196608488049924803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6774786131072325366616535 10162179196608488049924803)
      ·
        refine ⟨15243268794912732074887205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10162179196608488049924803 15243268794912732074887205)
        ·
          refine ⟨2858112899046137264041351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15243268794912732074887205 2858112899046137264041351)
          ·
            refine ⟨4287169348569205896062027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2858112899046137264041351 4287169348569205896062027)
            ·
              refine ⟨6430754022853808844093041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4287169348569205896062027 6430754022853808844093041)
              ·
                refine ⟨4823065517140356633069781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6430754022853808844093041 4823065517140356633069781)
                ·
                  refine ⟨113040598057977108587573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4823065517140356633069781 113040598057977108587573)
                  ·
                    rfl

theorem cell20_247664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 7].length) (baseStart_247664 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_247664 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_247664 prefixEnd_247664 := by exact prefixLift 247664
  have htrace : WordTrace (prefixWord ++ tailWord_247664) baseStart_247664 baseEnd_247664 := by
    simpa [prefixWord, tailWord_247664, baseEnd_247664] using wordTrace_append hprefix tailTrace_247664
  have hstable : (prefixWord ++ tailWord_247664).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247664).length < 2 ^ (prefixWord ++ tailWord_247664).sum := by decide
  have hdescent : baseEnd_247664 < baseStart_247664 := by decide
  rcases family_descends (prefixWord ++ tailWord_247664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247670 : List Nat := [5, 1, 1, 3, 2, 1, 3, 4]
def baseStart_247670 : Nat := 118140960795 + 247670 * 2 ^ 59
def prefixEnd_247670 : Nat := 4983230072969 + 3 ^ 40 * 247670 * 2
def baseEnd_247670 : Nat := 37681112207155918129183

theorem tailTrace_247670 : CollatzResearch.WordTrace tailWord_247670 prefixEnd_247670 37681112207155918129183 := by
  unfold tailWord_247670
  simp only [CollatzResearch.WordTrace]
  refine ⟨564579188296335219596279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6022178008494242342360309 564579188296335219596279)
  ·
    refine ⟨846868782444502829394419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 564579188296335219596279 846868782444502829394419)
    ·
      refine ⟨1270303173666754244091629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 846868782444502829394419 1270303173666754244091629)
      ·
        refine ⟨476363690125032841534361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1270303173666754244091629 476363690125032841534361)
        ·
          refine ⟨357272767593774631150771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 476363690125032841534361 357272767593774631150771)
          ·
            refine ⟨535909151390661946726157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357272767593774631150771 535909151390661946726157)
            ·
              refine ⟨200965931771498230022309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 535909151390661946726157 200965931771498230022309)
              ·
                refine ⟨37681112207155918129183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 200965931771498230022309 37681112207155918129183)
                ·
                  rfl

theorem cell20_247670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_247670 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_247670 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_247670 prefixEnd_247670 := by exact prefixLift 247670
  have htrace : WordTrace (prefixWord ++ tailWord_247670) baseStart_247670 baseEnd_247670 := by
    simpa [prefixWord, tailWord_247670, baseEnd_247670] using wordTrace_append hprefix tailTrace_247670
  have hstable : (prefixWord ++ tailWord_247670).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247670).length < 2 ^ (prefixWord ++ tailWord_247670).sum := by decide
  have hdescent : baseEnd_247670 < baseStart_247670 := by decide
  rcases family_descends (prefixWord ++ tailWord_247670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247694 : List Nat := [4, 1, 1, 5, 1, 2, 1, 2, 3]
def baseStart_247694 : Nat := 118140960795 + 247694 * 2 ^ 59
def prefixEnd_247694 : Nat := 4983230072969 + 3 ^ 40 * 247694 * 2
def baseEnd_247694 : Nat := 113054290875430337587451

theorem tailTrace_247694 : CollatzResearch.WordTrace tailWord_247694 prefixEnd_247694 113054290875430337587451 := by
  unfold tailWord_247694
  simp only [CollatzResearch.WordTrace]
  refine ⟨1129267795581801951551767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6022761576436277074942757 1129267795581801951551767)
  ·
    refine ⟨1693901693372702927327651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1129267795581801951551767 1693901693372702927327651)
    ·
      refine ⟨2540852540059054390991477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1693901693372702927327651 2540852540059054390991477)
      ·
        refine ⟨238204925630536349155451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2540852540059054390991477 238204925630536349155451)
        ·
          refine ⟨357307388445804523733177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238204925630536349155451 357307388445804523733177)
          ·
            refine ⟨267980541334353392799883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 357307388445804523733177 267980541334353392799883)
            ·
              refine ⟨401970812001530089199825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267980541334353392799883 401970812001530089199825)
              ·
                refine ⟨301478109001147566899869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 401970812001530089199825 301478109001147566899869)
                ·
                  refine ⟨113054290875430337587451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 301478109001147566899869 113054290875430337587451)
                  ·
                    rfl

theorem cell20_247694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 2, 3].length) (baseStart_247694 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_247694 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_247694 prefixEnd_247694 := by exact prefixLift 247694
  have htrace : WordTrace (prefixWord ++ tailWord_247694) baseStart_247694 baseEnd_247694 := by
    simpa [prefixWord, tailWord_247694, baseEnd_247694] using wordTrace_append hprefix tailTrace_247694
  have hstable : (prefixWord ++ tailWord_247694).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247694).length < 2 ^ (prefixWord ++ tailWord_247694).sum := by decide
  have hdescent : baseEnd_247694 < baseStart_247694 := by decide
  rcases family_descends (prefixWord ++ tailWord_247694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247698 : List Nat := [3, 2, 3, 2, 1, 2, 1, 1, 5]
def baseStart_247698 : Nat := 118140960795 + 247698 * 2 ^ 59
def prefixEnd_247698 : Nat := 4983230072969 + 3 ^ 40 * 247698 * 2
def baseEnd_247698 : Nat := 113056116584424101454101

theorem tailTrace_247698 : CollatzResearch.WordTrace tailWord_247698 prefixEnd_247698 113056116584424101454101 := by
  unfold tailWord_247698
  simp only [CollatzResearch.WordTrace]
  refine ⟨2258572064159981073889937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6022858837759949530373165 2258572064159981073889937)
  ·
    refine ⟨1693929048119985805417453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2258572064159981073889937 1693929048119985805417453)
    ·
      refine ⟨635223393044994677031545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1693929048119985805417453 635223393044994677031545)
      ·
        refine ⟨476417544783746007773659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 635223393044994677031545 476417544783746007773659)
        ·
          refine ⟨714626317175619011660489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 476417544783746007773659 714626317175619011660489)
          ·
            refine ⟨535969737881714258745367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 714626317175619011660489 535969737881714258745367)
            ·
              refine ⟨803954606822571388118051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 535969737881714258745367 803954606822571388118051)
              ·
                refine ⟨1205931910233857082177077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 803954606822571388118051 1205931910233857082177077)
                ·
                  refine ⟨113056116584424101454101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1205931910233857082177077 113056116584424101454101)
                  ·
                    rfl

theorem cell20_247698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_247698 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_247698 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_247698 prefixEnd_247698 := by exact prefixLift 247698
  have htrace : WordTrace (prefixWord ++ tailWord_247698) baseStart_247698 baseEnd_247698 := by
    simpa [prefixWord, tailWord_247698, baseEnd_247698] using wordTrace_append hprefix tailTrace_247698
  have hstable : (prefixWord ++ tailWord_247698).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247698).length < 2 ^ (prefixWord ++ tailWord_247698).sum := by decide
  have hdescent : baseEnd_247698 < baseStart_247698 := by decide
  rcases family_descends (prefixWord ++ tailWord_247698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247705 : List Nat := [1, 2, 1, 2, 1, 3, 4, 4, 2]
def baseStart_247705 : Nat := 118140960795 + 247705 * 2 ^ 59
def prefixEnd_247705 : Nat := 4983230072969 + 3 ^ 40 * 247705 * 2
def baseEnd_247705 : Nat := 113059311575163188220739

theorem tailTrace_247705 : CollatzResearch.WordTrace tailWord_247705 prefixEnd_247705 113059311575163188220739 := by
  unfold tailWord_247705
  simp only [CollatzResearch.WordTrace]
  refine ⟨9034543567614564491064569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6023029045076376327376379 9034543567614564491064569)
  ·
    refine ⟨6775907675710923368298427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9034543567614564491064569 6775907675710923368298427)
    ·
      refine ⟨10163861513566385052447641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6775907675710923368298427 10163861513566385052447641)
      ·
        refine ⟨7622896135174788789335731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10163861513566385052447641 7622896135174788789335731)
        ·
          refine ⟨11434344202762183184003597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7622896135174788789335731 11434344202762183184003597)
          ·
            refine ⟨4287879076035818694001349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11434344202762183184003597 4287879076035818694001349)
            ·
              refine ⟨803977326756716005125253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4287879076035818694001349 803977326756716005125253)
              ·
                refine ⟨150745748766884250960985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 803977326756716005125253 150745748766884250960985)
                ·
                  refine ⟨113059311575163188220739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150745748766884250960985 113059311575163188220739)
                  ·
                    rfl

theorem cell20_247705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 4, 2].length) (baseStart_247705 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_247705 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_247705 prefixEnd_247705 := by exact prefixLift 247705
  have htrace : WordTrace (prefixWord ++ tailWord_247705) baseStart_247705 baseEnd_247705 := by
    simpa [prefixWord, tailWord_247705, baseEnd_247705] using wordTrace_append hprefix tailTrace_247705
  have hstable : (prefixWord ++ tailWord_247705).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247705).length < 2 ^ (prefixWord ++ tailWord_247705).sum := by decide
  have hdescent : baseEnd_247705 < baseStart_247705 := by decide
  rcases family_descends (prefixWord ++ tailWord_247705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247729 : List Nat := [1, 2, 2, 4, 2, 3, 2, 4]
def baseStart_247729 : Nat := 118140960795 + 247729 * 2 ^ 59
def prefixEnd_247729 : Nat := 4983230072969 + 3 ^ 40 * 247729 * 2
def baseEnd_247729 : Nat := 37690088609708590473547

theorem tailTrace_247729 : CollatzResearch.WordTrace tailWord_247729 prefixEnd_247729 37690088609708590473547 := by
  unfold tailWord_247729
  simp only [CollatzResearch.WordTrace]
  refine ⟨9035418919527616589938241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6023612613018411059958827 9035418919527616589938241)
  ·
    refine ⟨6776564189645712442453681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9035418919527616589938241 6776564189645712442453681)
    ·
      refine ⟨5082423142234284331840261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6776564189645712442453681 5082423142234284331840261)
      ·
        refine ⟨952954339168928312220049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5082423142234284331840261 952954339168928312220049)
        ·
          refine ⟨714715754376696234165037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 952954339168928312220049 714715754376696234165037)
          ·
            refine ⟨268018407891261087811889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 714715754376696234165037 268018407891261087811889)
            ·
              refine ⟨201013805918445815858917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 268018407891261087811889 201013805918445815858917)
              ·
                refine ⟨37690088609708590473547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 201013805918445815858917 37690088609708590473547)
                ·
                  rfl

theorem cell20_247729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 2, 4].length) (baseStart_247729 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_247729 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_247729 prefixEnd_247729 := by exact prefixLift 247729
  have htrace : WordTrace (prefixWord ++ tailWord_247729) baseStart_247729 baseEnd_247729 := by
    simpa [prefixWord, tailWord_247729, baseEnd_247729] using wordTrace_append hprefix tailTrace_247729
  have hstable : (prefixWord ++ tailWord_247729).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247729).length < 2 ^ (prefixWord ++ tailWord_247729).sum := by decide
  have hdescent : baseEnd_247729 < baseStart_247729 := by decide
  rcases family_descends (prefixWord ++ tailWord_247729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247770 : List Nat := [3, 1, 1, 2, 6, 1, 2, 1, 3]
def baseStart_247770 : Nat := 118140960795 + 247770 * 2 ^ 59
def prefixEnd_247770 : Nat := 4983230072969 + 3 ^ 40 * 247770 * 2
def baseEnd_247770 : Nat := 113088979346311851053807

theorem tailTrace_247770 : CollatzResearch.WordTrace tailWord_247770 prefixEnd_247770 113088979346311851053807 := by
  unfold tailWord_247770
  simp only [CollatzResearch.WordTrace]
  refine ⟨2259228578094770148045191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6024609541586053728120509 2259228578094770148045191)
  ·
    refine ⟨3388842867142155222067787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2259228578094770148045191 3388842867142155222067787)
    ·
      refine ⟨5083264300713232833101681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3388842867142155222067787 5083264300713232833101681)
      ·
        refine ⟨3812448225534924624826261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5083264300713232833101681 3812448225534924624826261)
        ·
          refine ⟨178708510571949591788731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3812448225534924624826261 178708510571949591788731)
          ·
            refine ⟨268062765857924387683097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178708510571949591788731 268062765857924387683097)
            ·
              refine ⟨201047074393443290762323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 268062765857924387683097 201047074393443290762323)
              ·
                refine ⟨301570611590164936143485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201047074393443290762323 301570611590164936143485)
                ·
                  refine ⟨113088979346311851053807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 301570611590164936143485 113088979346311851053807)
                  ·
                    rfl

theorem cell20_247770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 2, 1, 3].length) (baseStart_247770 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_247770 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_247770 prefixEnd_247770 := by exact prefixLift 247770
  have htrace : WordTrace (prefixWord ++ tailWord_247770) baseStart_247770 baseEnd_247770 := by
    simpa [prefixWord, tailWord_247770, baseEnd_247770] using wordTrace_append hprefix tailTrace_247770
  have hstable : (prefixWord ++ tailWord_247770).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247770).length < 2 ^ (prefixWord ++ tailWord_247770).sum := by decide
  have hdescent : baseEnd_247770 < baseStart_247770 := by decide
  rcases family_descends (prefixWord ++ tailWord_247770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247815 : List Nat := [1, 1, 4, 3, 1, 4, 2, 2, 2]
def baseStart_247815 : Nat := 118140960795 + 247815 * 2 ^ 59
def prefixEnd_247815 : Nat := 4983230072969 + 3 ^ 40 * 247815 * 2
def baseEnd_247815 : Nat := 113109518572491694553623

theorem tailTrace_247815 : CollatzResearch.WordTrace tailWord_247815 prefixEnd_247815 113109518572491694553623 := by
  unfold tailWord_247815
  simp only [CollatzResearch.WordTrace]
  refine ⟨9038555597216053277568899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6025703731477368851712599 9038555597216053277568899)
  ·
    refine ⟨13557833395824079916353349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9038555597216053277568899 13557833395824079916353349)
    ·
      refine ⟨2542093761717014984316253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13557833395824079916353349 2542093761717014984316253)
      ·
        refine ⟨953285160643880619118595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2542093761717014984316253 953285160643880619118595)
        ·
          refine ⟨1429927740965820928677893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 953285160643880619118595 1429927740965820928677893)
          ·
            refine ⟨268111451431091424127105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1429927740965820928677893 268111451431091424127105)
            ·
              refine ⟨201083588573318568095329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 268111451431091424127105 201083588573318568095329)
              ·
                refine ⟨150812691429988926071497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201083588573318568095329 150812691429988926071497)
                ·
                  refine ⟨113109518572491694553623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150812691429988926071497 113109518572491694553623)
                  ·
                    rfl

theorem cell20_247815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 2, 2, 2].length) (baseStart_247815 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_247815 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_247815 prefixEnd_247815 := by exact prefixLift 247815
  have htrace : WordTrace (prefixWord ++ tailWord_247815) baseStart_247815 baseEnd_247815 := by
    simpa [prefixWord, tailWord_247815, baseEnd_247815] using wordTrace_append hprefix tailTrace_247815
  have hstable : (prefixWord ++ tailWord_247815).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247815).length < 2 ^ (prefixWord ++ tailWord_247815).sum := by decide
  have hdescent : baseEnd_247815 < baseStart_247815 := by decide
  rcases family_descends (prefixWord ++ tailWord_247815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247819 : List Nat := [1, 1, 1, 1, 6, 1, 3, 4, 2]
def baseStart_247819 : Nat := 118140960795 + 247819 * 2 ^ 59
def prefixEnd_247819 : Nat := 4983230072969 + 3 ^ 40 * 247819 * 2
def baseEnd_247819 : Nat := 113111344281485458420273

theorem tailTrace_247819 : CollatzResearch.WordTrace tailWord_247819 prefixEnd_247819 113111344281485458420273 := by
  unfold tailWord_247819
  simp only [CollatzResearch.WordTrace]
  refine ⟨9038701489201561960714511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6025800992801041307143007 9038701489201561960714511)
  ·
    refine ⟨13558052233802342941071767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9038701489201561960714511 13558052233802342941071767)
    ·
      refine ⟨20337078350703514411607651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13558052233802342941071767 20337078350703514411607651)
      ·
        refine ⟨30505617526055271617411477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20337078350703514411607651 30505617526055271617411477)
        ·
          refine ⟨1429950821533840857066163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 30505617526055271617411477 1429950821533840857066163)
          ·
            refine ⟨2144926232300761285599245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1429950821533840857066163 2144926232300761285599245)
            ·
              refine ⟨804347337112785482099717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2144926232300761285599245 804347337112785482099717)
              ·
                refine ⟨150815125708647277893697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 804347337112785482099717 150815125708647277893697)
                ·
                  refine ⟨113111344281485458420273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150815125708647277893697 113111344281485458420273)
                  ·
                    rfl

theorem cell20_247819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 4, 2].length) (baseStart_247819 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_247819 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_247819 prefixEnd_247819 := by exact prefixLift 247819
  have htrace : WordTrace (prefixWord ++ tailWord_247819) baseStart_247819 baseEnd_247819 := by
    simpa [prefixWord, tailWord_247819, baseEnd_247819] using wordTrace_append hprefix tailTrace_247819
  have hstable : (prefixWord ++ tailWord_247819).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247819).length < 2 ^ (prefixWord ++ tailWord_247819).sum := by decide
  have hdescent : baseEnd_247819 < baseStart_247819 := by decide
  rcases family_descends (prefixWord ++ tailWord_247819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247857 : List Nat := [1, 2, 2, 3, 1, 3, 1, 5, 2]
def baseStart_247857 : Nat := 118140960795 + 247857 * 2 ^ 59
def prefixEnd_247857 : Nat := 4983230072969 + 3 ^ 40 * 247857 * 2
def baseEnd_247857 : Nat := 113128688516926215153451

theorem tailTrace_247857 : CollatzResearch.WordTrace tailWord_247857 prefixEnd_247857 113128688516926215153451 := by
  unfold tailWord_247857
  simp only [CollatzResearch.WordTrace]
  refine ⟨9040087463063894450597825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6026724975375929633731883 9040087463063894450597825)
  ·
    refine ⟨6780065597297920837948369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9040087463063894450597825 6780065597297920837948369)
    ·
      refine ⟨5085049197973440628461277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6780065597297920837948369 5085049197973440628461277)
      ·
        refine ⟨1906893449240040235672979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5085049197973440628461277 1906893449240040235672979)
        ·
          refine ⟨2860340173860060353509469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1906893449240040235672979 2860340173860060353509469)
          ·
            refine ⟨1072627565197522632566051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2860340173860060353509469 1072627565197522632566051)
            ·
              refine ⟨1608941347796283948849077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1072627565197522632566051 1608941347796283948849077)
              ·
                refine ⟨150838251355901620204601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1608941347796283948849077 150838251355901620204601)
                ·
                  refine ⟨113128688516926215153451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150838251355901620204601 113128688516926215153451)
                  ·
                    rfl

theorem cell20_247857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 5, 2].length) (baseStart_247857 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_247857 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_247857 prefixEnd_247857 := by exact prefixLift 247857
  have htrace : WordTrace (prefixWord ++ tailWord_247857) baseStart_247857 baseEnd_247857 := by
    simpa [prefixWord, tailWord_247857, baseEnd_247857] using wordTrace_append hprefix tailTrace_247857
  have hstable : (prefixWord ++ tailWord_247857).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247857).length < 2 ^ (prefixWord ++ tailWord_247857).sum := by decide
  have hdescent : baseEnd_247857 < baseStart_247857 := by decide
  rcases family_descends (prefixWord ++ tailWord_247857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247871 : List Nat := [1, 1, 2, 2, 3, 1, 5, 2, 3]
def baseStart_247871 : Nat := 118140960795 + 247871 * 2 ^ 59
def prefixEnd_247871 : Nat := 4983230072969 + 3 ^ 40 * 247871 * 2
def baseEnd_247871 : Nat := 113135078498404388686727

theorem tailTrace_247871 : CollatzResearch.WordTrace tailWord_247871 prefixEnd_247871 113135078498404388686727 := by
  unfold tailWord_247871
  simp only [CollatzResearch.WordTrace]
  refine ⟨9040598085013174841607467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6027065390008783227738311 9040598085013174841607467)
  ·
    refine ⟨13560897127519762262411201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9040598085013174841607467 13560897127519762262411201)
    ·
      refine ⟨10170672845639821696808401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13560897127519762262411201 10170672845639821696808401)
      ·
        refine ⟨7628004634229866272606301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10170672845639821696808401 7628004634229866272606301)
        ·
          refine ⟨2860501737836199852227363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7628004634229866272606301 2860501737836199852227363)
          ·
            refine ⟨4290752606754299778341045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2860501737836199852227363 4290752606754299778341045)
            ·
              refine ⟨402258056883215604219473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4290752606754299778341045 402258056883215604219473)
              ·
                refine ⟨301693542662411703164605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 402258056883215604219473 301693542662411703164605)
                ·
                  refine ⟨113135078498404388686727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 301693542662411703164605 113135078498404388686727)
                  ·
                    rfl

theorem cell20_247871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 2, 3].length) (baseStart_247871 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_247871 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_247871 prefixEnd_247871 := by exact prefixLift 247871
  have htrace : WordTrace (prefixWord ++ tailWord_247871) baseStart_247871 baseEnd_247871 := by
    simpa [prefixWord, tailWord_247871, baseEnd_247871] using wordTrace_append hprefix tailTrace_247871
  have hstable : (prefixWord ++ tailWord_247871).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247871).length < 2 ^ (prefixWord ++ tailWord_247871).sum := by decide
  have hdescent : baseEnd_247871 < baseStart_247871 := by decide
  rcases family_descends (prefixWord ++ tailWord_247871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247933 : List Nat := [1, 4, 1, 1, 3, 4, 1, 1, 4]
def baseStart_247933 : Nat := 118140960795 + 247933 * 2 ^ 59
def prefixEnd_247933 : Nat := 4983230072969 + 3 ^ 40 * 247933 * 2
def baseEnd_247933 : Nat := 113163376987807728619807

theorem tailTrace_247933 : CollatzResearch.WordTrace tailWord_247933 prefixEnd_247933 113163376987807728619807 := by
  unfold tailWord_247933
  simp only [CollatzResearch.WordTrace]
  refine ⟨9042859410788559430364453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6028572940525706286909635 9042859410788559430364453)
  ·
    refine ⟨1695536139522854893193335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9042859410788559430364453 1695536139522854893193335)
    ·
      refine ⟨2543304209284282339790003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1695536139522854893193335 2543304209284282339790003)
      ·
        refine ⟨3814956313926423509685005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2543304209284282339790003 3814956313926423509685005)
        ·
          refine ⟨1430608617722408816131877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3814956313926423509685005 1430608617722408816131877)
          ·
            refine ⟨268239115822951653024727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1430608617722408816131877 268239115822951653024727)
            ·
              refine ⟨402358673734427479537091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268239115822951653024727 402358673734427479537091)
              ·
                refine ⟨603538010601641219305637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 402358673734427479537091 603538010601641219305637)
                ·
                  refine ⟨113163376987807728619807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 603538010601641219305637 113163376987807728619807)
                  ·
                    rfl

theorem cell20_247933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 1, 4].length) (baseStart_247933 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_247933 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_247933 prefixEnd_247933 := by exact prefixLift 247933
  have htrace : WordTrace (prefixWord ++ tailWord_247933) baseStart_247933 baseEnd_247933 := by
    simpa [prefixWord, tailWord_247933, baseEnd_247933] using wordTrace_append hprefix tailTrace_247933
  have hstable : (prefixWord ++ tailWord_247933).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247933).length < 2 ^ (prefixWord ++ tailWord_247933).sum := by decide
  have hdescent : baseEnd_247933 < baseStart_247933 := by decide
  rcases family_descends (prefixWord ++ tailWord_247933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247954 : List Nat := [3, 2, 3, 1, 1, 1, 2, 1, 6]
def baseStart_247954 : Nat := 118140960795 + 247954 * 2 ^ 59
def prefixEnd_247954 : Nat := 4983230072969 + 3 ^ 40 * 247954 * 2
def baseEnd_247954 : Nat := 113172961960024988919721

theorem tailTrace_247954 : CollatzResearch.WordTrace tailWord_247954 prefixEnd_247954 113172961960024988919721 := by
  unfold tailWord_247954
  simp only [CollatzResearch.WordTrace]
  refine ⟨2260906335928120004219729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6029083562474986677919277 2260906335928120004219729)
  ·
    refine ⟨1695679751946090003164797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2260906335928120004219729 1695679751946090003164797)
    ·
      refine ⟨635879906979783751186799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1695679751946090003164797 635879906979783751186799)
      ·
        refine ⟨953819860469675626780199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 635879906979783751186799 953819860469675626780199)
        ·
          refine ⟨1430729790704513440170299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 953819860469675626780199 1430729790704513440170299)
          ·
            refine ⟨2146094686056770160255449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1430729790704513440170299 2146094686056770160255449)
            ·
              refine ⟨1609571014542577620191587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2146094686056770160255449 1609571014542577620191587)
              ·
                refine ⟨2414356521813866430287381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1609571014542577620191587 2414356521813866430287381)
                ·
                  refine ⟨113172961960024988919721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2414356521813866430287381 113172961960024988919721)
                  ·
                    rfl

theorem cell20_247954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_247954 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_247954 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_247954 prefixEnd_247954 := by exact prefixLift 247954
  have htrace : WordTrace (prefixWord ++ tailWord_247954) baseStart_247954 baseEnd_247954 := by
    simpa [prefixWord, tailWord_247954, baseEnd_247954] using wordTrace_append hprefix tailTrace_247954
  have hstable : (prefixWord ++ tailWord_247954).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247954).length < 2 ^ (prefixWord ++ tailWord_247954).sum := by decide
  have hdescent : baseEnd_247954 < baseStart_247954 := by decide
  rcases family_descends (prefixWord ++ tailWord_247954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_247978 : List Nat := [3, 1, 5, 1, 2, 8]
def baseStart_247978 : Nat := 118140960795 + 247978 * 2 ^ 59
def prefixEnd_247978 : Nat := 4983230072969 + 3 ^ 40 * 247978 * 2
def baseEnd_247978 : Nat := 4191996896814354522949

theorem tailTrace_247978 : CollatzResearch.WordTrace tailWord_247978 prefixEnd_247978 4191996896814354522949 := by
  unfold tailWord_247978
  simp only [CollatzResearch.WordTrace]
  refine ⟨2261125173906383028938147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6029667130417021410501725 2261125173906383028938147)
  ·
    refine ⟨3391687760859574543407221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2261125173906383028938147 3391687760859574543407221)
    ·
      refine ⟨317970727580585113444427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3391687760859574543407221 317970727580585113444427)
      ·
        refine ⟨476956091370877670166641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317970727580585113444427 476956091370877670166641)
        ·
          refine ⟨357717068528158252624981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 476956091370877670166641 357717068528158252624981)
          ·
            refine ⟨4191996896814354522949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 357717068528158252624981 4191996896814354522949)
            ·
              rfl

theorem cell20_247978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 8].length) (baseStart_247978 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_247978 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_247978 prefixEnd_247978 := by exact prefixLift 247978
  have htrace : WordTrace (prefixWord ++ tailWord_247978) baseStart_247978 baseEnd_247978 := by
    simpa [prefixWord, tailWord_247978, baseEnd_247978] using wordTrace_append hprefix tailTrace_247978
  have hstable : (prefixWord ++ tailWord_247978).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_247978).length < 2 ^ (prefixWord ++ tailWord_247978).sum := by decide
  have hdescent : baseEnd_247978 < baseStart_247978 := by decide
  rcases family_descends (prefixWord ++ tailWord_247978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248037 : List Nat := [1, 3, 1, 4, 2, 2, 7]
def baseStart_248037 : Nat := 118140960795 + 248037 * 2 ^ 59
def prefixEnd_248037 : Nat := 4983230072969 + 3 ^ 40 * 248037 * 2
def baseEnd_248037 : Nat := 12578982824627287683635

theorem tailTrace_248037 : CollatzResearch.WordTrace tailWord_248037 prefixEnd_248037 12578982824627287683635 := by
  unfold tailWord_248037
  simp only [CollatzResearch.WordTrace]
  refine ⟨9046652602411785192150365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6031101734941190128100243 9046652602411785192150365)
  ·
    refine ⟨3392494725904419447056387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9046652602411785192150365 3392494725904419447056387)
    ·
      refine ⟨5088742088856629170584581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3392494725904419447056387 5088742088856629170584581)
      ·
        refine ⟨954139141660617969484609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5088742088856629170584581 954139141660617969484609)
        ·
          refine ⟨715604356245463477113457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 954139141660617969484609 715604356245463477113457)
          ·
            refine ⟨536703267184097607835093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 715604356245463477113457 536703267184097607835093)
            ·
              refine ⟨12578982824627287683635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 536703267184097607835093 12578982824627287683635)
              ·
                rfl

theorem cell20_248037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 7].length) (baseStart_248037 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_248037 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_248037 prefixEnd_248037 := by exact prefixLift 248037
  have htrace : WordTrace (prefixWord ++ tailWord_248037) baseStart_248037 baseEnd_248037 := by
    simpa [prefixWord, tailWord_248037, baseEnd_248037] using wordTrace_append hprefix tailTrace_248037
  have hstable : (prefixWord ++ tailWord_248037).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248037).length < 2 ^ (prefixWord ++ tailWord_248037).sum := by decide
  have hdescent : baseEnd_248037 < baseStart_248037 := by decide
  rcases family_descends (prefixWord ++ tailWord_248037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248040 : List Nat := [2, 1, 4, 1, 2, 4, 1, 2, 3]
def baseStart_248040 : Nat := 118140960795 + 248040 * 2 ^ 59
def prefixEnd_248040 : Nat := 4983230072969 + 3 ^ 40 * 248040 * 2
def baseEnd_248040 : Nat := 113212214703390912052703

theorem tailTrace_248040 : CollatzResearch.WordTrace tailWord_248040 prefixEnd_248040 113212214703390912052703 := by
  unfold tailWord_248040
  simp only [CollatzResearch.WordTrace]
  refine ⟨4523381010700458352254787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6031174680933944469673049 4523381010700458352254787)
  ·
    refine ⟨6785071516050687528382181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4523381010700458352254787 6785071516050687528382181)
    ·
      refine ⟨1272200909259503911571659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6785071516050687528382181 1272200909259503911571659)
      ·
        refine ⟨1908301363889255867357489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1272200909259503911571659 1908301363889255867357489)
        ·
          refine ⟨1431226022916941900518117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1908301363889255867357489 1431226022916941900518117)
          ·
            refine ⟨268354879296926606347147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1431226022916941900518117 268354879296926606347147)
            ·
              refine ⟨402532318945389909520721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268354879296926606347147 402532318945389909520721)
              ·
                refine ⟨301899239209042432140541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 402532318945389909520721 301899239209042432140541)
                ·
                  refine ⟨113212214703390912052703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 301899239209042432140541 113212214703390912052703)
                  ·
                    rfl

theorem cell20_248040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 2, 3].length) (baseStart_248040 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_248040 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_248040 prefixEnd_248040 := by exact prefixLift 248040
  have htrace : WordTrace (prefixWord ++ tailWord_248040) baseStart_248040 baseEnd_248040 := by
    simpa [prefixWord, tailWord_248040, baseEnd_248040] using wordTrace_append hprefix tailTrace_248040
  have hstable : (prefixWord ++ tailWord_248040).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248040).length < 2 ^ (prefixWord ++ tailWord_248040).sum := by decide
  have hdescent : baseEnd_248040 < baseStart_248040 := by decide
  rcases family_descends (prefixWord ++ tailWord_248040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248044 : List Nat := [2, 2, 1, 1, 2, 3, 3, 1, 5]
def baseStart_248044 : Nat := 118140960795 + 248044 * 2 ^ 59
def prefixEnd_248044 : Nat := 4983230072969 + 3 ^ 40 * 248044 * 2
def baseEnd_248044 : Nat := 113214040412384675919353

theorem tailTrace_248044 : CollatzResearch.WordTrace tailWord_248044 prefixEnd_248044 113214040412384675919353 := by
  unfold tailWord_248044
  simp only [CollatzResearch.WordTrace]
  refine ⟨4523453956693212693827593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6031271942257616925103457 4523453956693212693827593)
  ·
    refine ⟨3392590467519909520370695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4523453956693212693827593 3392590467519909520370695)
    ·
      refine ⟨5088885701279864280556043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3392590467519909520370695 5088885701279864280556043)
      ·
        refine ⟨7633328551919796420834065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5088885701279864280556043 7633328551919796420834065)
        ·
          refine ⟨5724996413939847315625549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7633328551919796420834065 5724996413939847315625549)
          ·
            refine ⟨2146873655227442743359581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5724996413939847315625549 2146873655227442743359581)
            ·
              refine ⟨805077620710291028759843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2146873655227442743359581 805077620710291028759843)
              ·
                refine ⟨1207616431065436543139765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 805077620710291028759843 1207616431065436543139765)
                ·
                  refine ⟨113214040412384675919353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1207616431065436543139765 113214040412384675919353)
                  ·
                    rfl

theorem cell20_248044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 5].length) (baseStart_248044 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_248044 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_248044 prefixEnd_248044 := by exact prefixLift 248044
  have htrace : WordTrace (prefixWord ++ tailWord_248044) baseStart_248044 baseEnd_248044 := by
    simpa [prefixWord, tailWord_248044, baseEnd_248044] using wordTrace_append hprefix tailTrace_248044
  have hstable : (prefixWord ++ tailWord_248044).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248044).length < 2 ^ (prefixWord ++ tailWord_248044).sum := by decide
  have hdescent : baseEnd_248044 < baseStart_248044 := by decide
  rcases family_descends (prefixWord ++ tailWord_248044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248047 : List Nat := [1, 1, 2, 1, 6, 1, 2, 4, 2]
def baseStart_248047 : Nat := 118140960795 + 248047 * 2 ^ 59
def prefixEnd_248047 : Nat := 4983230072969 + 3 ^ 40 * 248047 * 2
def baseEnd_248047 : Nat := 113215409694129998819341

theorem tailTrace_248047 : CollatzResearch.WordTrace tailWord_248047 prefixEnd_248047 113215409694129998819341 := by
  unfold tailWord_248047
  simp only [CollatzResearch.WordTrace]
  refine ⟨9047017332375556900014395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6031344888250371266676263 9047017332375556900014395)
  ·
    refine ⟨13570525998563335350021593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9047017332375556900014395 13570525998563335350021593)
    ·
      refine ⟨10177894498922501512516195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13570525998563335350021593 10177894498922501512516195)
      ·
        refine ⟨15266841748383752268774293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10177894498922501512516195 15266841748383752268774293)
        ·
          refine ⟨715633206955488387598795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15266841748383752268774293 715633206955488387598795)
          ·
            refine ⟨1073449810433232581398193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 715633206955488387598795 1073449810433232581398193)
            ·
              refine ⟨805087357824924436048645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1073449810433232581398193 805087357824924436048645)
              ·
                refine ⟨150953879592173331759121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 805087357824924436048645 150953879592173331759121)
                ·
                  refine ⟨113215409694129998819341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150953879592173331759121 113215409694129998819341)
                  ·
                    rfl

theorem cell20_248047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 4, 2].length) (baseStart_248047 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_248047 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_248047 prefixEnd_248047 := by exact prefixLift 248047
  have htrace : WordTrace (prefixWord ++ tailWord_248047) baseStart_248047 baseEnd_248047 := by
    simpa [prefixWord, tailWord_248047, baseEnd_248047] using wordTrace_append hprefix tailTrace_248047
  have hstable : (prefixWord ++ tailWord_248047).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248047).length < 2 ^ (prefixWord ++ tailWord_248047).sum := by decide
  have hdescent : baseEnd_248047 < baseStart_248047 := by decide
  rcases family_descends (prefixWord ++ tailWord_248047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248085 : List Nat := [1, 3, 2, 1, 2, 1, 5, 3, 2]
def baseStart_248085 : Nat := 118140960795 + 248085 * 2 ^ 59
def prefixEnd_248085 : Nat := 4983230072969 + 3 ^ 40 * 248085 * 2
def baseEnd_248085 : Nat := 113232753929570755552519

theorem tailTrace_248085 : CollatzResearch.WordTrace tailWord_248085 prefixEnd_248085 113232753929570755552519 := by
  unfold tailWord_248085
  simp only [CollatzResearch.WordTrace]
  refine ⟨9048403306237889389897709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6032268870825259593265139 9048403306237889389897709)
  ·
    refine ⟨3393151239839208521211641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9048403306237889389897709 3393151239839208521211641)
    ·
      refine ⟨2544863429879406390908731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3393151239839208521211641 2544863429879406390908731)
      ·
        refine ⟨3817295144819109586363097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2544863429879406390908731 3817295144819109586363097)
        ·
          refine ⟨2862971358614332189772323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3817295144819109586363097 2862971358614332189772323)
          ·
            refine ⟨4294457037921498284658485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2862971358614332189772323 4294457037921498284658485)
            ·
              refine ⟨402605347305140464186733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4294457037921498284658485 402605347305140464186733)
              ·
                refine ⟨150977005239427674070025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 402605347305140464186733 150977005239427674070025)
                ·
                  refine ⟨113232753929570755552519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150977005239427674070025 113232753929570755552519)
                  ·
                    rfl

theorem cell20_248085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 3, 2].length) (baseStart_248085 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_248085 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_248085 prefixEnd_248085 := by exact prefixLift 248085
  have htrace : WordTrace (prefixWord ++ tailWord_248085) baseStart_248085 baseEnd_248085 := by
    simpa [prefixWord, tailWord_248085, baseEnd_248085] using wordTrace_append hprefix tailTrace_248085
  have hstable : (prefixWord ++ tailWord_248085).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248085).length < 2 ^ (prefixWord ++ tailWord_248085).sum := by decide
  have hdescent : baseEnd_248085 < baseStart_248085 := by decide
  rcases family_descends (prefixWord ++ tailWord_248085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248109 : List Nat := [1, 5, 3, 1, 2, 1, 2, 5]
def baseStart_248109 : Nat := 118140960795 + 248109 * 2 ^ 59
def prefixEnd_248109 : Nat := 4983230072969 + 3 ^ 40 * 248109 * 2
def baseEnd_248109 : Nat := 37747902727844446250807

theorem tailTrace_248109 : CollatzResearch.WordTrace tailWord_248109 prefixEnd_248109 37747902727844446250807 := by
  unfold tailWord_248109
  simp only [CollatzResearch.WordTrace]
  refine ⟨9049278658150941488771381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6032852438767294325847587 9049278658150941488771381)
  ·
    refine ⟨848369874201650764572317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9049278658150941488771381 848369874201650764572317)
    ·
      refine ⟨318138702825619036714619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 848369874201650764572317 318138702825619036714619)
      ·
        refine ⟨477208054238428555071929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318138702825619036714619 477208054238428555071929)
        ·
          refine ⟨357906040678821416303947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 477208054238428555071929 357906040678821416303947)
          ·
            refine ⟨536859061018232124455921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357906040678821416303947 536859061018232124455921)
            ·
              refine ⟨402644295763674093341941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 536859061018232124455921 402644295763674093341941)
              ·
                refine ⟨37747902727844446250807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 402644295763674093341941 37747902727844446250807)
                ·
                  rfl

theorem cell20_248109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 5].length) (baseStart_248109 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_248109 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_248109 prefixEnd_248109 := by exact prefixLift 248109
  have htrace : WordTrace (prefixWord ++ tailWord_248109) baseStart_248109 baseEnd_248109 := by
    simpa [prefixWord, tailWord_248109, baseEnd_248109] using wordTrace_append hprefix tailTrace_248109
  have hstable : (prefixWord ++ tailWord_248109).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248109).length < 2 ^ (prefixWord ++ tailWord_248109).sum := by decide
  have hdescent : baseEnd_248109 < baseStart_248109 := by decide
  rcases family_descends (prefixWord ++ tailWord_248109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248116 : List Nat := [2, 5, 1, 1, 1, 3, 1, 3, 3]
def baseStart_248116 : Nat := 118140960795 + 248116 * 2 ^ 59
def prefixEnd_248116 : Nat := 4983230072969 + 3 ^ 40 * 248116 * 2
def baseEnd_248116 : Nat := 113246903174272425519059

theorem tailTrace_248116 : CollatzResearch.WordTrace tailWord_248116 prefixEnd_248116 113246903174272425519059 := by
  unfold tailWord_248116
  simp only [CollatzResearch.WordTrace]
  refine ⟨4524766984562790842138101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6033022646083721122850801 4524766984562790842138101)
  ·
    refine ⟨424196904802761641450447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4524766984562790842138101 424196904802761641450447)
    ·
      refine ⟨636295357204142462175671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424196904802761641450447 636295357204142462175671)
      ·
        refine ⟨954443035806213693263507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 636295357204142462175671 954443035806213693263507)
        ·
          refine ⟨1431664553709320539895261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 954443035806213693263507 1431664553709320539895261)
          ·
            refine ⟨536874207640995202460723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1431664553709320539895261 536874207640995202460723)
            ·
              refine ⟨805311311461492803691085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 536874207640995202460723 805311311461492803691085)
              ·
                refine ⟨301991741798059801384157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 805311311461492803691085 301991741798059801384157)
                ·
                  refine ⟨113246903174272425519059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 301991741798059801384157 113246903174272425519059)
                  ·
                    rfl

theorem cell20_248116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_248116 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_248116 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_248116 prefixEnd_248116 := by exact prefixLift 248116
  have htrace : WordTrace (prefixWord ++ tailWord_248116) baseStart_248116 baseEnd_248116 := by
    simpa [prefixWord, tailWord_248116, baseEnd_248116] using wordTrace_append hprefix tailTrace_248116
  have hstable : (prefixWord ++ tailWord_248116).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248116).length < 2 ^ (prefixWord ++ tailWord_248116).sum := by decide
  have hdescent : baseEnd_248116 < baseStart_248116 := by decide
  rcases family_descends (prefixWord ++ tailWord_248116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248127 : List Nat := [1, 1, 2, 2, 4, 1, 2, 1, 6]
def baseStart_248127 : Nat := 118140960795 + 248127 * 2 ^ 59
def prefixEnd_248127 : Nat := 4983230072969 + 3 ^ 40 * 248127 * 2
def baseEnd_248127 : Nat := 113251923874005276152347

theorem tailTrace_248127 : CollatzResearch.WordTrace tailWord_248127 prefixEnd_248127 113251923874005276152347 := by
  unfold tailWord_248127
  simp only [CollatzResearch.WordTrace]
  refine ⟨9049935172085730562926635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6033290114723820375284423 9049935172085730562926635)
  ·
    refine ⟨13574902758128595844389953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9049935172085730562926635 13574902758128595844389953)
    ·
      refine ⟨10181177068596446883292465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13574902758128595844389953 10181177068596446883292465)
      ·
        refine ⟨7635882801447335162469349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10181177068596446883292465 7635882801447335162469349)
        ·
          refine ⟨1431728025271375342963003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7635882801447335162469349 1431728025271375342963003)
          ·
            refine ⟨2147592037907063014444505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1431728025271375342963003 2147592037907063014444505)
            ·
              refine ⟨1610694028430297260833379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2147592037907063014444505 1610694028430297260833379)
              ·
                refine ⟨2416041042645445891250069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1610694028430297260833379 2416041042645445891250069)
                ·
                  refine ⟨113251923874005276152347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2416041042645445891250069 113251923874005276152347)
                  ·
                    rfl

theorem cell20_248127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 6].length) (baseStart_248127 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_248127 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_248127 prefixEnd_248127 := by exact prefixLift 248127
  have htrace : WordTrace (prefixWord ++ tailWord_248127) baseStart_248127 baseEnd_248127 := by
    simpa [prefixWord, tailWord_248127, baseEnd_248127] using wordTrace_append hprefix tailTrace_248127
  have hstable : (prefixWord ++ tailWord_248127).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248127).length < 2 ^ (prefixWord ++ tailWord_248127).sum := by decide
  have hdescent : baseEnd_248127 < baseStart_248127 := by decide
  rcases family_descends (prefixWord ++ tailWord_248127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248168 : List Nat := [2, 1, 4, 2, 2, 3, 1, 5]
def baseStart_248168 : Nat := 118140960795 + 248168 * 2 ^ 59
def prefixEnd_248168 : Nat := 4983230072969 + 3 ^ 40 * 248168 * 2
def baseEnd_248168 : Nat := 37756879130397118595171

theorem tailTrace_248168 : CollatzResearch.WordTrace tailWord_248168 prefixEnd_248168 37756879130397118595171 := by
  unfold tailWord_248168
  simp only [CollatzResearch.WordTrace]
  refine ⟨4525715282468597282584579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6034287043291463043446105 4525715282468597282584579)
  ·
    refine ⟨6788572923702895923876869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4525715282468597282584579 6788572923702895923876869)
    ·
      refine ⟨1272857423194292985726913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6788572923702895923876869 1272857423194292985726913)
      ·
        refine ⟨954643067395719739295185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1272857423194292985726913 954643067395719739295185)
        ·
          refine ⟨715982300546789804471389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 954643067395719739295185 715982300546789804471389)
          ·
            refine ⟨268493362705046176676771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 715982300546789804471389 268493362705046176676771)
            ·
              refine ⟨402740044057569265015157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268493362705046176676771 402740044057569265015157)
              ·
                refine ⟨37756879130397118595171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 402740044057569265015157 37756879130397118595171)
                ·
                  rfl

theorem cell20_248168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 5].length) (baseStart_248168 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_248168 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_248168 prefixEnd_248168 := by exact prefixLift 248168
  have htrace : WordTrace (prefixWord ++ tailWord_248168) baseStart_248168 baseEnd_248168 := by
    simpa [prefixWord, tailWord_248168, baseEnd_248168] using wordTrace_append hprefix tailTrace_248168
  have hstable : (prefixWord ++ tailWord_248168).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248168).length < 2 ^ (prefixWord ++ tailWord_248168).sum := by decide
  have hdescent : baseEnd_248168 < baseStart_248168 := by decide
  rcases family_descends (prefixWord ++ tailWord_248168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248196 : List Nat := [2, 3, 2, 1, 1, 2, 2, 2, 5]
def baseStart_248196 : Nat := 118140960795 + 248196 * 2 ^ 59
def prefixEnd_248196 : Nat := 4983230072969 + 3 ^ 40 * 248196 * 2
def baseEnd_248196 : Nat := 113283417354147702852065

theorem tailTrace_248196 : CollatzResearch.WordTrace tailWord_248196 prefixEnd_248196 113283417354147702852065 := by
  unfold tailWord_248196
  simp only [CollatzResearch.WordTrace]
  refine ⟨4526225904417877673594221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6034967872557170231458961 4526225904417877673594221)
  ·
    refine ⟨1697334714156704127597833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4526225904417877673594221 1697334714156704127597833)
    ·
      refine ⟨1273001035617528095698375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1697334714156704127597833 1273001035617528095698375)
      ·
        refine ⟨1909501553426292143547563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1273001035617528095698375 1909501553426292143547563)
        ·
          refine ⟨2864252330139438215321345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1909501553426292143547563 2864252330139438215321345)
          ·
            refine ⟨2148189247604578661491009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2864252330139438215321345 2148189247604578661491009)
            ·
              refine ⟨1611141935703433996118257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2148189247604578661491009 1611141935703433996118257)
              ·
                refine ⟨1208356451777575497088693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1611141935703433996118257 1208356451777575497088693)
                ·
                  refine ⟨113283417354147702852065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1208356451777575497088693 113283417354147702852065)
                  ·
                    rfl

theorem cell20_248196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_248196 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_248196 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_248196 prefixEnd_248196 := by exact prefixLift 248196
  have htrace : WordTrace (prefixWord ++ tailWord_248196) baseStart_248196 baseEnd_248196 := by
    simpa [prefixWord, tailWord_248196, baseEnd_248196] using wordTrace_append hprefix tailTrace_248196
  have hstable : (prefixWord ++ tailWord_248196).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248196).length < 2 ^ (prefixWord ++ tailWord_248196).sum := by decide
  have hdescent : baseEnd_248196 < baseStart_248196 := by decide
  rcases family_descends (prefixWord ++ tailWord_248196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248199 : List Nat := [1, 1, 4, 2, 2, 1, 4, 3, 2]
def baseStart_248199 : Nat := 118140960795 + 248199 * 2 ^ 59
def prefixEnd_248199 : Nat := 4983230072969 + 3 ^ 40 * 248199 * 2
def baseEnd_248199 : Nat := 113284786635893025752053

theorem tailTrace_248199 : CollatzResearch.WordTrace tailWord_248199 prefixEnd_248199 113284786635893025752053 := by
  unfold tailWord_248199
  simp only [CollatzResearch.WordTrace]
  refine ⟨9052561227824886859547651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6035040818549924573031767 9052561227824886859547651)
  ·
    refine ⟨13578841841737330289321477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9052561227824886859547651 13578841841737330289321477)
    ·
      refine ⟨2546032845325749429247777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13578841841737330289321477 2546032845325749429247777)
      ·
        refine ⟨1909524633994312071935833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2546032845325749429247777 1909524633994312071935833)
        ·
          refine ⟨1432143475495734053951875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1909524633994312071935833 1432143475495734053951875)
          ·
            refine ⟨2148215213243601080927813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1432143475495734053951875 2148215213243601080927813)
            ·
              refine ⟨402790352483175202673965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2148215213243601080927813 402790352483175202673965)
              ·
                refine ⟨151046382181190701002737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 402790352483175202673965 151046382181190701002737)
                ·
                  refine ⟨113284786635893025752053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 151046382181190701002737 113284786635893025752053)
                  ·
                    rfl

theorem cell20_248199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 3, 2].length) (baseStart_248199 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_248199 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_248199 prefixEnd_248199 := by exact prefixLift 248199
  have htrace : WordTrace (prefixWord ++ tailWord_248199) baseStart_248199 baseEnd_248199 := by
    simpa [prefixWord, tailWord_248199, baseEnd_248199] using wordTrace_append hprefix tailTrace_248199
  have hstable : (prefixWord ++ tailWord_248199).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248199).length < 2 ^ (prefixWord ++ tailWord_248199).sum := by decide
  have hdescent : baseEnd_248199 < baseStart_248199 := by decide
  rcases family_descends (prefixWord ++ tailWord_248199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248326 : List Nat := [6, 2, 1, 1, 1, 2, 1, 4, 2]
def baseStart_248326 : Nat := 118140960795 + 248326 * 2 ^ 59
def prefixEnd_248326 : Nat := 4983230072969 + 3 ^ 40 * 248326 * 2
def baseEnd_248326 : Nat := 113342752896445028518201

theorem tailTrace_248326 : CollatzResearch.WordTrace tailWord_248326 prefixEnd_248326 113342752896445028518201 := by
  unfold tailWord_248326
  simp only [CollatzResearch.WordTrace]
  refine ⟨283037290573899610919401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6038128865576525032947221 283037290573899610919401)
  ·
    refine ⟨212277967930424708189551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 283037290573899610919401 212277967930424708189551)
    ·
      refine ⟨318416951895637062284327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212277967930424708189551 318416951895637062284327)
      ·
        refine ⟨477625427843455593426491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318416951895637062284327 477625427843455593426491)
        ·
          refine ⟨716438141765183390139737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 477625427843455593426491 716438141765183390139737)
          ·
            refine ⟨537328606323887542604803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 716438141765183390139737 537328606323887542604803)
            ·
              refine ⟨805992909485831313907205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 537328606323887542604803 805992909485831313907205)
              ·
                refine ⟨151123670528593371357601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 805992909485831313907205 151123670528593371357601)
                ·
                  refine ⟨113342752896445028518201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 151123670528593371357601 113342752896445028518201)
                  ·
                    rfl

theorem cell20_248326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_248326 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_248326 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_248326 prefixEnd_248326 := by exact prefixLift 248326
  have htrace : WordTrace (prefixWord ++ tailWord_248326) baseStart_248326 baseEnd_248326 := by
    simpa [prefixWord, tailWord_248326, baseEnd_248326] using wordTrace_append hprefix tailTrace_248326
  have hstable : (prefixWord ++ tailWord_248326).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248326).length < 2 ^ (prefixWord ++ tailWord_248326).sum := by decide
  have hdescent : baseEnd_248326 < baseStart_248326 := by decide
  rcases family_descends (prefixWord ++ tailWord_248326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248355 : List Nat := [1, 1, 1, 4, 4, 1, 1, 1, 6]
def baseStart_248355 : Nat := 118140960795 + 248355 * 2 ^ 59
def prefixEnd_248355 : Nat := 4983230072969 + 3 ^ 40 * 248355 * 2
def baseEnd_248355 : Nat := 113355989286649816551415

theorem tailTrace_248355 : CollatzResearch.WordTrace tailWord_248355 prefixEnd_248355 113355989286649816551415 := by
  unfold tailWord_248355
  simp only [CollatzResearch.WordTrace]
  refine ⟨9058251015259725502226519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6038834010173150334817679 9058251015259725502226519)
  ·
    refine ⟨13587376522889588253339779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9058251015259725502226519 13587376522889588253339779)
    ·
      refine ⟨20381064784334382380009669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13587376522889588253339779 20381064784334382380009669)
      ·
        refine ⟨3821449647062696696251813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20381064784334382380009669 3821449647062696696251813)
        ·
          refine ⟨716521808824255630547215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3821449647062696696251813 716521808824255630547215)
          ·
            refine ⟨1074782713236383445820823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 716521808824255630547215 1074782713236383445820823)
            ·
              refine ⟨1612174069854575168731235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1074782713236383445820823 1612174069854575168731235)
              ·
                refine ⟨2418261104781862753096853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1612174069854575168731235 2418261104781862753096853)
                ·
                  refine ⟨113355989286649816551415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2418261104781862753096853 113355989286649816551415)
                  ·
                    rfl

theorem cell20_248355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 6].length) (baseStart_248355 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_248355 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_248355 prefixEnd_248355 := by exact prefixLift 248355
  have htrace : WordTrace (prefixWord ++ tailWord_248355) baseStart_248355 baseEnd_248355 := by
    simpa [prefixWord, tailWord_248355, baseEnd_248355] using wordTrace_append hprefix tailTrace_248355
  have hstable : (prefixWord ++ tailWord_248355).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248355).length < 2 ^ (prefixWord ++ tailWord_248355).sum := by decide
  have hdescent : baseEnd_248355 < baseStart_248355 := by decide
  rcases family_descends (prefixWord ++ tailWord_248355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248382 : List Nat := [4, 2, 1, 4, 1, 1, 1, 1, 5]
def baseStart_248382 : Nat := 118140960795 + 248382 * 2 ^ 59
def prefixEnd_248382 : Nat := 4983230072969 + 3 ^ 40 * 248382 * 2
def baseEnd_248382 : Nat := 113368312822357722651305

theorem tailTrace_248382 : CollatzResearch.WordTrace tailWord_248382 prefixEnd_248382 113368312822357722651305 := by
  unfold tailWord_248382
  simp only [CollatzResearch.WordTrace]
  refine ⟨1132404473270238639182425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6039490524107939408972933 1132404473270238639182425)
  ·
    refine ⟨849303354952678979386819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1132404473270238639182425 849303354952678979386819)
    ·
      refine ⟨1273955032429018469080229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 849303354952678979386819 1273955032429018469080229)
      ·
        refine ⟨238866568580440962952543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1273955032429018469080229 238866568580440962952543)
        ·
          refine ⟨358299852870661444428815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238866568580440962952543 358299852870661444428815)
          ·
            refine ⟨537449779305992166643223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358299852870661444428815 537449779305992166643223)
            ·
              refine ⟨806174668958988249964835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 537449779305992166643223 806174668958988249964835)
              ·
                refine ⟨1209262003438482374947253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 806174668958988249964835 1209262003438482374947253)
                ·
                  refine ⟨113368312822357722651305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1209262003438482374947253 113368312822357722651305)
                  ·
                    rfl

theorem cell20_248382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_248382 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_248382 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_248382 prefixEnd_248382 := by exact prefixLift 248382
  have htrace : WordTrace (prefixWord ++ tailWord_248382) baseStart_248382 baseEnd_248382 := by
    simpa [prefixWord, tailWord_248382, baseEnd_248382] using wordTrace_append hprefix tailTrace_248382
  have hstable : (prefixWord ++ tailWord_248382).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248382).length < 2 ^ (prefixWord ++ tailWord_248382).sum := by decide
  have hdescent : baseEnd_248382 < baseStart_248382 := by decide
  rcases family_descends (prefixWord ++ tailWord_248382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248417 : List Nat := [1, 2, 3, 1, 1, 4, 4, 4]
def baseStart_248417 : Nat := 118140960795 + 248417 * 2 ^ 59
def prefixEnd_248417 : Nat := 4983230072969 + 3 ^ 40 * 248417 * 2
def baseEnd_248417 : Nat := 37794762592017718828165

theorem tailTrace_248417 : CollatzResearch.WordTrace tailWord_248417 prefixEnd_248417 37794762592017718828165 := by
  unfold tailWord_248417
  simp only [CollatzResearch.WordTrace]
  refine ⟨9060512341035110090983505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6040341560690073393989003 9060512341035110090983505)
  ·
    refine ⟨6795384255776332568237629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9060512341035110090983505 6795384255776332568237629)
    ·
      refine ⟨2548269095916124713089111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6795384255776332568237629 2548269095916124713089111)
      ·
        refine ⟨3822403643874187069633667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2548269095916124713089111 3822403643874187069633667)
        ·
          refine ⟨5733605465811280604450501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3822403643874187069633667 5733605465811280604450501)
          ·
            refine ⟨1075051024839615113334469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5733605465811280604450501 1075051024839615113334469)
            ·
              refine ⟨201572067157427833750213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1075051024839615113334469 201572067157427833750213)
              ·
                refine ⟨37794762592017718828165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 201572067157427833750213 37794762592017718828165)
                ·
                  rfl

theorem cell20_248417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 4, 4].length) (baseStart_248417 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_248417 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_248417 prefixEnd_248417 := by exact prefixLift 248417
  have htrace : WordTrace (prefixWord ++ tailWord_248417) baseStart_248417 baseEnd_248417 := by
    simpa [prefixWord, tailWord_248417, baseEnd_248417] using wordTrace_append hprefix tailTrace_248417
  have hstable : (prefixWord ++ tailWord_248417).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248417).length < 2 ^ (prefixWord ++ tailWord_248417).sum := by decide
  have hdescent : baseEnd_248417 < baseStart_248417 := by decide
  rcases family_descends (prefixWord ++ tailWord_248417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248434 : List Nat := [3, 2, 1, 2, 5, 1, 6]
def baseStart_248434 : Nat := 118140960795 + 248434 * 2 ^ 59
def prefixEnd_248434 : Nat := 4983230072969 + 3 ^ 40 * 248434 * 2
def baseEnd_248434 : Nat := 12599116337697405879751

theorem tailTrace_248434 : CollatzResearch.WordTrace tailWord_248434 prefixEnd_248434 12599116337697405879751 := by
  unfold tailWord_248434
  simp only [CollatzResearch.WordTrace]
  refine ⟨2265283095493380498588089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6040754921315681329568237 2265283095493380498588089)
  ·
    refine ⟨1698962321620035373941067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2265283095493380498588089 1698962321620035373941067)
    ·
      refine ⟨2548443482430053060911601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1698962321620035373941067 2548443482430053060911601)
      ·
        refine ⟨1911332611822539795683701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2548443482430053060911601 1911332611822539795683701)
        ·
          refine ⟨179187432358363105845347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1911332611822539795683701 179187432358363105845347)
          ·
            refine ⟨268781148537544658768021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179187432358363105845347 268781148537544658768021)
            ·
              refine ⟨12599116337697405879751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 268781148537544658768021 12599116337697405879751)
              ·
                rfl

theorem cell20_248434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 6].length) (baseStart_248434 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_248434 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_248434 prefixEnd_248434 := by exact prefixLift 248434
  have htrace : WordTrace (prefixWord ++ tailWord_248434) baseStart_248434 baseEnd_248434 := by
    simpa [prefixWord, tailWord_248434, baseEnd_248434] using wordTrace_append hprefix tailTrace_248434
  have hstable : (prefixWord ++ tailWord_248434).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248434).length < 2 ^ (prefixWord ++ tailWord_248434).sum := by decide
  have hdescent : baseEnd_248434 < baseStart_248434 := by decide
  rcases family_descends (prefixWord ++ tailWord_248434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248448 : List Nat := [2, 1, 1, 2, 1, 7, 1, 1, 4]
def baseStart_248448 : Nat := 118140960795 + 248448 * 2 ^ 59
def prefixEnd_248448 : Nat := 4983230072969 + 3 ^ 40 * 248448 * 2
def baseEnd_248448 : Nat := 113398437020754826451035

theorem tailTrace_248448 : CollatzResearch.WordTrace tailWord_248448 prefixEnd_248448 113398437020754826451035 := by
  unfold tailWord_248448
  simp only [CollatzResearch.WordTrace]
  refine ⟨4530821501961401192680999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6041095335948534923574665 4530821501961401192680999)
  ·
    refine ⟨6796232252942101789021499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4530821501961401192680999 6796232252942101789021499)
    ·
      refine ⟨10194348379413152683532249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6796232252942101789021499 10194348379413152683532249)
      ·
        refine ⟨7645761284559864512649187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10194348379413152683532249 7645761284559864512649187)
        ·
          refine ⟨11468641926839796768973781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7645761284559864512649187 11468641926839796768973781)
          ·
            refine ⟨268796295160307736772823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 11468641926839796768973781 268796295160307736772823)
            ·
              refine ⟨403194442740461605159235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268796295160307736772823 403194442740461605159235)
              ·
                refine ⟨604791664110692407738853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 403194442740461605159235 604791664110692407738853)
                ·
                  refine ⟨113398437020754826451035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 604791664110692407738853 113398437020754826451035)
                  ·
                    rfl

theorem cell20_248448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 1, 4].length) (baseStart_248448 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_248448 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_248448 prefixEnd_248448 := by exact prefixLift 248448
  have htrace : WordTrace (prefixWord ++ tailWord_248448) baseStart_248448 baseEnd_248448 := by
    simpa [prefixWord, tailWord_248448, baseEnd_248448] using wordTrace_append hprefix tailTrace_248448
  have hstable : (prefixWord ++ tailWord_248448).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248448).length < 2 ^ (prefixWord ++ tailWord_248448).sum := by decide
  have hdescent : baseEnd_248448 < baseStart_248448 := by decide
  rcases family_descends (prefixWord ++ tailWord_248448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248450 : List Nat := [3, 4, 3, 1, 2, 1, 2, 1, 3]
def baseStart_248450 : Nat := 118140960795 + 248450 * 2 ^ 59
def prefixEnd_248450 : Nat := 4983230072969 + 3 ^ 40 * 248450 * 2
def baseEnd_248450 : Nat := 113399349875251708384361

theorem tailTrace_248450 : CollatzResearch.WordTrace tailWord_248450 prefixEnd_248450 113399349875251708384361 := by
  unfold tailWord_248450
  simp only [CollatzResearch.WordTrace]
  refine ⟨2265428987478889181733701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6041143966610371151289869 2265428987478889181733701)
  ·
    refine ⟨424767935152291721575069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2265428987478889181733701 424767935152291721575069)
    ·
      refine ⟨159287975682109395590651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 424767935152291721575069 159287975682109395590651)
      ·
        refine ⟨238931963523164093385977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159287975682109395590651 238931963523164093385977)
        ·
          refine ⟨179198972642373070039483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238931963523164093385977 179198972642373070039483)
          ·
            refine ⟨268798458963559605059225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179198972642373070039483 268798458963559605059225)
            ·
              refine ⟨201598844222669703794419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 268798458963559605059225 201598844222669703794419)
              ·
                refine ⟨302398266334004555691629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201598844222669703794419 302398266334004555691629)
                ·
                  refine ⟨113399349875251708384361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 302398266334004555691629 113399349875251708384361)
                  ·
                    rfl

theorem cell20_248450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_248450 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_248450 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_248450 prefixEnd_248450 := by exact prefixLift 248450
  have htrace : WordTrace (prefixWord ++ tailWord_248450) baseStart_248450 baseEnd_248450 := by
    simpa [prefixWord, tailWord_248450, baseEnd_248450] using wordTrace_append hprefix tailTrace_248450
  have hstable : (prefixWord ++ tailWord_248450).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248450).length < 2 ^ (prefixWord ++ tailWord_248450).sum := by decide
  have hdescent : baseEnd_248450 < baseStart_248450 := by decide
  rcases family_descends (prefixWord ++ tailWord_248450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248483 : List Nat := [1, 1, 1, 4, 1, 1, 2, 4, 5]
def baseStart_248483 : Nat := 118140960795 + 248483 * 2 ^ 59
def prefixEnd_248483 : Nat := 4983230072969 + 3 ^ 40 * 248483 * 2
def baseEnd_248483 : Nat := 113414411974450260284225

theorem tailTrace_248483 : CollatzResearch.WordTrace tailWord_248483 prefixEnd_248483 113414411974450260284225 := by
  unfold tailWord_248483
  simp only [CollatzResearch.WordTrace]
  refine ⟨9062919558796003362886103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6041946372530668908590735 9062919558796003362886103)
  ·
    refine ⟨13594379338194005044329155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9062919558796003362886103 13594379338194005044329155)
    ·
      refine ⟨20391569007291007566493733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13594379338194005044329155 20391569007291007566493733)
      ·
        refine ⟨3823419188867063918717575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20391569007291007566493733 3823419188867063918717575)
        ·
          refine ⟨5735128783300595878076363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3823419188867063918717575 5735128783300595878076363)
          ·
            refine ⟨8602693174950893817114545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5735128783300595878076363 8602693174950893817114545)
            ·
              refine ⟨6452019881213170362835909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8602693174950893817114545 6452019881213170362835909)
              ·
                refine ⟨1209753727727469443031733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6452019881213170362835909 1209753727727469443031733)
                ·
                  refine ⟨113414411974450260284225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1209753727727469443031733 113414411974450260284225)
                  ·
                    rfl

theorem cell20_248483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4, 5].length) (baseStart_248483 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_248483 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_248483 prefixEnd_248483 := by exact prefixLift 248483
  have htrace : WordTrace (prefixWord ++ tailWord_248483) baseStart_248483 baseEnd_248483 := by
    simpa [prefixWord, tailWord_248483, baseEnd_248483] using wordTrace_append hprefix tailTrace_248483
  have hstable : (prefixWord ++ tailWord_248483).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248483).length < 2 ^ (prefixWord ++ tailWord_248483).sum := by decide
  have hdescent : baseEnd_248483 < baseStart_248483 := by decide
  rcases family_descends (prefixWord ++ tailWord_248483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248503 : List Nat := [1, 1, 3, 1, 6, 1, 1, 4, 2]
def baseStart_248503 : Nat := 118140960795 + 248503 * 2 ^ 59
def prefixEnd_248503 : Nat := 4983230072969 + 3 ^ 40 * 248503 * 2
def baseEnd_248503 : Nat := 113423540519419079617477

theorem tailTrace_248503 : CollatzResearch.WordTrace tailWord_248503 prefixEnd_248503 113423540519419079617477 := by
  unfold tailWord_248503
  simp only [CollatzResearch.WordTrace]
  refine ⟨9063649018723546778614163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6042432679149031185742775 9063649018723546778614163)
  ·
    refine ⟨13595473528085320167921245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9063649018723546778614163 13595473528085320167921245)
    ·
      refine ⟨5098302573031995062970467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13595473528085320167921245 5098302573031995062970467)
      ·
        refine ⟨7647453859547992594455701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5098302573031995062970467 7647453859547992594455701)
        ·
          refine ⟨358474399666312152865111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7647453859547992594455701 358474399666312152865111)
          ·
            refine ⟨537711599499468229297667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358474399666312152865111 537711599499468229297667)
            ·
              refine ⟨806567399249202343946501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 537711599499468229297667 806567399249202343946501)
              ·
                refine ⟨151231387359225439489969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 806567399249202343946501 151231387359225439489969)
                ·
                  refine ⟨113423540519419079617477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 151231387359225439489969 113423540519419079617477)
                  ·
                    rfl

theorem cell20_248503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 4, 2].length) (baseStart_248503 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_248503 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_248503 prefixEnd_248503 := by exact prefixLift 248503
  have htrace : WordTrace (prefixWord ++ tailWord_248503) baseStart_248503 baseEnd_248503 := by
    simpa [prefixWord, tailWord_248503, baseEnd_248503] using wordTrace_append hprefix tailTrace_248503
  have hstable : (prefixWord ++ tailWord_248503).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248503).length < 2 ^ (prefixWord ++ tailWord_248503).sum := by decide
  have hdescent : baseEnd_248503 < baseStart_248503 := by decide
  rcases family_descends (prefixWord ++ tailWord_248503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248524 : List Nat := [2, 2, 1, 5, 1, 2, 1, 2, 4]
def baseStart_248524 : Nat := 118140960795 + 248524 * 2 ^ 59
def prefixEnd_248524 : Nat := 4983230072969 + 3 ^ 40 * 248524 * 2
def baseEnd_248524 : Nat := 113433125491636339917391

theorem tailTrace_248524 : CollatzResearch.WordTrace tailWord_248524 prefixEnd_248524 113433125491636339917391 := by
  unfold tailWord_248524
  simp only [CollatzResearch.WordTrace]
  refine ⟨4532207475823733682564313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6042943301098311576752417 4532207475823733682564313)
  ·
    refine ⟨3399155606867800261923235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4532207475823733682564313 3399155606867800261923235)
    ·
      refine ⟨5098733410301700392884853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3399155606867800261923235 5098733410301700392884853)
      ·
        refine ⟨478006257215784411832955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5098733410301700392884853 478006257215784411832955)
        ·
          refine ⟨717009385823676617749433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 478006257215784411832955 717009385823676617749433)
          ·
            refine ⟨537757039367757463312075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 717009385823676617749433 537757039367757463312075)
            ·
              refine ⟨806635559051636194968113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 537757039367757463312075 806635559051636194968113)
              ·
                refine ⟨604976669288727146226085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 806635559051636194968113 604976669288727146226085)
                ·
                  refine ⟨113433125491636339917391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 604976669288727146226085 113433125491636339917391)
                  ·
                    rfl

theorem cell20_248524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 2, 4].length) (baseStart_248524 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_248524 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_248524 prefixEnd_248524 := by exact prefixLift 248524
  have htrace : WordTrace (prefixWord ++ tailWord_248524) baseStart_248524 baseEnd_248524 := by
    simpa [prefixWord, tailWord_248524, baseEnd_248524] using wordTrace_append hprefix tailTrace_248524
  have hstable : (prefixWord ++ tailWord_248524).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248524).length < 2 ^ (prefixWord ++ tailWord_248524).sum := by decide
  have hdescent : baseEnd_248524 < baseStart_248524 := by decide
  rcases family_descends (prefixWord ++ tailWord_248524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248562 : List Nat := [3, 2, 1, 3, 1, 3, 2, 1, 4]
def baseStart_248562 : Nat := 118140960795 + 248562 * 2 ^ 59
def prefixEnd_248562 : Nat := 4983230072969 + 3 ^ 40 * 248562 * 2
def baseEnd_248562 : Nat := 113450469727077096650569

theorem tailTrace_248562 : CollatzResearch.WordTrace tailWord_248562 prefixEnd_248562 113450469727077096650569 := by
  unfold tailWord_248562
  simp only [CollatzResearch.WordTrace]
  refine ⟨2266450231377449963752985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6043867283673199903341293 2266450231377449963752985)
  ·
    refine ⟨1699837673533087472814739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2266450231377449963752985 1699837673533087472814739)
    ·
      refine ⟨2549756510299631209222109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1699837673533087472814739 2549756510299631209222109)
      ·
        refine ⟨956158691362361703458291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2549756510299631209222109 956158691362361703458291)
        ·
          refine ⟨1434238037043542555187437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 956158691362361703458291 1434238037043542555187437)
          ·
            refine ⟨537839263891328458195289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1434238037043542555187437 537839263891328458195289)
            ·
              refine ⟨403379447918496343646467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 537839263891328458195289 403379447918496343646467)
              ·
                refine ⟨605069171877744515469701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 403379447918496343646467 605069171877744515469701)
                ·
                  refine ⟨113450469727077096650569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 605069171877744515469701 113450469727077096650569)
                  ·
                    rfl

theorem cell20_248562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_248562 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_248562 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_248562 prefixEnd_248562 := by exact prefixLift 248562
  have htrace : WordTrace (prefixWord ++ tailWord_248562) baseStart_248562 baseEnd_248562 := by
    simpa [prefixWord, tailWord_248562, baseEnd_248562] using wordTrace_append hprefix tailTrace_248562
  have hstable : (prefixWord ++ tailWord_248562).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248562).length < 2 ^ (prefixWord ++ tailWord_248562).sum := by decide
  have hdescent : baseEnd_248562 < baseStart_248562 := by decide
  rcases family_descends (prefixWord ++ tailWord_248562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248597 : List Nat := [1, 3, 2, 1, 2, 2, 1, 1, 7]
def baseStart_248597 : Nat := 118140960795 + 248597 * 2 ^ 59
def prefixEnd_248597 : Nat := 4983230072969 + 3 ^ 40 * 248597 * 2
def baseEnd_248597 : Nat := 113466444680772530483759

theorem tailTrace_248597 : CollatzResearch.WordTrace tailWord_248597 prefixEnd_248597 113466444680772530483759 := by
  unfold tailWord_248597
  simp only [CollatzResearch.WordTrace]
  refine ⟨9067077480383000832536045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6044718320255333888357363 9067077480383000832536045)
  ·
    refine ⟨3400154055143625312201017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9067077480383000832536045 3400154055143625312201017)
    ·
      refine ⟨2550115541357718984150763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3400154055143625312201017 2550115541357718984150763)
      ·
        refine ⟨3825173312036578476226145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2550115541357718984150763 3825173312036578476226145)
        ·
          refine ⟨2868879984027433857169609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3825173312036578476226145 2868879984027433857169609)
          ·
            refine ⟨2151659988020575392877207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2868879984027433857169609 2151659988020575392877207)
            ·
              refine ⟨3227489982030863089315811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2151659988020575392877207 3227489982030863089315811)
              ·
                refine ⟨4841234973046294633973717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3227489982030863089315811 4841234973046294633973717)
                ·
                  refine ⟨113466444680772530483759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4841234973046294633973717 113466444680772530483759)
                  ·
                    rfl

theorem cell20_248597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 7].length) (baseStart_248597 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_248597 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_248597 prefixEnd_248597 := by exact prefixLift 248597
  have htrace : WordTrace (prefixWord ++ tailWord_248597) baseStart_248597 baseEnd_248597 := by
    simpa [prefixWord, tailWord_248597, baseEnd_248597] using wordTrace_append hprefix tailTrace_248597
  have hstable : (prefixWord ++ tailWord_248597).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248597).length < 2 ^ (prefixWord ++ tailWord_248597).sum := by decide
  have hdescent : baseEnd_248597 < baseStart_248597 := by decide
  rcases family_descends (prefixWord ++ tailWord_248597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248690 : List Nat := [3, 2, 1, 2, 1, 1, 4, 3, 3]
def baseStart_248690 : Nat := 118140960795 + 248690 * 2 ^ 59
def prefixEnd_248690 : Nat := 4983230072969 + 3 ^ 40 * 248690 * 2
def baseEnd_248690 : Nat := 113508892414877540383379

theorem tailTrace_248690 : CollatzResearch.WordTrace tailWord_248690 prefixEnd_248690 113508892414877540383379 := by
  unfold tailWord_248690
  simp only [CollatzResearch.WordTrace]
  refine ⟨2267617367261519428917881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6046979646030718477114349 2267617367261519428917881)
  ·
    refine ⟨1700713025446139571688411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2267617367261519428917881 1700713025446139571688411)
    ·
      refine ⟨2551069538169209357532617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1700713025446139571688411 2551069538169209357532617)
      ·
        refine ⟨1913302153626907018149463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2551069538169209357532617 1913302153626907018149463)
        ·
          refine ⟨2869953230440360527224195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1913302153626907018149463 2869953230440360527224195)
          ·
            refine ⟨4304929845660540790836293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2869953230440360527224195 4304929845660540790836293)
            ·
              refine ⟨807174346061351398281805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4304929845660540790836293 807174346061351398281805)
              ·
                refine ⟨302690379773006774355677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 807174346061351398281805 302690379773006774355677)
                ·
                  refine ⟨113508892414877540383379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 302690379773006774355677 113508892414877540383379)
                  ·
                    rfl

theorem cell20_248690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 3, 3].length) (baseStart_248690 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_248690 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_248690 prefixEnd_248690 := by exact prefixLift 248690
  have htrace : WordTrace (prefixWord ++ tailWord_248690) baseStart_248690 baseEnd_248690 := by
    simpa [prefixWord, tailWord_248690, baseEnd_248690] using wordTrace_append hprefix tailTrace_248690
  have hstable : (prefixWord ++ tailWord_248690).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248690).length < 2 ^ (prefixWord ++ tailWord_248690).sum := by decide
  have hdescent : baseEnd_248690 < baseStart_248690 := by decide
  rcases family_descends (prefixWord ++ tailWord_248690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248697 : List Nat := [1, 2, 1, 3, 2, 4, 1, 2, 4]
def baseStart_248697 : Nat := 118140960795 + 248697 * 2 ^ 59
def prefixEnd_248697 : Nat := 4983230072969 + 3 ^ 40 * 248697 * 2
def baseEnd_248697 : Nat := 113512087405616627150017

theorem tailTrace_248697 : CollatzResearch.WordTrace tailWord_248697 prefixEnd_248697 113512087405616627150017 := by
  unfold tailWord_248697
  simp only [CollatzResearch.WordTrace]
  refine ⟨9070724780020717911176345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6047149853347145274117563 9070724780020717911176345)
  ·
    refine ⟨6803043585015538433382259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9070724780020717911176345 6803043585015538433382259)
    ·
      refine ⟨10204565377523307650073389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6803043585015538433382259 10204565377523307650073389)
      ·
        refine ⟨3826712016571240368777521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10204565377523307650073389 3826712016571240368777521)
        ·
          refine ⟨2870034012428430276583141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3826712016571240368777521 2870034012428430276583141)
          ·
            refine ⟨538131377330330676859339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2870034012428430276583141 538131377330330676859339)
            ·
              refine ⟨807197065995496015289009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 538131377330330676859339 807197065995496015289009)
              ·
                refine ⟨605397799496622011466757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 807197065995496015289009 605397799496622011466757)
                ·
                  refine ⟨113512087405616627150017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 605397799496622011466757 113512087405616627150017)
                  ·
                    rfl

theorem cell20_248697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 2, 4].length) (baseStart_248697 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_248697 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_248697 prefixEnd_248697 := by exact prefixLift 248697
  have htrace : WordTrace (prefixWord ++ tailWord_248697) baseStart_248697 baseEnd_248697 := by
    simpa [prefixWord, tailWord_248697, baseEnd_248697] using wordTrace_append hprefix tailTrace_248697
  have hstable : (prefixWord ++ tailWord_248697).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248697).length < 2 ^ (prefixWord ++ tailWord_248697).sum := by decide
  have hdescent : baseEnd_248697 < baseStart_248697 := by decide
  rcases family_descends (prefixWord ++ tailWord_248697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248735 : List Nat := [1, 1, 2, 5, 2, 1, 1, 3, 4]
def baseStart_248735 : Nat := 118140960795 + 248735 * 2 ^ 59
def prefixEnd_248735 : Nat := 4983230072969 + 3 ^ 40 * 248735 * 2
def baseEnd_248735 : Nat := 113529431641057383883195

theorem tailTrace_248735 : CollatzResearch.WordTrace tailWord_248735 prefixEnd_248735 113529431641057383883195 := by
  unfold tailWord_248735
  simp only [CollatzResearch.WordTrace]
  refine ⟨9072110753883050401059659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6048073835922033600706439 9072110753883050401059659)
  ·
    refine ⟨13608166130824575601589489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9072110753883050401059659 13608166130824575601589489)
    ·
      refine ⟨10206124598118431701192117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13608166130824575601589489 10206124598118431701192117)
      ·
        refine ⟨956824181073602971986761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10206124598118431701192117 956824181073602971986761)
        ·
          refine ⟨717618135805202228990071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 956824181073602971986761 717618135805202228990071)
          ·
            refine ⟨1076427203707803343485107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 717618135805202228990071 1076427203707803343485107)
            ·
              refine ⟨1614640805561705015227661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1076427203707803343485107 1614640805561705015227661)
              ·
                refine ⟨605490302085639380710373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1614640805561705015227661 605490302085639380710373)
                ·
                  refine ⟨113529431641057383883195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 605490302085639380710373 113529431641057383883195)
                  ·
                    rfl

theorem cell20_248735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 3, 4].length) (baseStart_248735 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_248735 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_248735 prefixEnd_248735 := by exact prefixLift 248735
  have htrace : WordTrace (prefixWord ++ tailWord_248735) baseStart_248735 baseEnd_248735 := by
    simpa [prefixWord, tailWord_248735, baseEnd_248735] using wordTrace_append hprefix tailTrace_248735
  have hstable : (prefixWord ++ tailWord_248735).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248735).length < 2 ^ (prefixWord ++ tailWord_248735).sum := by decide
  have hdescent : baseEnd_248735 < baseStart_248735 := by decide
  rcases family_descends (prefixWord ++ tailWord_248735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248786 : List Nat := [3, 2, 2, 3, 1, 2, 3, 2, 2]
def baseStart_248786 : Nat := 118140960795 + 248786 * 2 ^ 59
def prefixEnd_248786 : Nat := 4983230072969 + 3 ^ 40 * 248786 * 2
def baseEnd_248786 : Nat := 113552709430727873182987

theorem tailTrace_248786 : CollatzResearch.WordTrace tailWord_248786 prefixEnd_248786 113552709430727873182987 := by
  unfold tailWord_248786
  simp only [CollatzResearch.WordTrace]
  refine ⟨2268492719174571527791553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6049313917798857407444141 2268492719174571527791553)
  ·
    refine ⟨1701369539380928645843665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2268492719174571527791553 1701369539380928645843665)
    ·
      refine ⟨1276027154535696484382749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1701369539380928645843665 1276027154535696484382749)
      ·
        refine ⟨478510182950886181643531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1276027154535696484382749 478510182950886181643531)
        ·
          refine ⟨717765274426329272465297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 478510182950886181643531 717765274426329272465297)
          ·
            refine ⟨538323955819746954348973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 717765274426329272465297 538323955819746954348973)
            ·
              refine ⟨201871483432405107880865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 538323955819746954348973 201871483432405107880865)
              ·
                refine ⟨151403612574303830910649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201871483432405107880865 151403612574303830910649)
                ·
                  refine ⟨113552709430727873182987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 151403612574303830910649 113552709430727873182987)
                  ·
                    rfl

theorem cell20_248786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 3, 2, 2].length) (baseStart_248786 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_248786 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_248786 prefixEnd_248786 := by exact prefixLift 248786
  have htrace : WordTrace (prefixWord ++ tailWord_248786) baseStart_248786 baseEnd_248786 := by
    simpa [prefixWord, tailWord_248786, baseEnd_248786] using wordTrace_append hprefix tailTrace_248786
  have hstable : (prefixWord ++ tailWord_248786).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248786).length < 2 ^ (prefixWord ++ tailWord_248786).sum := by decide
  have hdescent : baseEnd_248786 < baseStart_248786 := by decide
  rcases family_descends (prefixWord ++ tailWord_248786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248797 : List Nat := [1, 4, 3, 1, 2, 2, 2, 5]
def baseStart_248797 : Nat := 118140960795 + 248797 * 2 ^ 59
def prefixEnd_248797 : Nat := 4983230072969 + 3 ^ 40 * 248797 * 2
def baseEnd_248797 : Nat := 37852576710153574605425

theorem tailTrace_248797 : CollatzResearch.WordTrace tailWord_248797 prefixEnd_248797 37852576710153574605425 := by
  unfold tailWord_248797
  simp only [CollatzResearch.WordTrace]
  refine ⟨9074372079658434989816645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6049581386438956659877763 9074372079658434989816645)
  ·
    refine ⟨1701444764935956560590621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9074372079658434989816645 1701444764935956560590621)
    ·
      refine ⟨638041786850983710221483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1701444764935956560590621 638041786850983710221483)
      ·
        refine ⟨957062680276475565332225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 638041786850983710221483 957062680276475565332225)
        ·
          refine ⟨717797010207356673999169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 957062680276475565332225 717797010207356673999169)
          ·
            refine ⟨538347757655517505499377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 717797010207356673999169 538347757655517505499377)
            ·
              refine ⟨403760818241638129124533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 538347757655517505499377 403760818241638129124533)
              ·
                refine ⟨37852576710153574605425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 403760818241638129124533 37852576710153574605425)
                ·
                  rfl

theorem cell20_248797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 5].length) (baseStart_248797 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_248797 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_248797 prefixEnd_248797 := by exact prefixLift 248797
  have htrace : WordTrace (prefixWord ++ tailWord_248797) baseStart_248797 baseEnd_248797 := by
    simpa [prefixWord, tailWord_248797, baseEnd_248797] using wordTrace_append hprefix tailTrace_248797
  have hstable : (prefixWord ++ tailWord_248797).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248797).length < 2 ^ (prefixWord ++ tailWord_248797).sum := by decide
  have hdescent : baseEnd_248797 < baseStart_248797 := by decide
  rcases family_descends (prefixWord ++ tailWord_248797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248842 : List Nat := [3, 1, 2, 2, 3, 1, 1, 4, 3]
def baseStart_248842 : Nat := 118140960795 + 248842 * 2 ^ 59
def prefixEnd_248842 : Nat := 4983230072969 + 3 ^ 40 * 248842 * 2
def baseEnd_248842 : Nat := 113578269356640567316091

theorem tailTrace_248842 : CollatzResearch.WordTrace tailWord_248842 prefixEnd_248842 113578269356640567316091 := by
  unfold tailWord_248842
  simp only [CollatzResearch.WordTrace]
  refine ⟨2269003341123851918801195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6050675576330271783469853 2269003341123851918801195)
  ·
    refine ⟨3403505011685777878201793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2269003341123851918801195 3403505011685777878201793)
    ·
      refine ⟨2552628758764333408651345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3403505011685777878201793 2552628758764333408651345)
      ·
        refine ⟨1914471569073250056488509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2552628758764333408651345 1914471569073250056488509)
        ·
          refine ⟨717926838402468771183191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1914471569073250056488509 717926838402468771183191)
          ·
            refine ⟨1076890257603703156774787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 717926838402468771183191 1076890257603703156774787)
            ·
              refine ⟨1615335386405554735162181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1076890257603703156774787 1615335386405554735162181)
              ·
                refine ⟨302875384951041512842909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1615335386405554735162181 302875384951041512842909)
                ·
                  refine ⟨113578269356640567316091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 302875384951041512842909 113578269356640567316091)
                  ·
                    rfl

theorem cell20_248842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 4, 3].length) (baseStart_248842 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_248842 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_248842 prefixEnd_248842 := by exact prefixLift 248842
  have htrace : WordTrace (prefixWord ++ tailWord_248842) baseStart_248842 baseEnd_248842 := by
    simpa [prefixWord, tailWord_248842, baseEnd_248842] using wordTrace_append hprefix tailTrace_248842
  have hstable : (prefixWord ++ tailWord_248842).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248842).length < 2 ^ (prefixWord ++ tailWord_248842).sum := by decide
  have hdescent : baseEnd_248842 < baseStart_248842 := by decide
  rcases family_descends (prefixWord ++ tailWord_248842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248856 : List Nat := [2, 1, 2, 3, 2, 2, 3, 5]
def baseStart_248856 : Nat := 118140960795 + 248856 * 2 ^ 59
def prefixEnd_248856 : Nat := 4983230072969 + 3 ^ 40 * 248856 * 2
def baseEnd_248856 : Nat := 37861553112706246949789

theorem tailTrace_248856 : CollatzResearch.WordTrace tailWord_248856 prefixEnd_248856 37861553112706246949789 := by
  unfold tailWord_248856
  simp only [CollatzResearch.WordTrace]
  refine ⟨4538261993222344033107211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6051015990963125377476281 4538261993222344033107211)
  ·
    refine ⟨6807392989833516049660817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4538261993222344033107211 6807392989833516049660817)
    ·
      refine ⟨5105544742375137037245613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6807392989833516049660817 5105544742375137037245613)
      ·
        refine ⟨1914579278390676388967105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5105544742375137037245613 1914579278390676388967105)
        ·
          refine ⟨1435934458793007291725329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1914579278390676388967105 1435934458793007291725329)
          ·
            refine ⟨1076950844094755468793997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1435934458793007291725329 1076950844094755468793997)
            ·
              refine ⟨403856566535533300797749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1076950844094755468793997 403856566535533300797749)
              ·
                refine ⟨37861553112706246949789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 403856566535533300797749 37861553112706246949789)
                ·
                  rfl

theorem cell20_248856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 5].length) (baseStart_248856 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_248856 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_248856 prefixEnd_248856 := by exact prefixLift 248856
  have htrace : WordTrace (prefixWord ++ tailWord_248856) baseStart_248856 baseEnd_248856 := by
    simpa [prefixWord, tailWord_248856, baseEnd_248856] using wordTrace_append hprefix tailTrace_248856
  have hstable : (prefixWord ++ tailWord_248856).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248856).length < 2 ^ (prefixWord ++ tailWord_248856).sum := by decide
  have hdescent : baseEnd_248856 < baseStart_248856 := by decide
  rcases family_descends (prefixWord ++ tailWord_248856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_248970 : List Nat := [3, 1, 2, 3, 1, 1, 4, 5]
def baseStart_248970 : Nat := 118140960795 + 248970 * 2 ^ 59
def prefixEnd_248970 : Nat := 4983230072969 + 3 ^ 40 * 248970 * 2
def baseEnd_248970 : Nat := 37878897348147003682967

theorem tailTrace_248970 : CollatzResearch.WordTrace tailWord_248970 prefixEnd_248970 37878897348147003682967 := by
  unfold tailWord_248970
  simp only [CollatzResearch.WordTrace]
  refine ⟨2270170477007921383966091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6053787938687790357242909 2270170477007921383966091)
  ·
    refine ⟨3405255715511882075949137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2270170477007921383966091 3405255715511882075949137)
    ·
      refine ⟨2553941786633911556961853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3405255715511882075949137 2553941786633911556961853)
      ·
        refine ⟨957728169987716833860695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2553941786633911556961853 957728169987716833860695)
        ·
          refine ⟨1436592254981575250791043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 957728169987716833860695 1436592254981575250791043)
          ·
            refine ⟨2154888382472362876186565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1436592254981575250791043 2154888382472362876186565)
            ·
              refine ⟨404041571713568039284981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2154888382472362876186565 404041571713568039284981)
              ·
                refine ⟨37878897348147003682967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 404041571713568039284981 37878897348147003682967)
                ·
                  rfl

theorem cell20_248970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 5].length) (baseStart_248970 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_248970 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_248970 prefixEnd_248970 := by exact prefixLift 248970
  have htrace : WordTrace (prefixWord ++ tailWord_248970) baseStart_248970 baseEnd_248970 := by
    simpa [prefixWord, tailWord_248970, baseEnd_248970] using wordTrace_append hprefix tailTrace_248970
  have hstable : (prefixWord ++ tailWord_248970).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_248970).length < 2 ^ (prefixWord ++ tailWord_248970).sum := by decide
  have hdescent : baseEnd_248970 < baseStart_248970 := by decide
  rcases family_descends (prefixWord ++ tailWord_248970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249025 : List Nat := [1, 2, 6, 1, 1, 1, 3, 5]
def baseStart_249025 : Nat := 118140960795 + 249025 * 2 ^ 59
def prefixEnd_249025 : Nat := 4983230072969 + 3 ^ 40 * 249025 * 2
def baseEnd_249025 : Nat := 37887265181035088071781

theorem tailTrace_249025 : CollatzResearch.WordTrace tailWord_249025 prefixEnd_249025 37887265181035088071781 := by
  unfold tailWord_249025
  simp only [CollatzResearch.WordTrace]
  refine ⟨9082687922832429929116529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6055125281888286619411019 9082687922832429929116529)
  ·
    refine ⟨6812015942124322446837397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9082687922832429929116529 6812015942124322446837397)
    ·
      refine ⟨319313247287077614695503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 6812015942124322446837397 319313247287077614695503)
      ·
        refine ⟨478969870930616422043255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319313247287077614695503 478969870930616422043255)
        ·
          refine ⟨718454806395924633064883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 478969870930616422043255 718454806395924633064883)
          ·
            refine ⟨1077682209593886949597325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 718454806395924633064883 1077682209593886949597325)
            ·
              refine ⟨404130828597707606098997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1077682209593886949597325 404130828597707606098997)
              ·
                refine ⟨37887265181035088071781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 404130828597707606098997 37887265181035088071781)
                ·
                  rfl

theorem cell20_249025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 5].length) (baseStart_249025 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_249025 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_249025 prefixEnd_249025 := by exact prefixLift 249025
  have htrace : WordTrace (prefixWord ++ tailWord_249025) baseStart_249025 baseEnd_249025 := by
    simpa [prefixWord, tailWord_249025, baseEnd_249025] using wordTrace_append hprefix tailTrace_249025
  have hstable : (prefixWord ++ tailWord_249025).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249025).length < 2 ^ (prefixWord ++ tailWord_249025).sum := by decide
  have hdescent : baseEnd_249025 < baseStart_249025 := by decide
  rcases family_descends (prefixWord ++ tailWord_249025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249056 : List Nat := [2, 1, 1, 3, 1, 5, 2, 3, 2]
def baseStart_249056 : Nat := 118140960795 + 249056 * 2 ^ 59
def prefixEnd_249056 : Nat := 4983230072969 + 3 ^ 40 * 249056 * 2
def baseEnd_249056 : Nat := 113675944787806934181883

theorem tailTrace_249056 : CollatzResearch.WordTrace tailWord_249056 prefixEnd_249056 113675944787806934181883 := by
  unfold tailWord_249056
  simp only [CollatzResearch.WordTrace]
  refine ⟨4541909292860061111747511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6055879057146748148996681 4541909292860061111747511)
  ·
    refine ⟨6812863939290091667621267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4541909292860061111747511 6812863939290091667621267)
    ·
      refine ⟨10219295908935137501431901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6812863939290091667621267 10219295908935137501431901)
      ·
        refine ⟨3832235965850676563036963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10219295908935137501431901 3832235965850676563036963)
        ·
          refine ⟨5748353948776014844555445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3832235965850676563036963 5748353948776014844555445)
          ·
            refine ⟨538908182697751391677073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5748353948776014844555445 538908182697751391677073)
            ·
              refine ⟨404181137023313543757805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 538908182697751391677073 404181137023313543757805)
              ·
                refine ⟨151567926383742578909177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 404181137023313543757805 151567926383742578909177)
                ·
                  refine ⟨113675944787806934181883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 151567926383742578909177 113675944787806934181883)
                  ·
                    rfl

theorem cell20_249056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 3, 2].length) (baseStart_249056 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_249056 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_249056 prefixEnd_249056 := by exact prefixLift 249056
  have htrace : WordTrace (prefixWord ++ tailWord_249056) baseStart_249056 baseEnd_249056 := by
    simpa [prefixWord, tailWord_249056, baseEnd_249056] using wordTrace_append hprefix tailTrace_249056
  have hstable : (prefixWord ++ tailWord_249056).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249056).length < 2 ^ (prefixWord ++ tailWord_249056).sum := by decide
  have hdescent : baseEnd_249056 < baseStart_249056 := by decide
  rcases family_descends (prefixWord ++ tailWord_249056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249067 : List Nat := [1, 1, 1, 1, 2, 7, 7]
def baseStart_249067 : Nat := 118140960795 + 249067 * 2 ^ 59
def prefixEnd_249067 : Nat := 4983230072969 + 3 ^ 40 * 249067 * 2
def baseEnd_249067 : Nat := 12631218387504420535019

theorem tailTrace_249067 : CollatzResearch.WordTrace tailWord_249067 prefixEnd_249067 12631218387504420535019 := by
  unfold tailWord_249067
  simp only [CollatzResearch.WordTrace]
  refine ⟨9084219788680271102145455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6056146525786847401430303 9084219788680271102145455)
  ·
    refine ⟨13626329683020406653218183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9084219788680271102145455 13626329683020406653218183)
    ·
      refine ⟨20439494524530609979827275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13626329683020406653218183 20439494524530609979827275)
      ·
        refine ⟨30659241786795914969740913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20439494524530609979827275 30659241786795914969740913)
        ·
          refine ⟨22994431340096936227305685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30659241786795914969740913 22994431340096936227305685)
          ·
            refine ⟨538931984533521942827477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 22994431340096936227305685 538931984533521942827477)
            ·
              refine ⟨12631218387504420535019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 538931984533521942827477 12631218387504420535019)
              ·
                rfl

theorem cell20_249067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 7].length) (baseStart_249067 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_249067 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_249067 prefixEnd_249067 := by exact prefixLift 249067
  have htrace : WordTrace (prefixWord ++ tailWord_249067) baseStart_249067 baseEnd_249067 := by
    simpa [prefixWord, tailWord_249067, baseEnd_249067] using wordTrace_append hprefix tailTrace_249067
  have hstable : (prefixWord ++ tailWord_249067).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249067).length < 2 ^ (prefixWord ++ tailWord_249067).sum := by decide
  have hdescent : baseEnd_249067 < baseStart_249067 := by decide
  rcases family_descends (prefixWord ++ tailWord_249067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249070 : List Nat := [4, 1, 2, 1, 1, 1, 5, 2, 3]
def baseStart_249070 : Nat := 118140960795 + 249070 * 2 ^ 59
def prefixEnd_249070 : Nat := 4983230072969 + 3 ^ 40 * 249070 * 2
def baseEnd_249070 : Nat := 113682334769285107715159

theorem tailTrace_249070 : CollatzResearch.WordTrace tailWord_249070 prefixEnd_249070 113682334769285107715159 := by
  unfold tailWord_249070
  simp only [CollatzResearch.WordTrace]
  refine ⟨1135541150958675326813083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6056219471779601743003109 1135541150958675326813083)
  ·
    refine ⟨1703311726438012990219625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1135541150958675326813083 1703311726438012990219625)
    ·
      refine ⟨1277483794828509742664719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1703311726438012990219625 1277483794828509742664719)
      ·
        refine ⟨1916225692242764613997079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1277483794828509742664719 1916225692242764613997079)
        ·
          refine ⟨2874338538364146920995619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1916225692242764613997079 2874338538364146920995619)
          ·
            refine ⟨4311507807546220381493429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2874338538364146920995619 4311507807546220381493429)
            ·
              refine ⟨404203856957458160765009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4311507807546220381493429 404203856957458160765009)
              ·
                refine ⟨303152892718093620573757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 404203856957458160765009 303152892718093620573757)
                ·
                  refine ⟨113682334769285107715159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 303152892718093620573757 113682334769285107715159)
                  ·
                    rfl

theorem cell20_249070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 2, 3].length) (baseStart_249070 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_249070 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_249070 prefixEnd_249070 := by exact prefixLift 249070
  have htrace : WordTrace (prefixWord ++ tailWord_249070) baseStart_249070 baseEnd_249070 := by
    simpa [prefixWord, tailWord_249070, baseEnd_249070] using wordTrace_append hprefix tailTrace_249070
  have hstable : (prefixWord ++ tailWord_249070).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249070).length < 2 ^ (prefixWord ++ tailWord_249070).sum := by decide
  have hdescent : baseEnd_249070 < baseStart_249070 := by decide
  rcases family_descends (prefixWord ++ tailWord_249070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249105 : List Nat := [1, 2, 2, 1, 1, 4, 3, 6]
def baseStart_249105 : Nat := 118140960795 + 249105 * 2 ^ 59
def prefixEnd_249105 : Nat := 4983230072969 + 3 ^ 40 * 249105 * 2
def baseEnd_249105 : Nat := 37899436574326847182783

theorem tailTrace_249105 : CollatzResearch.WordTrace tailWord_249105 prefixEnd_249105 37899436574326847182783 := by
  unfold tailWord_249105
  simp only [CollatzResearch.WordTrace]
  refine ⟨9085605762542603592028769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6057070508361735728019179 9085605762542603592028769)
  ·
    refine ⟨6814204321906952694021577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9085605762542603592028769 6814204321906952694021577)
    ·
      refine ⟨5110653241430214520516183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6814204321906952694021577 5110653241430214520516183)
      ·
        refine ⟨7665979862145321780774275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5110653241430214520516183 7665979862145321780774275)
        ·
          refine ⟨11498969793217982671161413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7665979862145321780774275 11498969793217982671161413)
          ·
            refine ⟨2156056836228371750842765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11498969793217982671161413 2156056836228371750842765)
            ·
              refine ⟨808521313585639406566037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2156056836228371750842765 808521313585639406566037)
              ·
                refine ⟨37899436574326847182783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 808521313585639406566037 37899436574326847182783)
                ·
                  rfl

theorem cell20_249105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 6].length) (baseStart_249105 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_249105 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_249105 prefixEnd_249105 := by exact prefixLift 249105
  have htrace : WordTrace (prefixWord ++ tailWord_249105) baseStart_249105 baseEnd_249105 := by
    simpa [prefixWord, tailWord_249105, baseEnd_249105] using wordTrace_append hprefix tailTrace_249105
  have hstable : (prefixWord ++ tailWord_249105).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249105).length < 2 ^ (prefixWord ++ tailWord_249105).sum := by decide
  have hdescent : baseEnd_249105 < baseStart_249105 := by decide
  rcases family_descends (prefixWord ++ tailWord_249105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249118 : List Nat := [4, 3, 2, 1, 2, 2, 6]
def baseStart_249118 : Nat := 118140960795 + 249118 * 2 ^ 59
def prefixEnd_249118 : Nat := 4983230072969 + 3 ^ 40 * 249118 * 2
def baseEnd_249118 : Nat := 12633804808578919346107

theorem tailTrace_249118 : CollatzResearch.WordTrace tailWord_249118 prefixEnd_249118 12633804808578919346107 := by
  unfold tailWord_249118
  simp only [CollatzResearch.WordTrace]
  refine ⟨1135759988936938351531501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6057386607663671208168005 1135759988936938351531501)
  ·
    refine ⟨425909995851351881824313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1135759988936938351531501 425909995851351881824313)
    ·
      refine ⟨319432496888513911368235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 425909995851351881824313 319432496888513911368235)
      ·
        refine ⟨479148745332770867052353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319432496888513911368235 479148745332770867052353)
        ·
          refine ⟨359361558999578150289265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 479148745332770867052353 359361558999578150289265)
          ·
            refine ⟨269521169249683612716949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 359361558999578150289265 269521169249683612716949)
            ·
              refine ⟨12633804808578919346107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 269521169249683612716949 12633804808578919346107)
              ·
                rfl

theorem cell20_249118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 6].length) (baseStart_249118 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_249118 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_249118 prefixEnd_249118 := by exact prefixLift 249118
  have htrace : WordTrace (prefixWord ++ tailWord_249118) baseStart_249118 baseEnd_249118 := by
    simpa [prefixWord, tailWord_249118, baseEnd_249118] using wordTrace_append hprefix tailTrace_249118
  have hstable : (prefixWord ++ tailWord_249118).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249118).length < 2 ^ (prefixWord ++ tailWord_249118).sum := by decide
  have hdescent : baseEnd_249118 < baseStart_249118 := by decide
  rcases family_descends (prefixWord ++ tailWord_249118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249142 : List Nat := [5, 1, 2, 3, 1, 1, 1, 3, 3]
def baseStart_249142 : Nat := 118140960795 + 249142 * 2 ^ 59
def prefixEnd_249142 : Nat := 4983230072969 + 3 ^ 40 * 249142 * 2
def baseEnd_249142 : Nat := 113715197531172857314865

theorem tailTrace_249142 : CollatzResearch.WordTrace tailWord_249142 prefixEnd_249142 113715197531172857314865 := by
  unfold tailWord_249142
  simp only [CollatzResearch.WordTrace]
  refine ⟨567934703963034931945355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6057970175605705940750453 567934703963034931945355)
  ·
    refine ⟨851902055944552397918033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 567934703963034931945355 851902055944552397918033)
    ·
      refine ⟨638926541958414298438525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 851902055944552397918033 638926541958414298438525)
      ·
        refine ⟨239597453234405361914447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 638926541958414298438525 239597453234405361914447)
        ·
          refine ⟨359396179851608042871671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239597453234405361914447 359396179851608042871671)
          ·
            refine ⟨539094269777412064307507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359396179851608042871671 539094269777412064307507)
            ·
              refine ⟨808641404666118096461261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 539094269777412064307507 808641404666118096461261)
              ·
                refine ⟨303240526749794286172973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 808641404666118096461261 303240526749794286172973)
                ·
                  refine ⟨113715197531172857314865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 303240526749794286172973 113715197531172857314865)
                  ·
                    rfl

theorem cell20_249142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_249142 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_249142 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_249142 prefixEnd_249142 := by exact prefixLift 249142
  have htrace : WordTrace (prefixWord ++ tailWord_249142) baseStart_249142 baseEnd_249142 := by
    simpa [prefixWord, tailWord_249142, baseEnd_249142] using wordTrace_append hprefix tailTrace_249142
  have hstable : (prefixWord ++ tailWord_249142).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249142).length < 2 ^ (prefixWord ++ tailWord_249142).sum := by decide
  have hdescent : baseEnd_249142 < baseStart_249142 := by decide
  rcases family_descends (prefixWord ++ tailWord_249142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249184 : List Nat := [2, 1, 1, 3, 4, 2, 2, 2, 3]
def baseStart_249184 : Nat := 118140960795 + 249184 * 2 ^ 59
def prefixEnd_249184 : Nat := 4983230072969 + 3 ^ 40 * 249184 * 2
def baseEnd_249184 : Nat := 113734367475607377914693

theorem tailTrace_249184 : CollatzResearch.WordTrace tailWord_249184 prefixEnd_249184 113734367475607377914693 := by
  unfold tailWord_249184
  simp only [CollatzResearch.WordTrace]
  refine ⟨4544243564628200042077303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6058991419504266722769737 4544243564628200042077303)
  ·
    refine ⟨6816365346942300063115955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4544243564628200042077303 6816365346942300063115955)
    ·
      refine ⟨10224548020413450094673933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6816365346942300063115955 10224548020413450094673933)
      ·
        refine ⟨3834205507655043785502725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10224548020413450094673933 3834205507655043785502725)
        ·
          refine ⟨718913532685320709781761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3834205507655043785502725 718913532685320709781761)
          ·
            refine ⟨539185149513990532336321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 718913532685320709781761 539185149513990532336321)
            ·
              refine ⟨404388862135492899252241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 539185149513990532336321 404388862135492899252241)
              ·
                refine ⟨303291646601619674439181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 404388862135492899252241 303291646601619674439181)
                ·
                  refine ⟨113734367475607377914693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 303291646601619674439181 113734367475607377914693)
                  ·
                    rfl

theorem cell20_249184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 2, 3].length) (baseStart_249184 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_249184 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_249184 prefixEnd_249184 := by exact prefixLift 249184
  have htrace : WordTrace (prefixWord ++ tailWord_249184) baseStart_249184 baseEnd_249184 := by
    simpa [prefixWord, tailWord_249184, baseEnd_249184] using wordTrace_append hprefix tailTrace_249184
  have hstable : (prefixWord ++ tailWord_249184).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249184).length < 2 ^ (prefixWord ++ tailWord_249184).sum := by decide
  have hdescent : baseEnd_249184 < baseStart_249184 := by decide
  rcases family_descends (prefixWord ++ tailWord_249184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249187 : List Nat := [1, 1, 1, 5, 2, 4, 2, 2, 2]
def baseStart_249187 : Nat := 118140960795 + 249187 * 2 ^ 59
def prefixEnd_249187 : Nat := 4983230072969 + 3 ^ 40 * 249187 * 2
def baseEnd_249187 : Nat := 113735736757352700814681

theorem tailTrace_249187 : CollatzResearch.WordTrace tailWord_249187 prefixEnd_249187 113735736757352700814681 := by
  unfold tailWord_249187
  simp only [CollatzResearch.WordTrace]
  refine ⟨9088596548245531596513815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6059064365497021064342543 9088596548245531596513815)
  ·
    refine ⟨13632894822368297394770723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9088596548245531596513815 13632894822368297394770723)
    ·
      refine ⟨20449342233552446092156085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13632894822368297394770723 20449342233552446092156085)
      ·
        refine ⟨1917125834395541821139633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20449342233552446092156085 1917125834395541821139633)
        ·
          refine ⟨1437844375796656365854725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1917125834395541821139633 1437844375796656365854725)
          ·
            refine ⟨269595820461873068597761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1437844375796656365854725 269595820461873068597761)
            ·
              refine ⟨202196865346404801448321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 269595820461873068597761 202196865346404801448321)
              ·
                refine ⟨151647649009803601086241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 202196865346404801448321 151647649009803601086241)
                ·
                  refine ⟨113735736757352700814681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 151647649009803601086241 113735736757352700814681)
                  ·
                    rfl

theorem cell20_249187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 2, 2, 2].length) (baseStart_249187 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_249187 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_249187 prefixEnd_249187 := by exact prefixLift 249187
  have htrace : WordTrace (prefixWord ++ tailWord_249187) baseStart_249187 baseEnd_249187 := by
    simpa [prefixWord, tailWord_249187, baseEnd_249187] using wordTrace_append hprefix tailTrace_249187
  have hstable : (prefixWord ++ tailWord_249187).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249187).length < 2 ^ (prefixWord ++ tailWord_249187).sum := by decide
  have hdescent : baseEnd_249187 < baseStart_249187 := by decide
  rcases family_descends (prefixWord ++ tailWord_249187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249194 : List Nat := [3, 1, 3, 3, 3, 1, 1, 5]
def baseStart_249194 : Nat := 118140960795 + 249194 * 2 ^ 59
def prefixEnd_249194 : Nat := 4983230072969 + 3 ^ 40 * 249194 * 2
def baseEnd_249194 : Nat := 37912977249363929193773

theorem tailTrace_249194 : CollatzResearch.WordTrace tailWord_249194 prefixEnd_249194 37912977249363929193773 := by
  unfold tailWord_249194
  simp only [CollatzResearch.WordTrace]
  refine ⟨2272212964805042948004659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6059234572813447861345757 2272212964805042948004659)
  ·
    refine ⟨3408319447207564422006989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2272212964805042948004659 3408319447207564422006989)
    ·
      refine ⟨1278119792702836658252621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3408319447207564422006989 1278119792702836658252621)
      ·
        refine ⟨479294922263563746844733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1278119792702836658252621 479294922263563746844733)
        ·
          refine ⟨179735595848836405066775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 479294922263563746844733 179735595848836405066775)
          ·
            refine ⟨269603393773254607600163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179735595848836405066775 269603393773254607600163)
            ·
              refine ⟨404405090659881911400245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 269603393773254607600163 404405090659881911400245)
              ·
                refine ⟨37912977249363929193773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 404405090659881911400245 37912977249363929193773)
                ·
                  rfl

theorem cell20_249194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 5].length) (baseStart_249194 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_249194 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_249194 prefixEnd_249194 := by exact prefixLift 249194
  have htrace : WordTrace (prefixWord ++ tailWord_249194) baseStart_249194 baseEnd_249194 := by
    simpa [prefixWord, tailWord_249194, baseEnd_249194] using wordTrace_append hprefix tailTrace_249194
  have hstable : (prefixWord ++ tailWord_249194).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249194).length < 2 ^ (prefixWord ++ tailWord_249194).sum := by decide
  have hdescent : baseEnd_249194 < baseStart_249194 := by decide
  rcases family_descends (prefixWord ++ tailWord_249194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249212 : List Nat := [2, 2, 2, 1, 1, 1, 5, 2, 4]
def baseStart_249212 : Nat := 118140960795 + 249212 * 2 ^ 59
def prefixEnd_249212 : Nat := 4983230072969 + 3 ^ 40 * 249212 * 2
def baseEnd_249212 : Nat := 113747147438563724981245

theorem tailTrace_249212 : CollatzResearch.WordTrace tailWord_249212 prefixEnd_249212 113747147438563724981245 := by
  unfold tailWord_249212
  simp only [CollatzResearch.WordTrace]
  refine ⟨4544754186577480433086945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6059672248769973910782593 4544754186577480433086945)
  ·
    refine ⟨3408565639933110324815209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4544754186577480433086945 3408565639933110324815209)
    ·
      refine ⟨2556424229949832743611407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3408565639933110324815209 2556424229949832743611407)
      ·
        refine ⟨3834636344924749115417111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2556424229949832743611407 3834636344924749115417111)
        ·
          refine ⟨5751954517387123673125667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3834636344924749115417111 5751954517387123673125667)
          ·
            refine ⟨8627931776080685509688501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5751954517387123673125667 8627931776080685509688501)
            ·
              refine ⟨808868604007564266533297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8627931776080685509688501 808868604007564266533297)
              ·
                refine ⟨606651453005673199899973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 808868604007564266533297 606651453005673199899973)
                ·
                  refine ⟨113747147438563724981245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 606651453005673199899973 113747147438563724981245)
                  ·
                    rfl

theorem cell20_249212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 2, 4].length) (baseStart_249212 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_249212 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_249212 prefixEnd_249212 := by exact prefixLift 249212
  have htrace : WordTrace (prefixWord ++ tailWord_249212) baseStart_249212 baseEnd_249212 := by
    simpa [prefixWord, tailWord_249212, baseEnd_249212] using wordTrace_append hprefix tailTrace_249212
  have hstable : (prefixWord ++ tailWord_249212).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249212).length < 2 ^ (prefixWord ++ tailWord_249212).sum := by decide
  have hdescent : baseEnd_249212 < baseStart_249212 := by decide
  rcases family_descends (prefixWord ++ tailWord_249212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249236 : List Nat := [2, 4, 2, 1, 2, 2, 7]
def baseStart_249236 : Nat := 118140960795 + 249236 * 2 ^ 59
def prefixEnd_249236 : Nat := 4983230072969 + 3 ^ 40 * 249236 * 2
def baseEnd_249236 : Nat := 12639789076947367575683

theorem tailTrace_249236 : CollatzResearch.WordTrace tailWord_249236 prefixEnd_249236 12639789076947367575683 := by
  unfold tailWord_249236
  simp only [CollatzResearch.WordTrace]
  refine ⟨4545191862534006482523781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6060255816712008643365041 4545191862534006482523781)
  ·
    refine ⟨852223474225126215473209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4545191862534006482523781 852223474225126215473209)
    ·
      refine ⟨639167605668844661604907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 852223474225126215473209 639167605668844661604907)
      ·
        refine ⟨958751408503266992407361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 639167605668844661604907 958751408503266992407361)
        ·
          refine ⟨719063556377450244305521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 958751408503266992407361 719063556377450244305521)
          ·
            refine ⟨539297667283087683229141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 719063556377450244305521 539297667283087683229141)
            ·
              refine ⟨12639789076947367575683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 539297667283087683229141 12639789076947367575683)
              ·
                rfl

theorem cell20_249236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 7].length) (baseStart_249236 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_249236 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_249236 prefixEnd_249236 := by exact prefixLift 249236
  have htrace : WordTrace (prefixWord ++ tailWord_249236) baseStart_249236 baseEnd_249236 := by
    simpa [prefixWord, tailWord_249236, baseEnd_249236] using wordTrace_append hprefix tailTrace_249236
  have hstable : (prefixWord ++ tailWord_249236).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249236).length < 2 ^ (prefixWord ++ tailWord_249236).sum := by decide
  have hdescent : baseEnd_249236 < baseStart_249236 := by decide
  rcases family_descends (prefixWord ++ tailWord_249236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249256 : List Nat := [2, 1, 6, 1, 2, 1, 3, 1, 3]
def baseStart_249256 : Nat := 118140960795 + 249256 * 2 ^ 59
def prefixEnd_249256 : Nat := 4983230072969 + 3 ^ 40 * 249256 * 2
def baseEnd_249256 : Nat := 113767230237495127514399

theorem tailTrace_249256 : CollatzResearch.WordTrace tailWord_249256 prefixEnd_249256 113767230237495127514399 := by
  unfold tailWord_249256
  simp only [CollatzResearch.WordTrace]
  refine ⟨4545556592497778190387811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6060742123330370920517081 4545556592497778190387811)
  ·
    refine ⟨6818334888746667285581717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4545556592497778190387811 6818334888746667285581717)
    ·
      refine ⟨319609447910000029011643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 6818334888746667285581717 319609447910000029011643)
      ·
        refine ⟨479414171865000043517465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319609447910000029011643 479414171865000043517465)
        ·
          refine ⟨359560628898750032638099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 479414171865000043517465 359560628898750032638099)
          ·
            refine ⟨539340943348125048957149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359560628898750032638099 539340943348125048957149)
            ·
              refine ⟨202252853755546893358931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 539340943348125048957149 202252853755546893358931)
              ·
                refine ⟨303379280633320340038397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202252853755546893358931 303379280633320340038397)
                ·
                  refine ⟨113767230237495127514399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 303379280633320340038397 113767230237495127514399)
                  ·
                    rfl

theorem cell20_249256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 3, 1, 3].length) (baseStart_249256 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_249256 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_249256 prefixEnd_249256 := by exact prefixLift 249256
  have htrace : WordTrace (prefixWord ++ tailWord_249256) baseStart_249256 baseEnd_249256 := by
    simpa [prefixWord, tailWord_249256, baseEnd_249256] using wordTrace_append hprefix tailTrace_249256
  have hstable : (prefixWord ++ tailWord_249256).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249256).length < 2 ^ (prefixWord ++ tailWord_249256).sum := by decide
  have hdescent : baseEnd_249256 < baseStart_249256 := by decide
  rcases family_descends (prefixWord ++ tailWord_249256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249305 : List Nat := [1, 2, 1, 2, 4, 4, 1, 1, 4]
def baseStart_249305 : Nat := 118140960795 + 249305 * 2 ^ 59
def prefixEnd_249305 : Nat := 4983230072969 + 3 ^ 40 * 249305 * 2
def baseEnd_249305 : Nat := 113789595172668734880865

theorem tailTrace_249305 : CollatzResearch.WordTrace tailWord_249305 prefixEnd_249305 113789595172668734880865 := by
  unfold tailWord_249305
  simp only [CollatzResearch.WordTrace]
  refine ⟨9092900361818037749309369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6061933574545358499539579 9092900361818037749309369)
  ·
    refine ⟨6819675271363528311982027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9092900361818037749309369 6819675271363528311982027)
    ·
      refine ⟨10229512907045292467973041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6819675271363528311982027 10229512907045292467973041)
      ·
        refine ⟨7672134680283969350979781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10229512907045292467973041 7672134680283969350979781)
        ·
          refine ⟨1438525252553244253308709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7672134680283969350979781 1438525252553244253308709)
          ·
            refine ⟨269723484853733297495383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1438525252553244253308709 269723484853733297495383)
            ·
              refine ⟨404585227280599946243075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 269723484853733297495383 404585227280599946243075)
              ·
                refine ⟨606877840920899919364613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 404585227280599946243075 606877840920899919364613)
                ·
                  refine ⟨113789595172668734880865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 606877840920899919364613 113789595172668734880865)
                  ·
                    rfl

theorem cell20_249305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 1, 4].length) (baseStart_249305 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_249305 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_249305 prefixEnd_249305 := by exact prefixLift 249305
  have htrace : WordTrace (prefixWord ++ tailWord_249305) baseStart_249305 baseEnd_249305 := by
    simpa [prefixWord, tailWord_249305, baseEnd_249305] using wordTrace_append hprefix tailTrace_249305
  have hstable : (prefixWord ++ tailWord_249305).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249305).length < 2 ^ (prefixWord ++ tailWord_249305).sum := by decide
  have hdescent : baseEnd_249305 < baseStart_249305 := by decide
  rcases family_descends (prefixWord ++ tailWord_249305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249315 : List Nat := [1, 1, 1, 6, 2, 3, 2, 1, 3]
def baseStart_249315 : Nat := 118140960795 + 249315 * 2 ^ 59
def prefixEnd_249315 : Nat := 4983230072969 + 3 ^ 40 * 249315 * 2
def baseEnd_249315 : Nat := 113794159445153144547491

theorem tailTrace_249315 : CollatzResearch.WordTrace tailWord_249315 prefixEnd_249315 113794159445153144547491 := by
  unfold tailWord_249315
  simp only [CollatzResearch.WordTrace]
  refine ⟨9093265091781809457173399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6062176727854539638115599 9093265091781809457173399)
  ·
    refine ⟨13639897637672714185760099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9093265091781809457173399 13639897637672714185760099)
    ·
      refine ⟨20459846456509071278640149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13639897637672714185760099 20459846456509071278640149)
      ·
        refine ⟨959055302648862716186257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 20459846456509071278640149 959055302648862716186257)
        ·
          refine ⟨719291476986647037139693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 959055302648862716186257 719291476986647037139693)
          ·
            refine ⟨269734303869992638927385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 719291476986647037139693 269734303869992638927385)
            ·
              refine ⟨202300727902494479195539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 269734303869992638927385 202300727902494479195539)
              ·
                refine ⟨303451091853741718793309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202300727902494479195539 303451091853741718793309)
                ·
                  refine ⟨113794159445153144547491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 303451091853741718793309 113794159445153144547491)
                  ·
                    rfl

theorem cell20_249315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 2, 1, 3].length) (baseStart_249315 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_249315 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_249315 prefixEnd_249315 := by exact prefixLift 249315
  have htrace : WordTrace (prefixWord ++ tailWord_249315) baseStart_249315 baseEnd_249315 := by
    simpa [prefixWord, tailWord_249315, baseEnd_249315] using wordTrace_append hprefix tailTrace_249315
  have hstable : (prefixWord ++ tailWord_249315).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249315).length < 2 ^ (prefixWord ++ tailWord_249315).sum := by decide
  have hdescent : baseEnd_249315 < baseStart_249315 := by decide
  rcases family_descends (prefixWord ++ tailWord_249315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249326 : List Nat := [4, 1, 2, 1, 2, 1, 2, 1, 6]
def baseStart_249326 : Nat := 118140960795 + 249326 * 2 ^ 59
def prefixEnd_249326 : Nat := 4983230072969 + 3 ^ 40 * 249326 * 2
def baseEnd_249326 : Nat := 113799180144885995180779

theorem tailTrace_249326 : CollatzResearch.WordTrace tailWord_249326 prefixEnd_249326 113799180144885995180779 := by
  unfold tailWord_249326
  simp only [CollatzResearch.WordTrace]
  refine ⟨1136708286842744791977979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6062444196494638890549221 1136708286842744791977979)
  ·
    refine ⟨1705062430264117187966969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1136708286842744791977979 1705062430264117187966969)
    ·
      refine ⟨1278796822698087890975227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1705062430264117187966969 1278796822698087890975227)
      ·
        refine ⟨1918195234047131836462841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1278796822698087890975227 1918195234047131836462841)
        ·
          refine ⟨1438646425535348877347131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1918195234047131836462841 1438646425535348877347131)
          ·
            refine ⟨2157969638303023316020697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1438646425535348877347131 2157969638303023316020697)
            ·
              refine ⟨1618477228727267487015523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2157969638303023316020697 1618477228727267487015523)
              ·
                refine ⟨2427715843090901230523285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1618477228727267487015523 2427715843090901230523285)
                ·
                  refine ⟨113799180144885995180779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2427715843090901230523285 113799180144885995180779)
                  ·
                    rfl

theorem cell20_249326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_249326 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_249326 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_249326 prefixEnd_249326 := by exact prefixLift 249326
  have htrace : WordTrace (prefixWord ++ tailWord_249326) baseStart_249326 baseEnd_249326 := by
    simpa [prefixWord, tailWord_249326, baseEnd_249326] using wordTrace_append hprefix tailTrace_249326
  have hstable : (prefixWord ++ tailWord_249326).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249326).length < 2 ^ (prefixWord ++ tailWord_249326).sum := by decide
  have hdescent : baseEnd_249326 < baseStart_249326 := by decide
  rcases family_descends (prefixWord ++ tailWord_249326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249340 : List Nat := [2, 2, 2, 1, 2, 1, 2, 1, 7]
def baseStart_249340 : Nat := 118140960795 + 249340 * 2 ^ 59
def prefixEnd_249340 : Nat := 4983230072969 + 3 ^ 40 * 249340 * 2
def baseEnd_249340 : Nat := 113805570126364168714055

theorem tailTrace_249340 : CollatzResearch.WordTrace tailWord_249340 prefixEnd_249340 113805570126364168714055 := by
  unfold tailWord_249340
  simp only [CollatzResearch.WordTrace]
  refine ⟨4547088458345619363416737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6062784611127492484555649 4547088458345619363416737)
  ·
    refine ⟨3410316343759214522562553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4547088458345619363416737 3410316343759214522562553)
    ·
      refine ⟨2557737257819410891921915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3410316343759214522562553 2557737257819410891921915)
      ·
        refine ⟨3836605886729116337882873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2557737257819410891921915 3836605886729116337882873)
        ·
          refine ⟨2877454415046837253412155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3836605886729116337882873 2877454415046837253412155)
          ·
            refine ⟨4316181622570255880118233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2877454415046837253412155 4316181622570255880118233)
            ·
              refine ⟨3237136216927691910088675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4316181622570255880118233 3237136216927691910088675)
              ·
                refine ⟨4855704325391537865133013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3237136216927691910088675 4855704325391537865133013)
                ·
                  refine ⟨113805570126364168714055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4855704325391537865133013 113805570126364168714055)
                  ·
                    rfl

theorem cell20_249340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 7].length) (baseStart_249340 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_249340 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_249340 prefixEnd_249340 := by exact prefixLift 249340
  have htrace : WordTrace (prefixWord ++ tailWord_249340) baseStart_249340 baseEnd_249340 := by
    simpa [prefixWord, tailWord_249340, baseEnd_249340] using wordTrace_append hprefix tailTrace_249340
  have hstable : (prefixWord ++ tailWord_249340).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249340).length < 2 ^ (prefixWord ++ tailWord_249340).sum := by decide
  have hdescent : baseEnd_249340 < baseStart_249340 := by decide
  rcases family_descends (prefixWord ++ tailWord_249340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249347 : List Nat := [1, 1, 1, 3, 2, 1, 2, 1, 8]
def baseStart_249347 : Nat := 118140960795 + 249347 * 2 ^ 59
def prefixEnd_249347 : Nat := 4983230072969 + 3 ^ 40 * 249347 * 2
def baseEnd_249347 : Nat := 113808765117103255480693

theorem tailTrace_249347 : CollatzResearch.WordTrace tailWord_249347 prefixEnd_249347 113808765117103255480693 := by
  unfold tailWord_249347
  simp only [CollatzResearch.WordTrace]
  refine ⟨9094432227665878922338295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6062954818443919281558863 9094432227665878922338295)
  ·
    refine ⟨13641648341498818383507443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9094432227665878922338295 13641648341498818383507443)
    ·
      refine ⟨20462472512248227575261165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13641648341498818383507443 20462472512248227575261165)
      ·
        refine ⟨7673427192093085340722937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20462472512248227575261165 7673427192093085340722937)
        ·
          refine ⟨5755070394069814005542203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7673427192093085340722937 5755070394069814005542203)
          ·
            refine ⟨8632605591104721008313305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5755070394069814005542203 8632605591104721008313305)
            ·
              refine ⟨6474454193328540756234979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8632605591104721008313305 6474454193328540756234979)
              ·
                refine ⟨9711681289992811134352469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6474454193328540756234979 9711681289992811134352469)
                ·
                  refine ⟨113808765117103255480693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9711681289992811134352469 113808765117103255480693)
                  ·
                    rfl

theorem cell20_249347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 8].length) (baseStart_249347 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_249347 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_249347 prefixEnd_249347 := by exact prefixLift 249347
  have htrace : WordTrace (prefixWord ++ tailWord_249347) baseStart_249347 baseEnd_249347 := by
    simpa [prefixWord, tailWord_249347, baseEnd_249347] using wordTrace_append hprefix tailTrace_249347
  have hstable : (prefixWord ++ tailWord_249347).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249347).length < 2 ^ (prefixWord ++ tailWord_249347).sum := by decide
  have hdescent : baseEnd_249347 < baseStart_249347 := by decide
  rcases family_descends (prefixWord ++ tailWord_249347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249356 : List Nat := [2, 2, 1, 2, 6, 1, 2, 2, 2]
def baseStart_249356 : Nat := 118140960795 + 249356 * 2 ^ 59
def prefixEnd_249356 : Nat := 4983230072969 + 3 ^ 40 * 249356 * 2
def baseEnd_249356 : Nat := 113812872962339224180657

theorem tailTrace_249356 : CollatzResearch.WordTrace tailWord_249356 prefixEnd_249356 113812872962339224180657 := by
  unfold tailWord_249356
  simp only [CollatzResearch.WordTrace]
  refine ⟨4547380242316636729707961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6063173656422182306277281 4547380242316636729707961)
  ·
    refine ⟨3410535181737477547280971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4547380242316636729707961 3410535181737477547280971)
    ·
      refine ⟨5115802772606216320921457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3410535181737477547280971 5115802772606216320921457)
      ·
        refine ⟨3836852079454662240691093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5115802772606216320921457 3836852079454662240691093)
        ·
          refine ⟨179852441224437292532395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3836852079454662240691093 179852441224437292532395)
          ·
            refine ⟨269778661836655938798593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179852441224437292532395 269778661836655938798593)
            ·
              refine ⟨202333996377491954098945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 269778661836655938798593 202333996377491954098945)
              ·
                refine ⟨151750497283118965574209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 202333996377491954098945 151750497283118965574209)
                ·
                  refine ⟨113812872962339224180657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 151750497283118965574209 113812872962339224180657)
                  ·
                    rfl

theorem cell20_249356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 2, 2, 2].length) (baseStart_249356 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_249356 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_249356 prefixEnd_249356 := by exact prefixLift 249356
  have htrace : WordTrace (prefixWord ++ tailWord_249356) baseStart_249356 baseEnd_249356 := by
    simpa [prefixWord, tailWord_249356, baseEnd_249356] using wordTrace_append hprefix tailTrace_249356
  have hstable : (prefixWord ++ tailWord_249356).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249356).length < 2 ^ (prefixWord ++ tailWord_249356).sum := by decide
  have hdescent : baseEnd_249356 < baseStart_249356 := by decide
  rcases family_descends (prefixWord ++ tailWord_249356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249409 : List Nat := [1, 2, 5, 1, 1, 1, 9]
def baseStart_249409 : Nat := 118140960795 + 249409 * 2 ^ 59
def prefixEnd_249409 : Nat := 4983230072969 + 3 ^ 40 * 249409 * 2
def baseEnd_249409 : Nat := 12648562622945177268197

theorem tailTrace_249409 : CollatzResearch.WordTrace tailWord_249409 prefixEnd_249409 12648562622945177268197 := by
  unfold tailWord_249409
  simp only [CollatzResearch.WordTrace]
  refine ⟨9096693553441263511095281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6064462368960842340730187 9096693553441263511095281)
  ·
    refine ⟨6822520165080947633321461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9096693553441263511095281 6822520165080947633321461)
    ·
      refine ⟨639611265476338840623887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6822520165080947633321461 639611265476338840623887)
      ·
        refine ⟨959416898214508260935831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 639611265476338840623887 959416898214508260935831)
        ·
          refine ⟨1439125347321762391403747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 959416898214508260935831 1439125347321762391403747)
          ·
            refine ⟨2158688020982643587105621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1439125347321762391403747 2158688020982643587105621)
            ·
              refine ⟨12648562622945177268197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2158688020982643587105621 12648562622945177268197)
              ·
                rfl

theorem cell20_249409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 9].length) (baseStart_249409 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_249409 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_249409 prefixEnd_249409 := by exact prefixLift 249409
  have htrace : WordTrace (prefixWord ++ tailWord_249409) baseStart_249409 baseEnd_249409 := by
    simpa [prefixWord, tailWord_249409, baseEnd_249409] using wordTrace_append hprefix tailTrace_249409
  have hstable : (prefixWord ++ tailWord_249409).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249409).length < 2 ^ (prefixWord ++ tailWord_249409).sum := by decide
  have hdescent : baseEnd_249409 < baseStart_249409 := by decide
  rcases family_descends (prefixWord ++ tailWord_249409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249453 : List Nat := [1, 5, 1, 1, 4, 2, 1, 3, 2]
def baseStart_249453 : Nat := 118140960795 + 249453 * 2 ^ 59
def prefixEnd_249453 : Nat := 4983230072969 + 3 ^ 40 * 249453 * 2
def baseEnd_249453 : Nat := 113857146405437997946927

theorem tailTrace_249453 : CollatzResearch.WordTrace tailWord_249453 prefixEnd_249453 113857146405437997946927 := by
  unfold tailWord_249453
  simp only [CollatzResearch.WordTrace]
  refine ⟨9098298365281859025697013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6065532243521239350464675 9098298365281859025697013)
  ·
    refine ⟨852965471745174283659095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9098298365281859025697013 852965471745174283659095)
    ·
      refine ⟨1279448207617761425488643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 852965471745174283659095 1279448207617761425488643)
      ·
        refine ⟨1919172311426642138232965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1279448207617761425488643 1919172311426642138232965)
        ·
          refine ⟨359844808392495400918681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1919172311426642138232965 359844808392495400918681)
          ·
            refine ⟨269883606294371550689011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 359844808392495400918681 269883606294371550689011)
            ·
              refine ⟨404825409441557326033517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 269883606294371550689011 404825409441557326033517)
              ·
                refine ⟨151809528540583997262569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 404825409441557326033517 151809528540583997262569)
                ·
                  refine ⟨113857146405437997946927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 151809528540583997262569 113857146405437997946927)
                  ·
                    rfl

theorem cell20_249453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 3, 2].length) (baseStart_249453 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_249453 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_249453 prefixEnd_249453 := by exact prefixLift 249453
  have htrace : WordTrace (prefixWord ++ tailWord_249453) baseStart_249453 baseEnd_249453 := by
    simpa [prefixWord, tailWord_249453, baseEnd_249453] using wordTrace_append hprefix tailTrace_249453
  have hstable : (prefixWord ++ tailWord_249453).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249453).length < 2 ^ (prefixWord ++ tailWord_249453).sum := by decide
  have hdescent : baseEnd_249453 < baseStart_249453 := by decide
  rcases family_descends (prefixWord ++ tailWord_249453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249502 : List Nat := [4, 3, 1, 1, 1, 2, 2, 6]
def baseStart_249502 : Nat := 118140960795 + 249502 * 2 ^ 59
def prefixEnd_249502 : Nat := 4983230072969 + 3 ^ 40 * 249502 * 2
def baseEnd_249502 : Nat := 37959837113537201771131

theorem tailTrace_249502 : CollatzResearch.WordTrace tailWord_249502 prefixEnd_249502 37959837113537201771131 := by
  unfold tailWord_249502
  simp only [CollatzResearch.WordTrace]
  refine ⟨1137510692763042549278845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6066723694736226929487173 1137510692763042549278845)
  ·
    refine ⟨426566509786140955979567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1137510692763042549278845 426566509786140955979567)
    ·
      refine ⟨639849764679211433969351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426566509786140955979567 639849764679211433969351)
      ·
        refine ⟨959774647018817150954027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 639849764679211433969351 959774647018817150954027)
        ·
          refine ⟨1439661970528225726431041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 959774647018817150954027 1439661970528225726431041)
          ·
            refine ⟨1079746477896169294823281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1439661970528225726431041 1079746477896169294823281)
            ·
              refine ⟨809809858422126971117461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1079746477896169294823281 809809858422126971117461)
              ·
                refine ⟨37959837113537201771131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 809809858422126971117461 37959837113537201771131)
                ·
                  rfl

theorem cell20_249502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 6].length) (baseStart_249502 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_249502 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_249502 prefixEnd_249502 := by exact prefixLift 249502
  have htrace : WordTrace (prefixWord ++ tailWord_249502) baseStart_249502 baseEnd_249502 := by
    simpa [prefixWord, tailWord_249502, baseEnd_249502] using wordTrace_append hprefix tailTrace_249502
  have hstable : (prefixWord ++ tailWord_249502).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249502).length < 2 ^ (prefixWord ++ tailWord_249502).sum := by decide
  have hdescent : baseEnd_249502 < baseStart_249502 := by decide
  rcases family_descends (prefixWord ++ tailWord_249502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249533 : List Nat := [1, 4, 1, 2, 1, 2, 3, 4, 2]
def baseStart_249533 : Nat := 118140960795 + 249533 * 2 ^ 59
def prefixEnd_249533 : Nat := 4983230072969 + 3 ^ 40 * 249533 * 2
def baseEnd_249533 : Nat := 113893660585313275279933

theorem tailTrace_249533 : CollatzResearch.WordTrace tailWord_249533 prefixEnd_249533 113893660585313275279933 := by
  unfold tailWord_249533
  simp only [CollatzResearch.WordTrace]
  refine ⟨9101216204992032688609253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6067477469994688459072835 9101216204992032688609253)
  ·
    refine ⟨1706478038436006129114235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9101216204992032688609253 1706478038436006129114235)
    ·
      refine ⟨2559717057654009193671353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1706478038436006129114235 2559717057654009193671353)
      ·
        refine ⟨1919787793240506895253515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2559717057654009193671353 1919787793240506895253515)
        ·
          refine ⟨2879681689860760342880273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1919787793240506895253515 2879681689860760342880273)
          ·
            refine ⟨2159761267395570257160205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2879681689860760342880273 2159761267395570257160205)
            ·
              refine ⟨809910475273338846435077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2159761267395570257160205 809910475273338846435077)
              ·
                refine ⟨151858214113751033706577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 809910475273338846435077 151858214113751033706577)
                ·
                  refine ⟨113893660585313275279933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 151858214113751033706577 113893660585313275279933)
                  ·
                    rfl

theorem cell20_249533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 4, 2].length) (baseStart_249533 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_249533 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_249533 prefixEnd_249533 := by exact prefixLift 249533
  have htrace : WordTrace (prefixWord ++ tailWord_249533) baseStart_249533 baseEnd_249533 := by
    simpa [prefixWord, tailWord_249533, baseEnd_249533] using wordTrace_append hprefix tailTrace_249533
  have hstable : (prefixWord ++ tailWord_249533).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249533).length < 2 ^ (prefixWord ++ tailWord_249533).sum := by decide
  have hdescent : baseEnd_249533 < baseStart_249533 := by decide
  rcases family_descends (prefixWord ++ tailWord_249533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249554 : List Nat := [3, 2, 2, 2, 2, 1, 1, 1, 6]
def baseStart_249554 : Nat := 118140960795 + 249554 * 2 ^ 59
def prefixEnd_249554 : Nat := 4983230072969 + 3 ^ 40 * 249554 * 2
def baseEnd_249554 : Nat := 113903245557530535579847

theorem tailTrace_249554 : CollatzResearch.WordTrace tailWord_249554 prefixEnd_249554 113903245557530535579847 := by
  unfold tailWord_249554
  simp only [CollatzResearch.WordTrace]
  refine ⟨2275495534478988318780929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6067988091943968850082477 2275495534478988318780929)
  ·
    refine ⟨1706621650859241239085697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2275495534478988318780929 1706621650859241239085697)
    ·
      refine ⟨1279966238144430929314273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1706621650859241239085697 1279966238144430929314273)
      ·
        refine ⟨959974678608323196985705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1279966238144430929314273 959974678608323196985705)
        ·
          refine ⟨719981008956242397739279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 959974678608323196985705 719981008956242397739279)
          ·
            refine ⟨1079971513434363596608919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 719981008956242397739279 1079971513434363596608919)
            ·
              refine ⟨1619957270151545394913379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1079971513434363596608919 1619957270151545394913379)
              ·
                refine ⟨2429935905227318092370069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1619957270151545394913379 2429935905227318092370069)
                ·
                  refine ⟨113903245557530535579847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2429935905227318092370069 113903245557530535579847)
                  ·
                    rfl

theorem cell20_249554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_249554 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_249554 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_249554 prefixEnd_249554 := by exact prefixLift 249554
  have htrace : WordTrace (prefixWord ++ tailWord_249554) baseStart_249554 baseEnd_249554 := by
    simpa [prefixWord, tailWord_249554, baseEnd_249554] using wordTrace_append hprefix tailTrace_249554
  have hstable : (prefixWord ++ tailWord_249554).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249554).length < 2 ^ (prefixWord ++ tailWord_249554).sum := by decide
  have hdescent : baseEnd_249554 < baseStart_249554 := by decide
  rcases family_descends (prefixWord ++ tailWord_249554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249585 : List Nat := [1, 2, 2, 2, 2, 3, 3, 2, 3]
def baseStart_249585 : Nat := 118140960795 + 249585 * 2 ^ 59
def prefixEnd_249585 : Nat := 4983230072969 + 3 ^ 40 * 249585 * 2
def baseEnd_249585 : Nat := 113917394802232205546387

theorem tailTrace_249585 : CollatzResearch.WordTrace tailWord_249585 prefixEnd_249585 113917394802232205546387 := by
  unfold tailWord_249585
  simp only [CollatzResearch.WordTrace]
  refine ⟨9103112800803645569502209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6068741867202430379668139 9103112800803645569502209)
  ·
    refine ⟨6827334600602734177126657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9103112800803645569502209 6827334600602734177126657)
    ·
      refine ⟨5120500950452050632844993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6827334600602734177126657 5120500950452050632844993)
      ·
        refine ⟨3840375712839037974633745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5120500950452050632844993 3840375712839037974633745)
        ·
          refine ⟨2880281784629278480975309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3840375712839037974633745 2880281784629278480975309)
          ·
            refine ⟨1080105669235979430365741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2880281784629278480975309 1080105669235979430365741)
            ·
              refine ⟨405039625963492286387153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1080105669235979430365741 405039625963492286387153)
              ·
                refine ⟨303779719472619214790365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 405039625963492286387153 303779719472619214790365)
                ·
                  refine ⟨113917394802232205546387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 303779719472619214790365 113917394802232205546387)
                  ·
                    rfl

theorem cell20_249585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 2, 3].length) (baseStart_249585 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_249585 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_249585 prefixEnd_249585 := by exact prefixLift 249585
  have htrace : WordTrace (prefixWord ++ tailWord_249585) baseStart_249585 baseEnd_249585 := by
    simpa [prefixWord, tailWord_249585, baseEnd_249585] using wordTrace_append hprefix tailTrace_249585
  have hstable : (prefixWord ++ tailWord_249585).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249585).length < 2 ^ (prefixWord ++ tailWord_249585).sum := by decide
  have hdescent : baseEnd_249585 < baseStart_249585 := by decide
  rcases family_descends (prefixWord ++ tailWord_249585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_249588 : List Nat := [2, 6, 1, 1, 1, 1, 1, 3, 4]
def baseStart_249588 : Nat := 118140960795 + 249588 * 2 ^ 59
def prefixEnd_249588 : Nat := 4983230072969 + 3 ^ 40 * 249588 * 2
def baseEnd_249588 : Nat := 113918764083977528446375

theorem tailTrace_249588 : CollatzResearch.WordTrace tailWord_249588 prefixEnd_249588 113918764083977528446375 := by
  unfold tailWord_249588
  simp only [CollatzResearch.WordTrace]
  refine ⟨4551611109896388540930709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6068814813195184721240945 4551611109896388540930709)
  ·
    refine ⟨213356770776393212856127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4551611109896388540930709 213356770776393212856127)
    ·
      refine ⟨320035156164589819284191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213356770776393212856127 320035156164589819284191)
      ·
        refine ⟨480052734246884728926287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320035156164589819284191 480052734246884728926287)
        ·
          refine ⟨720079101370327093389431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 480052734246884728926287 720079101370327093389431)
          ·
            refine ⟨1080118652055490640084147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 720079101370327093389431 1080118652055490640084147)
            ·
              refine ⟨1620177978083235960126221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1080118652055490640084147 1620177978083235960126221)
              ·
                refine ⟨607566741781213485047333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1620177978083235960126221 607566741781213485047333)
                ·
                  refine ⟨113918764083977528446375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 607566741781213485047333 113918764083977528446375)
                  ·
                    rfl

theorem cell20_249588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_249588 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_249588 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_249588 prefixEnd_249588 := by exact prefixLift 249588
  have htrace : WordTrace (prefixWord ++ tailWord_249588) baseStart_249588 baseEnd_249588 := by
    simpa [prefixWord, tailWord_249588, baseEnd_249588] using wordTrace_append hprefix tailTrace_249588
  have hstable : (prefixWord ++ tailWord_249588).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_249588).length < 2 ^ (prefixWord ++ tailWord_249588).sum := by decide
  have hdescent : baseEnd_249588 < baseStart_249588 := by decide
  rcases family_descends (prefixWord ++ tailWord_249588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
