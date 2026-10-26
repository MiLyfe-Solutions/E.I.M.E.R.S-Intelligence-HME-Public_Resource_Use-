import V185TrunkScan22Chunk088

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_798638 : List Nat := [4, 1, 5, 1, 2, 1, 1, 2, 1, 4]
def baseStart_798638 : Nat := 118140960795 + 798638 * 2 ^ 59
def prefixEnd_798638 : Nat := 4983230072969 + 3 ^ 40 * 798638 * 2
def baseEnd_798638 : Nat := 273390108630367705901425

theorem tailTrace_798638 : CollatzResearch.WordTrace tailWord_798638 prefixEnd_798638 273390108630367705901425 := by
  unfold tailWord_798638
  simp only [CollatzResearch.WordTrace]
  refine ⟨3641090110084799669553571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19419147253785598237619045 3641090110084799669553571)
  ·
    refine ⟨5461635165127199504330357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3641090110084799669553571 5461635165127199504330357)
    ·
      refine ⟨512028296730674953530971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5461635165127199504330357 512028296730674953530971)
      ·
        refine ⟨768042445096012430296457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 512028296730674953530971 768042445096012430296457)
        ·
          refine ⟨576031833822009322722343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 768042445096012430296457 576031833822009322722343)
          ·
            refine ⟨864047750733013984083515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 576031833822009322722343 864047750733013984083515)
            ·
              refine ⟨1296071626099520976125273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 864047750733013984083515 1296071626099520976125273)
              ·
                refine ⟨972053719574640732093955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1296071626099520976125273 972053719574640732093955)
                ·
                  refine ⟨1458080579361961098140933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 972053719574640732093955 1458080579361961098140933)
                  ·
                    refine ⟨273390108630367705901425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1458080579361961098140933 273390108630367705901425)
                    ·
                      rfl

theorem cell22_798638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_798638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_798638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_798638 prefixEnd_798638 := by exact prefixLift 798638
  have htrace : WordTrace (prefixWord ++ tailWord_798638) baseStart_798638 baseEnd_798638 := by
    simpa [prefixWord, tailWord_798638, baseEnd_798638] using wordTrace_append hprefix tailTrace_798638
  have hstable : (prefixWord ++ tailWord_798638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798638).length < 2 ^ (prefixWord ++ tailWord_798638).sum := by decide
  have hdescent : baseEnd_798638 < baseStart_798638 := by decide
  rcases family_descends (prefixWord ++ tailWord_798638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798703 : List Nat := [1, 1, 2, 1, 4, 2, 3, 2, 6]
def baseStart_798703 : Nat := 118140960795 + 798703 * 2 ^ 59
def prefixEnd_798703 : Nat := 4983230072969 + 3 ^ 40 * 798703 * 2
def baseEnd_798703 : Nat := 91137453152909734342075

theorem tailTrace_798703 : CollatzResearch.WordTrace tailWord_798703 prefixEnd_798703 91137453152909734342075 := by
  unfold tailWord_798703
  simp only [CollatzResearch.WordTrace]
  refine ⟨29131091625442913457544763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19420727750295275638363175 29131091625442913457544763)
  ·
    refine ⟨43696637438164370186317145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29131091625442913457544763 43696637438164370186317145)
    ·
      refine ⟨32772478078623277639737859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43696637438164370186317145 32772478078623277639737859)
      ·
        refine ⟨49158717117934916459606789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32772478078623277639737859 49158717117934916459606789)
        ·
          refine ⟨9217259459612796836176273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49158717117934916459606789 9217259459612796836176273)
          ·
            refine ⟨6912944594709597627132205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9217259459612796836176273 6912944594709597627132205)
            ·
              refine ⟨2592354223016099110174577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6912944594709597627132205 2592354223016099110174577)
              ·
                refine ⟨1944265667262074332630933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2592354223016099110174577 1944265667262074332630933)
                ·
                  refine ⟨91137453152909734342075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1944265667262074332630933 91137453152909734342075)
                  ·
                    rfl

theorem cell22_798703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 2, 6].length) (baseStart_798703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_798703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_798703 prefixEnd_798703 := by exact prefixLift 798703
  have htrace : WordTrace (prefixWord ++ tailWord_798703) baseStart_798703 baseEnd_798703 := by
    simpa [prefixWord, tailWord_798703, baseEnd_798703] using wordTrace_append hprefix tailTrace_798703
  have hstable : (prefixWord ++ tailWord_798703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798703).length < 2 ^ (prefixWord ++ tailWord_798703).sum := by decide
  have hdescent : baseEnd_798703 < baseStart_798703 := by decide
  rcases family_descends (prefixWord ++ tailWord_798703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798726 : List Nat := [6, 2, 1, 2, 1, 1, 1, 1, 7]
def baseStart_798726 : Nat := 118140960795 + 798726 * 2 ^ 59
def prefixEnd_798726 : Nat := 4983230072969 + 3 ^ 40 * 798726 * 2
def baseEnd_798726 : Nat := 91140077609588269900385

theorem tailTrace_798726 : CollatzResearch.WordTrace tailWord_798726 prefixEnd_798726 91140077609588269900385 := by
  unfold tailWord_798726
  simp only [CollatzResearch.WordTrace]
  refine ⟨910372828261237137051001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 19421287002906392257088021 910372828261237137051001)
  ·
    refine ⟨682779621195927852788251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 910372828261237137051001 682779621195927852788251)
    ·
      refine ⟨1024169431793891779182377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 682779621195927852788251 1024169431793891779182377)
      ·
        refine ⟨768127073845418834386783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1024169431793891779182377 768127073845418834386783)
        ·
          refine ⟨1152190610768128251580175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 768127073845418834386783 1152190610768128251580175)
          ·
            refine ⟨1728285916152192377370263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1152190610768128251580175 1728285916152192377370263)
            ·
              refine ⟨2592428874228288566055395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1728285916152192377370263 2592428874228288566055395)
              ·
                refine ⟨3888643311342432849083093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2592428874228288566055395 3888643311342432849083093)
                ·
                  refine ⟨91140077609588269900385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3888643311342432849083093 91140077609588269900385)
                  ·
                    rfl

theorem cell22_798726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_798726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_798726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_798726 prefixEnd_798726 := by exact prefixLift 798726
  have htrace : WordTrace (prefixWord ++ tailWord_798726) baseStart_798726 baseEnd_798726 := by
    simpa [prefixWord, tailWord_798726, baseEnd_798726] using wordTrace_append hprefix tailTrace_798726
  have hstable : (prefixWord ++ tailWord_798726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798726).length < 2 ^ (prefixWord ++ tailWord_798726).sum := by decide
  have hdescent : baseEnd_798726 < baseStart_798726 := by decide
  rcases family_descends (prefixWord ++ tailWord_798726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798778 : List Nat := [3, 1, 1, 1, 3, 1, 1, 2, 1, 8]
def baseStart_798778 : Nat := 118140960795 + 798778 * 2 ^ 59
def prefixEnd_798778 : Nat := 4983230072969 + 3 ^ 40 * 798778 * 2
def baseEnd_798778 : Nat := 273438033491454007400995

theorem tailTrace_798778 : CollatzResearch.WordTrace tailWord_798778 prefixEnd_798778 273438033491454007400995 := by
  unfold tailWord_798778
  simp only [CollatzResearch.WordTrace]
  refine ⟨7283456775042800316631247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19422551400114134177683325 7283456775042800316631247)
  ·
    refine ⟨10925185162564200474946871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7283456775042800316631247 10925185162564200474946871)
    ·
      refine ⟨16387777743846300712420307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10925185162564200474946871 16387777743846300712420307)
      ·
        refine ⟨24581666615769451068630461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16387777743846300712420307 24581666615769451068630461)
        ·
          refine ⟨9218124980913544150736423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24581666615769451068630461 9218124980913544150736423)
          ·
            refine ⟨13827187471370316226104635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9218124980913544150736423 13827187471370316226104635)
            ·
              refine ⟨20740781207055474339156953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13827187471370316226104635 20740781207055474339156953)
              ·
                refine ⟨15555585905291605754367715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20740781207055474339156953 15555585905291605754367715)
                ·
                  refine ⟨23333378857937408631551573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15555585905291605754367715 23333378857937408631551573)
                  ·
                    refine ⟨273438033491454007400995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 23333378857937408631551573 273438033491454007400995)
                    ·
                      rfl

theorem cell22_798778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 1, 8].length) (baseStart_798778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_798778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_798778 prefixEnd_798778 := by exact prefixLift 798778
  have htrace : WordTrace (prefixWord ++ tailWord_798778) baseStart_798778 baseEnd_798778 := by
    simpa [prefixWord, tailWord_798778, baseEnd_798778] using wordTrace_append hprefix tailTrace_798778
  have hstable : (prefixWord ++ tailWord_798778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798778).length < 2 ^ (prefixWord ++ tailWord_798778).sum := by decide
  have hdescent : baseEnd_798778 < baseStart_798778 := by decide
  rcases family_descends (prefixWord ++ tailWord_798778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798782 : List Nat := [4, 2, 1, 3, 2, 2, 8]
def baseStart_798782 : Nat := 118140960795 + 798782 * 2 ^ 59
def prefixEnd_798782 : Nat := 4983230072969 + 3 ^ 40 * 798782 * 2
def baseEnd_798782 : Nat := 10127385287896271492629

theorem tailTrace_798782 : CollatzResearch.WordTrace tailWord_798782 prefixEnd_798782 10127385287896271492629 := by
  unfold tailWord_798782
  simp only [CollatzResearch.WordTrace]
  refine ⟨3641746624019588743708825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19422648661437806633113733 3641746624019588743708825)
  ·
    refine ⟨2731309968014691557781619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3641746624019588743708825 2731309968014691557781619)
    ·
      refine ⟨4096964952022037336672429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2731309968014691557781619 4096964952022037336672429)
      ·
        refine ⟨1536361857008264001252161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4096964952022037336672429 1536361857008264001252161)
        ·
          refine ⟨1152271392756198000939121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1536361857008264001252161 1152271392756198000939121)
          ·
            refine ⟨864203544567148500704341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1152271392756198000939121 864203544567148500704341)
            ·
              refine ⟨10127385287896271492629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 864203544567148500704341 10127385287896271492629)
              ·
                rfl

theorem cell22_798782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 8].length) (baseStart_798782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_798782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_798782 prefixEnd_798782 := by exact prefixLift 798782
  have htrace : WordTrace (prefixWord ++ tailWord_798782) baseStart_798782 baseEnd_798782 := by
    simpa [prefixWord, tailWord_798782, baseEnd_798782] using wordTrace_append hprefix tailTrace_798782
  have hstable : (prefixWord ++ tailWord_798782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798782).length < 2 ^ (prefixWord ++ tailWord_798782).sum := by decide
  have hdescent : baseEnd_798782 < baseStart_798782 := by decide
  rcases family_descends (prefixWord ++ tailWord_798782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798793 : List Nat := [1, 2, 1, 1, 2, 2, 3, 3, 7]
def baseStart_798793 : Nat := 118140960795 + 798793 * 2 ^ 59
def prefixEnd_798793 : Nat := 4983230072969 + 3 ^ 40 * 798793 * 2
def baseEnd_798793 : Nat := 91147722765999656091983

theorem tailTrace_798793 : CollatzResearch.WordTrace tailWord_798793 prefixEnd_798793 91147722765999656091983 := by
  unfold tailWord_798793
  simp only [CollatzResearch.WordTrace]
  refine ⟨29134374195116858828321033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19422916130077905885547355 29134374195116858828321033)
  ·
    refine ⟨21850780646337644121240775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29134374195116858828321033 21850780646337644121240775)
    ·
      refine ⟨32776170969506466181861163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21850780646337644121240775 32776170969506466181861163)
      ·
        refine ⟨49164256454259699272791745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32776170969506466181861163 49164256454259699272791745)
        ·
          refine ⟨36873192340694774454593809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49164256454259699272791745 36873192340694774454593809)
          ·
            refine ⟨27654894255521080840945357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36873192340694774454593809 27654894255521080840945357)
            ·
              refine ⟨10370585345820405315354509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27654894255521080840945357 10370585345820405315354509)
              ·
                refine ⟨3888969504682651993257941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10370585345820405315354509 3888969504682651993257941)
                ·
                  refine ⟨91147722765999656091983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3888969504682651993257941 91147722765999656091983)
                  ·
                    rfl

theorem cell22_798793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 7].length) (baseStart_798793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_798793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_798793 prefixEnd_798793 := by exact prefixLift 798793
  have htrace : WordTrace (prefixWord ++ tailWord_798793) baseStart_798793 baseEnd_798793 := by
    simpa [prefixWord, tailWord_798793, baseEnd_798793] using wordTrace_append hprefix tailTrace_798793
  have hstable : (prefixWord ++ tailWord_798793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798793).length < 2 ^ (prefixWord ++ tailWord_798793).sum := by decide
  have hdescent : baseEnd_798793 < baseStart_798793 := by decide
  rcases family_descends (prefixWord ++ tailWord_798793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798810 : List Nat := [3, 1, 1, 2, 1, 1, 5, 3, 5]
def baseStart_798810 : Nat := 118140960795 + 798810 * 2 ^ 59
def prefixEnd_798810 : Nat := 4983230072969 + 3 ^ 40 * 798810 * 2
def baseEnd_798810 : Nat := 91149662581805530200299

theorem tailTrace_798810 : CollatzResearch.WordTrace tailWord_798810 prefixEnd_798810 91149662581805530200299 := by
  unfold tailWord_798810
  simp only [CollatzResearch.WordTrace]
  refine ⟨7283748559013817682922471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19423329490703513821126589 7283748559013817682922471)
  ·
    refine ⟨10925622838520726524383707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7283748559013817682922471 10925622838520726524383707)
    ·
      refine ⟨16388434257781089786575561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10925622838520726524383707 16388434257781089786575561)
      ·
        refine ⟨12291325693335817339931671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16388434257781089786575561 12291325693335817339931671)
        ·
          refine ⟨18436988540003726009897507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12291325693335817339931671 18436988540003726009897507)
          ·
            refine ⟨27655482810005589014846261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18436988540003726009897507 27655482810005589014846261)
            ·
              refine ⟨2592701513438023970141837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27655482810005589014846261 2592701513438023970141837)
              ·
                refine ⟨972263067539258988803189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2592701513438023970141837 972263067539258988803189)
                ·
                  refine ⟨91149662581805530200299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 972263067539258988803189 91149662581805530200299)
                  ·
                    rfl

theorem cell22_798810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 3, 5].length) (baseStart_798810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_798810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_798810 prefixEnd_798810 := by exact prefixLift 798810
  have htrace : WordTrace (prefixWord ++ tailWord_798810) baseStart_798810 baseEnd_798810 := by
    simpa [prefixWord, tailWord_798810, baseEnd_798810] using wordTrace_append hprefix tailTrace_798810
  have hstable : (prefixWord ++ tailWord_798810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798810).length < 2 ^ (prefixWord ++ tailWord_798810).sum := by decide
  have hdescent : baseEnd_798810 < baseStart_798810 := by decide
  rcases family_descends (prefixWord ++ tailWord_798810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798872 : List Nat := [2, 1, 2, 4, 3, 1, 1, 2, 6]
def baseStart_798872 : Nat := 118140960795 + 798872 * 2 ^ 59
def prefixEnd_798872 : Nat := 4983230072969 + 3 ^ 40 * 798872 * 2
def baseEnd_798872 : Nat := 91156737204156365183569

theorem tailTrace_798872 : CollatzResearch.WordTrace tailWord_798872 prefixEnd_798872 91156737204156365183569 := by
  unfold tailWord_798872
  simp only [CollatzResearch.WordTrace]
  refine ⟨14568627780915327660223435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19424837041220436880297913 14568627780915327660223435)
  ·
    refine ⟨21852941671372991490335153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14568627780915327660223435 21852941671372991490335153)
    ·
      refine ⟨16389706253529743617751365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21852941671372991490335153 16389706253529743617751365)
      ·
        refine ⟨3073069922536826928328381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16389706253529743617751365 3073069922536826928328381)
        ·
          refine ⟨1152401220951310098123143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3073069922536826928328381 1152401220951310098123143)
          ·
            refine ⟨1728601831426965147184715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1152401220951310098123143 1728601831426965147184715)
            ·
              refine ⟨2592902747140447720777073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1728601831426965147184715 2592902747140447720777073)
              ·
                refine ⟨1944677060355335790582805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2592902747140447720777073 1944677060355335790582805)
                ·
                  refine ⟨91156737204156365183569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1944677060355335790582805 91156737204156365183569)
                  ·
                    rfl

theorem cell22_798872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 2, 6].length) (baseStart_798872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_798872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_798872 prefixEnd_798872 := by exact prefixLift 798872
  have htrace : WordTrace (prefixWord ++ tailWord_798872) baseStart_798872 baseEnd_798872 := by
    simpa [prefixWord, tailWord_798872, baseEnd_798872] using wordTrace_append hprefix tailTrace_798872
  have hstable : (prefixWord ++ tailWord_798872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798872).length < 2 ^ (prefixWord ++ tailWord_798872).sum := by decide
  have hdescent : baseEnd_798872 < baseStart_798872 := by decide
  rcases family_descends (prefixWord ++ tailWord_798872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798885 : List Nat := [1, 3, 1, 2, 1, 3, 3, 1, 1, 6]
def baseStart_798885 : Nat := 118140960795 + 798885 * 2 ^ 59
def prefixEnd_798885 : Nat := 4983230072969 + 3 ^ 40 * 798885 * 2
def baseEnd_798885 : Nat := 273474661778141394975667

theorem tailTrace_798885 : CollatzResearch.WordTrace tailWord_798885 prefixEnd_798885 273474661778141394975667 := by
  unfold tailWord_798885
  simp only [CollatzResearch.WordTrace]
  refine ⟨29137729710783558540670109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19425153140522372360446739 29137729710783558540670109)
  ·
    refine ⟨10926648641543834452751291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29137729710783558540670109 10926648641543834452751291)
    ·
      refine ⟨16389972962315751679126937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10926648641543834452751291 16389972962315751679126937)
      ·
        refine ⟨12292479721736813759345203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16389972962315751679126937 12292479721736813759345203)
        ·
          refine ⟨18438719582605220639017805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12292479721736813759345203 18438719582605220639017805)
          ·
            refine ⟨6914519843476957739631677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18438719582605220639017805 6914519843476957739631677)
            ·
              refine ⟨2592944941303859152361879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6914519843476957739631677 2592944941303859152361879)
              ·
                refine ⟨3889417411955788728542819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2592944941303859152361879 3889417411955788728542819)
                ·
                  refine ⟨5834126117933683092814229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3889417411955788728542819 5834126117933683092814229)
                  ·
                    refine ⟨273474661778141394975667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5834126117933683092814229 273474661778141394975667)
                    ·
                      rfl

theorem cell22_798885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 1, 1, 6].length) (baseStart_798885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_798885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_798885 prefixEnd_798885 := by exact prefixLift 798885
  have htrace : WordTrace (prefixWord ++ tailWord_798885) baseStart_798885 baseEnd_798885 := by
    simpa [prefixWord, tailWord_798885, baseEnd_798885] using wordTrace_append hprefix tailTrace_798885
  have hstable : (prefixWord ++ tailWord_798885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798885).length < 2 ^ (prefixWord ++ tailWord_798885).sum := by decide
  have hdescent : baseEnd_798885 < baseStart_798885 := by decide
  rcases family_descends (prefixWord ++ tailWord_798885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798934 : List Nat := [5, 2, 1, 2, 1, 2, 1, 8]
def baseStart_798934 : Nat := 118140960795 + 798934 * 2 ^ 59
def prefixEnd_798934 : Nat := 4983230072969 + 3 ^ 40 * 798934 * 2
def baseEnd_798934 : Nat := 30387937275502400055613

theorem tailTrace_798934 : CollatzResearch.WordTrace tailWord_798934 prefixEnd_798934 30387937275502400055613 := by
  unfold tailWord_798934
  simp only [CollatzResearch.WordTrace]
  refine ⟨1821219805475377494325241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19426344591737359939469237 1821219805475377494325241)
  ·
    refine ⟨1365914854106533120743931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1821219805475377494325241 1365914854106533120743931)
    ·
      refine ⟨2048872281159799681115897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1365914854106533120743931 2048872281159799681115897)
      ·
        refine ⟨1536654210869849760836923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2048872281159799681115897 1536654210869849760836923)
        ·
          refine ⟨2304981316304774641255385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1536654210869849760836923 2304981316304774641255385)
          ·
            refine ⟨1728735987228580980941539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2304981316304774641255385 1728735987228580980941539)
            ·
              refine ⟨2593103980842871471412309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1728735987228580980941539 2593103980842871471412309)
              ·
                refine ⟨30387937275502400055613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2593103980842871471412309 30387937275502400055613)
                ·
                  rfl

theorem cell22_798934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 8].length) (baseStart_798934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_798934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_798934 prefixEnd_798934 := by exact prefixLift 798934
  have htrace : WordTrace (prefixWord ++ tailWord_798934) baseStart_798934 baseEnd_798934 := by
    simpa [prefixWord, tailWord_798934, baseEnd_798934] using wordTrace_append hprefix tailTrace_798934
  have hstable : (prefixWord ++ tailWord_798934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798934).length < 2 ^ (prefixWord ++ tailWord_798934).sum := by decide
  have hdescent : baseEnd_798934 < baseStart_798934 := by decide
  rcases family_descends (prefixWord ++ tailWord_798934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798940 : List Nat := [2, 2, 5, 2, 2, 1, 1, 3, 4]
def baseStart_798940 : Nat := 118140960795 + 798940 * 2 ^ 59
def prefixEnd_798940 : Nat := 4983230072969 + 3 ^ 40 * 798940 * 2
def baseEnd_798940 : Nat := 91164496467379861616833

theorem tailTrace_798940 : CollatzResearch.WordTrace tailWord_798940 prefixEnd_798940 91164496467379861616833 := by
  unfold tailWord_798940
  simp only [CollatzResearch.WordTrace]
  refine ⟨14569867862792151466961137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19426490483722868622614849 14569867862792151466961137)
  ·
    refine ⟨10927400897094113600220853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14569867862792151466961137 10927400897094113600220853)
    ·
      refine ⟨1024443834102573150020705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10927400897094113600220853 1024443834102573150020705)
      ·
        refine ⟨768332875576929862515529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1024443834102573150020705 768332875576929862515529)
        ·
          refine ⟨576249656682697396886647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 768332875576929862515529 576249656682697396886647)
          ·
            refine ⟨864374485024046095329971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 576249656682697396886647 864374485024046095329971)
            ·
              refine ⟨1296561727536069142994957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 864374485024046095329971 1296561727536069142994957)
              ·
                refine ⟨486210647826025928623109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1296561727536069142994957 486210647826025928623109)
                ·
                  refine ⟨91164496467379861616833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 486210647826025928623109 91164496467379861616833)
                  ·
                    rfl

theorem cell22_798940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 3, 4].length) (baseStart_798940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_798940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_798940 prefixEnd_798940 := by exact prefixLift 798940
  have htrace : WordTrace (prefixWord ++ tailWord_798940) baseStart_798940 baseEnd_798940 := by
    simpa [prefixWord, tailWord_798940, baseEnd_798940] using wordTrace_append hprefix tailTrace_798940
  have hstable : (prefixWord ++ tailWord_798940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798940).length < 2 ^ (prefixWord ++ tailWord_798940).sum := by decide
  have hdescent : baseEnd_798940 < baseStart_798940 := by decide
  rcases family_descends (prefixWord ++ tailWord_798940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798945 : List Nat := [1, 2, 3, 1, 3, 1, 1, 1, 9]
def baseStart_798945 : Nat := 118140960795 + 798945 * 2 ^ 59
def prefixEnd_798945 : Nat := 4983230072969 + 3 ^ 40 * 798945 * 2
def baseEnd_798945 : Nat := 91165067001440412825161

theorem tailTrace_798945 : CollatzResearch.WordTrace tailWord_798945 prefixEnd_798945 91165067001440412825161 := by
  unfold tailWord_798945
  simp only [CollatzResearch.WordTrace]
  refine ⟨29139918090566188787854289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19426612060377459191902859 29139918090566188787854289)
  ·
    refine ⟨21854938567924641590890717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29139918090566188787854289 21854938567924641590890717)
    ·
      refine ⟨8195601962971740596584019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21854938567924641590890717 8195601962971740596584019)
      ·
        refine ⟨12293402944457610894876029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8195601962971740596584019 12293402944457610894876029)
        ·
          refine ⟨4610026104171604085578511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12293402944457610894876029 4610026104171604085578511)
          ·
            refine ⟨6915039156257406128367767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4610026104171604085578511 6915039156257406128367767)
            ·
              refine ⟨10372558734386109192551651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6915039156257406128367767 10372558734386109192551651)
              ·
                refine ⟨15558838101579163788827477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10372558734386109192551651 15558838101579163788827477)
                ·
                  refine ⟨91165067001440412825161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 15558838101579163788827477 91165067001440412825161)
                  ·
                    rfl

theorem cell22_798945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 9].length) (baseStart_798945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_798945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_798945 prefixEnd_798945 := by exact prefixLift 798945
  have htrace : WordTrace (prefixWord ++ tailWord_798945) baseStart_798945 baseEnd_798945 := by
    simpa [prefixWord, tailWord_798945, baseEnd_798945] using wordTrace_append hprefix tailTrace_798945
  have hstable : (prefixWord ++ tailWord_798945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798945).length < 2 ^ (prefixWord ++ tailWord_798945).sum := by decide
  have hdescent : baseEnd_798945 < baseStart_798945 := by decide
  rcases family_descends (prefixWord ++ tailWord_798945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798960 : List Nat := [2, 1, 1, 1, 3, 1, 1, 3, 4, 5]
def baseStart_798960 : Nat := 118140960795 + 798960 * 2 ^ 59
def prefixEnd_798960 : Nat := 4983230072969 + 3 ^ 40 * 798960 * 2
def baseEnd_798960 : Nat := 273500335810866199350437

theorem tailTrace_798960 : CollatzResearch.WordTrace tailWord_798960 prefixEnd_798960 273500335810866199350437 := by
  unfold tailWord_798960
  simp only [CollatzResearch.WordTrace]
  refine ⟨14570232592755923174825167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19426976790341230899766889 14570232592755923174825167)
  ·
    refine ⟨21855348889133884762237751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14570232592755923174825167 21855348889133884762237751)
    ·
      refine ⟨32783023333700827143356627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21855348889133884762237751 32783023333700827143356627)
      ·
        refine ⟨49174535000551240715034941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32783023333700827143356627 49174535000551240715034941)
        ·
          refine ⟨18440450625206715268138103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49174535000551240715034941 18440450625206715268138103)
          ·
            refine ⟨27660675937810072902207155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18440450625206715268138103 27660675937810072902207155)
            ·
              refine ⟨41491013906715109353310733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27660675937810072902207155 41491013906715109353310733)
              ·
                refine ⟨15559130215018166007491525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41491013906715109353310733 15559130215018166007491525)
                ·
                  refine ⟨2917336915315906126404661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15559130215018166007491525 2917336915315906126404661)
                  ·
                    refine ⟨273500335810866199350437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2917336915315906126404661 273500335810866199350437)
                    ·
                      rfl

theorem cell22_798960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 4, 5].length) (baseStart_798960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_798960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_798960 prefixEnd_798960 := by exact prefixLift 798960
  have htrace : WordTrace (prefixWord ++ tailWord_798960) baseStart_798960 baseEnd_798960 := by
    simpa [prefixWord, tailWord_798960, baseEnd_798960] using wordTrace_append hprefix tailTrace_798960
  have hstable : (prefixWord ++ tailWord_798960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798960).length < 2 ^ (prefixWord ++ tailWord_798960).sum := by decide
  have hdescent : baseEnd_798960 < baseStart_798960 := by decide
  rcases family_descends (prefixWord ++ tailWord_798960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798962 : List Nat := [3, 2, 1, 3, 2, 1, 2, 1, 7]
def baseStart_798962 : Nat := 118140960795 + 798962 * 2 ^ 59
def prefixEnd_798962 : Nat := 4983230072969 + 3 ^ 40 * 798962 * 2
def baseEnd_798962 : Nat := 91167006817246286933477

theorem tailTrace_798962 : CollatzResearch.WordTrace tailWord_798962 prefixEnd_798962 91167006817246286933477 := by
  unfold tailWord_798962
  simp only [CollatzResearch.WordTrace]
  refine ⟨7285134532876150172805785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19427025421003067127482093 7285134532876150172805785)
  ·
    refine ⟨5463850899657112629604339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7285134532876150172805785 5463850899657112629604339)
    ·
      refine ⟨8195776349485668944406509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5463850899657112629604339 8195776349485668944406509)
      ·
        refine ⟨3073416131057125854152441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8195776349485668944406509 3073416131057125854152441)
        ·
          refine ⟨2305062098292844390614331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3073416131057125854152441 2305062098292844390614331)
          ·
            refine ⟨3457593147439266585921497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2305062098292844390614331 3457593147439266585921497)
            ·
              refine ⟨2593194860579449939441123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3457593147439266585921497 2593194860579449939441123)
              ·
                refine ⟨3889792290869174909161685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2593194860579449939441123 3889792290869174909161685)
                ·
                  refine ⟨91167006817246286933477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3889792290869174909161685 91167006817246286933477)
                  ·
                    rfl

theorem cell22_798962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 1, 7].length) (baseStart_798962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_798962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_798962 prefixEnd_798962 := by exact prefixLift 798962
  have htrace : WordTrace (prefixWord ++ tailWord_798962) baseStart_798962 baseEnd_798962 := by
    simpa [prefixWord, tailWord_798962, baseEnd_798962] using wordTrace_append hprefix tailTrace_798962
  have hstable : (prefixWord ++ tailWord_798962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798962).length < 2 ^ (prefixWord ++ tailWord_798962).sum := by decide
  have hdescent : baseEnd_798962 < baseStart_798962 := by decide
  rcases family_descends (prefixWord ++ tailWord_798962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_798966 : List Nat := [5, 1, 1, 1, 1, 1, 2, 6, 1, 3]
def baseStart_798966 : Nat := 118140960795 + 798966 * 2 ^ 59
def prefixEnd_798966 : Nat := 4983230072969 + 3 ^ 40 * 798966 * 2
def baseEnd_798966 : Nat := 273502389733484183700419

theorem tailTrace_798966 : CollatzResearch.WordTrace tailWord_798966 prefixEnd_798966 273502389733484183700419 := by
  unfold tailWord_798966
  simp only [CollatzResearch.WordTrace]
  refine ⟨1821292751468131835898047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19427122682326739582912501 1821292751468131835898047)
  ·
    refine ⟨2731939127202197753847071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1821292751468131835898047 2731939127202197753847071)
    ·
      refine ⟨4097908690803296630770607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2731939127202197753847071 4097908690803296630770607)
      ·
        refine ⟨6146863036204944946155911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4097908690803296630770607 6146863036204944946155911)
        ·
          refine ⟨9220294554307417419233867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6146863036204944946155911 9220294554307417419233867)
          ·
            refine ⟨13830441831461126128850801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9220294554307417419233867 13830441831461126128850801)
            ·
              refine ⟨10372831373595844596638101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13830441831461126128850801 10372831373595844596638101)
              ·
                refine ⟨486226470637305215467411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10372831373595844596638101 486226470637305215467411)
                ·
                  refine ⟨729339705955957823201117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 486226470637305215467411 729339705955957823201117)
                  ·
                    refine ⟨273502389733484183700419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 729339705955957823201117 273502389733484183700419)
                    ·
                      rfl

theorem cell22_798966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 6, 1, 3].length) (baseStart_798966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_798966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_798966 prefixEnd_798966 := by exact prefixLift 798966
  have htrace : WordTrace (prefixWord ++ tailWord_798966) baseStart_798966 baseEnd_798966 := by
    simpa [prefixWord, tailWord_798966, baseEnd_798966] using wordTrace_append hprefix tailTrace_798966
  have hstable : (prefixWord ++ tailWord_798966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_798966).length < 2 ^ (prefixWord ++ tailWord_798966).sum := by decide
  have hdescent : baseEnd_798966 < baseStart_798966 := by decide
  rcases family_descends (prefixWord ++ tailWord_798966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799039 : List Nat := [1, 1, 2, 2, 4, 1, 1, 5, 2, 3]
def baseStart_799039 : Nat := 118140960795 + 799039 * 2 ^ 59
def prefixEnd_799039 : Nat := 4983230072969 + 3 ^ 40 * 799039 * 2
def baseEnd_799039 : Nat := 273527379125336326625195

theorem tailTrace_799039 : CollatzResearch.WordTrace tailWord_799039 prefixEnd_799039 273527379125336326625195 := by
  unfold tailWord_799039
  simp only [CollatzResearch.WordTrace]
  refine ⟨29143346552225642841776171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19428897701483761894517447 29143346552225642841776171)
  ·
    refine ⟨43715019828338464262664257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29143346552225642841776171 43715019828338464262664257)
    ·
      refine ⟨32786264871253848196998193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43715019828338464262664257 32786264871253848196998193)
      ·
        refine ⟨24589698653440386147748645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32786264871253848196998193 24589698653440386147748645)
        ·
          refine ⟨4610568497520072402702871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24589698653440386147748645 4610568497520072402702871)
          ·
            refine ⟨6915852746280108604054307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4610568497520072402702871 6915852746280108604054307)
            ·
              refine ⟨10373779119420162906081461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6915852746280108604054307 10373779119420162906081461)
              ·
                refine ⟨972541792445640272445137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10373779119420162906081461 972541792445640272445137)
                ·
                  refine ⟨729406344334230204333853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 972541792445640272445137 729406344334230204333853)
                  ·
                    refine ⟨273527379125336326625195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 729406344334230204333853 273527379125336326625195)
                    ·
                      rfl

theorem cell22_799039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 5, 2, 3].length) (baseStart_799039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_799039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_799039 prefixEnd_799039 := by exact prefixLift 799039
  have htrace : WordTrace (prefixWord ++ tailWord_799039) baseStart_799039 baseEnd_799039 := by
    simpa [prefixWord, tailWord_799039, baseEnd_799039] using wordTrace_append hprefix tailTrace_799039
  have hstable : (prefixWord ++ tailWord_799039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799039).length < 2 ^ (prefixWord ++ tailWord_799039).sum := by decide
  have hdescent : baseEnd_799039 < baseStart_799039 := by decide
  rcases family_descends (prefixWord ++ tailWord_799039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799161 : List Nat := [1, 2, 1, 4, 3, 1, 3, 2, 1, 4]
def baseStart_799161 : Nat := 118140960795 + 799161 * 2 ^ 59
def prefixEnd_799161 : Nat := 4983230072969 + 3 ^ 40 * 799161 * 2
def baseEnd_799161 : Nat := 273569142218568675074821

theorem tailTrace_799161 : CollatzResearch.WordTrace tailWord_799161 prefixEnd_799161 273569142218568675074821 := by
  unfold tailWord_799161
  simp only [CollatzResearch.WordTrace]
  refine ⟨29147796257783657677717337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19431864171855771785144891 29147796257783657677717337)
  ·
    refine ⟨21860847193337743258288003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29147796257783657677717337 21860847193337743258288003)
    ·
      refine ⟨32791270790006614887432005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21860847193337743258288003 32791270790006614887432005)
      ·
        refine ⟨6148363273126240291393501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32791270790006614887432005 6148363273126240291393501)
        ·
          refine ⟨2305636227422340109272563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6148363273126240291393501 2305636227422340109272563)
          ·
            refine ⟨3458454341133510163908845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2305636227422340109272563 3458454341133510163908845)
            ·
              refine ⟨1296920377925066311465817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3458454341133510163908845 1296920377925066311465817)
              ·
                refine ⟨972690283443799733599363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1296920377925066311465817 972690283443799733599363)
                ·
                  refine ⟨1459035425165699600399045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 972690283443799733599363 1459035425165699600399045)
                  ·
                    refine ⟨273569142218568675074821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1459035425165699600399045 273569142218568675074821)
                    ·
                      rfl

theorem cell22_799161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 2, 1, 4].length) (baseStart_799161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_799161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_799161 prefixEnd_799161 := by exact prefixLift 799161
  have htrace : WordTrace (prefixWord ++ tailWord_799161) baseStart_799161 baseEnd_799161 := by
    simpa [prefixWord, tailWord_799161, baseEnd_799161] using wordTrace_append hprefix tailTrace_799161
  have hstable : (prefixWord ++ tailWord_799161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799161).length < 2 ^ (prefixWord ++ tailWord_799161).sum := by decide
  have hdescent : baseEnd_799161 < baseStart_799161 := by decide
  rcases family_descends (prefixWord ++ tailWord_799161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799249 : List Nat := [1, 2, 2, 1, 1, 2, 2, 6, 5]
def baseStart_799249 : Nat := 118140960795 + 799249 * 2 ^ 59
def prefixEnd_799249 : Nat := 4983230072969 + 3 ^ 40 * 799249 * 2
def baseEnd_799249 : Nat := 91199755472321926291517

theorem tailTrace_799249 : CollatzResearch.WordTrace tailWord_799249 prefixEnd_799249 91199755472321926291517 := by
  unfold tailWord_799249
  simp only [CollatzResearch.WordTrace]
  refine ⟨29151005881464848706920801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19434003920976565804613867 29151005881464848706920801)
  ·
    refine ⟨21863254411098636530190601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29151005881464848706920801 21863254411098636530190601)
    ·
      refine ⟨16397440808323977397642951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21863254411098636530190601 16397440808323977397642951)
      ·
        refine ⟨24596161212485966096464427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16397440808323977397642951 24596161212485966096464427)
        ·
          refine ⟨36894241818728949144696641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24596161212485966096464427 36894241818728949144696641)
          ·
            refine ⟨27670681364046711858522481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36894241818728949144696641 27670681364046711858522481)
            ·
              refine ⟨20753011023035033893891861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27670681364046711858522481 20753011023035033893891861)
              ·
                refine ⟨972797391704767213776181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20753011023035033893891861 972797391704767213776181)
                ·
                  refine ⟨91199755472321926291517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 972797391704767213776181 91199755472321926291517)
                  ·
                    rfl

theorem cell22_799249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 6, 5].length) (baseStart_799249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_799249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_799249 prefixEnd_799249 := by exact prefixLift 799249
  have htrace : WordTrace (prefixWord ++ tailWord_799249) baseStart_799249 baseEnd_799249 := by
    simpa [prefixWord, tailWord_799249, baseEnd_799249] using wordTrace_append hprefix tailTrace_799249
  have hstable : (prefixWord ++ tailWord_799249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799249).length < 2 ^ (prefixWord ++ tailWord_799249).sum := by decide
  have hdescent : baseEnd_799249 < baseStart_799249 := by decide
  rcases family_descends (prefixWord ++ tailWord_799249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799253 : List Nat := [1, 3, 2, 1, 3, 1, 1, 6, 1, 3]
def baseStart_799253 : Nat := 118140960795 + 799253 * 2 ^ 59
def prefixEnd_799253 : Nat := 4983230072969 + 3 ^ 40 * 799253 * 2
def baseEnd_799253 : Nat := 273600635698711101774539

theorem tailTrace_799253 : CollatzResearch.WordTrace tailWord_799253 prefixEnd_799253 273600635698711101774539 := by
  unfold tailWord_799253
  simp only [CollatzResearch.WordTrace]
  refine ⟨29151151773450357390066413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19434101182300238260044275 29151151773450357390066413)
  ·
    refine ⟨10931681915043884021274905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29151151773450357390066413 10931681915043884021274905)
    ·
      refine ⟨8198761436282913015956179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10931681915043884021274905 8198761436282913015956179)
      ·
        refine ⟨12298142154424369523934269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8198761436282913015956179 12298142154424369523934269)
        ·
          refine ⟨4611803307909138571475351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12298142154424369523934269 4611803307909138571475351)
          ·
            refine ⟨6917704961863707857213027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4611803307909138571475351 6917704961863707857213027)
            ·
              refine ⟨10376557442795561785819541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6917704961863707857213027 10376557442795561785819541)
              ·
                refine ⟨486401130131041958710291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10376557442795561785819541 486401130131041958710291)
                ·
                  refine ⟨729601695196562938065437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 486401130131041958710291 729601695196562938065437)
                  ·
                    refine ⟨273600635698711101774539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 729601695196562938065437 273600635698711101774539)
                    ·
                      rfl

theorem cell22_799253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 6, 1, 3].length) (baseStart_799253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_799253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_799253 prefixEnd_799253 := by exact prefixLift 799253
  have htrace : WordTrace (prefixWord ++ tailWord_799253) baseStart_799253 baseEnd_799253 := by
    simpa [prefixWord, tailWord_799253, baseEnd_799253] using wordTrace_append hprefix tailTrace_799253
  have hstable : (prefixWord ++ tailWord_799253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799253).length < 2 ^ (prefixWord ++ tailWord_799253).sum := by decide
  have hdescent : baseEnd_799253 < baseStart_799253 := by decide
  rcases family_descends (prefixWord ++ tailWord_799253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799296 : List Nat := [2, 1, 1, 2, 2, 2, 4, 3, 1, 4]
def baseStart_799296 : Nat := 118140960795 + 799296 * 2 ^ 59
def prefixEnd_799296 : Nat := 4983230072969 + 3 ^ 40 * 799296 * 2
def baseEnd_799296 : Nat := 273615355477473322949407

theorem tailTrace_799296 : CollatzResearch.WordTrace tailWord_799296 prefixEnd_799296 273615355477473322949407 := by
  unfold tailWord_799296
  simp only [CollatzResearch.WordTrace]
  refine ⟨14576360056147287866940871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19435146741529717155921161 14576360056147287866940871)
  ·
    refine ⟨21864540084220931800411307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14576360056147287866940871 21864540084220931800411307)
    ·
      refine ⟨32796810126331397700616961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21864540084220931800411307 32796810126331397700616961)
      ·
        refine ⟨24597607594748548275462721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32796810126331397700616961 24597607594748548275462721)
        ·
          refine ⟨18448205696061411206597041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24597607594748548275462721 18448205696061411206597041)
          ·
            refine ⟨13836154272046058404947781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18448205696061411206597041 13836154272046058404947781)
            ·
              refine ⟨2594278926008635950927709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13836154272046058404947781 2594278926008635950927709)
              ·
                refine ⟨972854597253238481597891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2594278926008635950927709 972854597253238481597891)
                ·
                  refine ⟨1459281895879857722396837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 972854597253238481597891 1459281895879857722396837)
                  ·
                    refine ⟨273615355477473322949407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1459281895879857722396837 273615355477473322949407)
                    ·
                      rfl

theorem cell22_799296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 3, 1, 4].length) (baseStart_799296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_799296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_799296 prefixEnd_799296 := by exact prefixLift 799296
  have htrace : WordTrace (prefixWord ++ tailWord_799296) baseStart_799296 baseEnd_799296 := by
    simpa [prefixWord, tailWord_799296, baseEnd_799296] using wordTrace_append hprefix tailTrace_799296
  have hstable : (prefixWord ++ tailWord_799296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799296).length < 2 ^ (prefixWord ++ tailWord_799296).sum := by decide
  have hdescent : baseEnd_799296 < baseStart_799296 := by decide
  rcases family_descends (prefixWord ++ tailWord_799296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799311 : List Nat := [1, 1, 2, 1, 1, 2, 4, 6, 4]
def baseStart_799311 : Nat := 118140960795 + 799311 * 2 ^ 59
def prefixEnd_799311 : Nat := 4983230072969 + 3 ^ 40 * 799311 * 2
def baseEnd_799311 : Nat := 91206830094672761274787

theorem tailTrace_799311 : CollatzResearch.WordTrace tailWord_799311 prefixEnd_799311 91206830094672761274787 := by
  unfold tailWord_799311
  simp only [CollatzResearch.WordTrace]
  refine ⟨29153267207240233295677787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19435511471493488863785191 29153267207240233295677787)
  ·
    refine ⟨43729900810860349943516681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29153267207240233295677787 43729900810860349943516681)
    ·
      refine ⟨32797425608145262457637511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43729900810860349943516681 32797425608145262457637511)
      ·
        refine ⟨49196138412217893686456267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32797425608145262457637511 49196138412217893686456267)
        ·
          refine ⟨73794207618326840529684401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49196138412217893686456267 73794207618326840529684401)
          ·
            refine ⟨55345655713745130397263301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73794207618326840529684401 55345655713745130397263301)
            ·
              refine ⟨10377310446327211949486869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55345655713745130397263301 10377310446327211949486869)
              ·
                refine ⟨486436427171588060132197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10377310446327211949486869 486436427171588060132197)
                ·
                  refine ⟨91206830094672761274787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 486436427171588060132197 91206830094672761274787)
                  ·
                    rfl

theorem cell22_799311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 6, 4].length) (baseStart_799311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_799311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_799311 prefixEnd_799311 := by exact prefixLift 799311
  have htrace : WordTrace (prefixWord ++ tailWord_799311) baseStart_799311 baseEnd_799311 := by
    simpa [prefixWord, tailWord_799311, baseEnd_799311] using wordTrace_append hprefix tailTrace_799311
  have hstable : (prefixWord ++ tailWord_799311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799311).length < 2 ^ (prefixWord ++ tailWord_799311).sum := by decide
  have hdescent : baseEnd_799311 < baseStart_799311 := by decide
  rcases family_descends (prefixWord ++ tailWord_799311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799330 : List Nat := [3, 3, 2, 3, 1, 1, 1, 1, 3, 4]
def baseStart_799330 : Nat := 118140960795 + 799330 * 2 ^ 59
def prefixEnd_799330 : Nat := 4983230072969 + 3 ^ 40 * 799330 * 2
def baseEnd_799330 : Nat := 273626994372308567599303

theorem tailTrace_799330 : CollatzResearch.WordTrace tailWord_799330 prefixEnd_799330 273626994372308567599303 := by
  unfold tailWord_799330
  simp only [CollatzResearch.WordTrace]
  refine ⟨7288490048542849885154861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19435973462780933027079629 7288490048542849885154861)
  ·
    refine ⟨2733183768203568706933073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7288490048542849885154861 2733183768203568706933073)
    ·
      refine ⟨2049887826152676530199805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2733183768203568706933073 2049887826152676530199805)
      ·
        refine ⟨768707934807253698824927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2049887826152676530199805 768707934807253698824927)
        ·
          refine ⟨1153061902210880548237391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 768707934807253698824927 1153061902210880548237391)
          ·
            refine ⟨1729592853316320822356087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1153061902210880548237391 1729592853316320822356087)
            ·
              refine ⟨2594389279974481233534131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1729592853316320822356087 2594389279974481233534131)
              ·
                refine ⟨3891583919961721850301197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2594389279974481233534131 3891583919961721850301197)
                ·
                  refine ⟨1459343969985645693862949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3891583919961721850301197 1459343969985645693862949)
                  ·
                    refine ⟨273626994372308567599303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1459343969985645693862949 273626994372308567599303)
                    ·
                      rfl

theorem cell22_799330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_799330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_799330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_799330 prefixEnd_799330 := by exact prefixLift 799330
  have htrace : WordTrace (prefixWord ++ tailWord_799330) baseStart_799330 baseEnd_799330 := by
    simpa [prefixWord, tailWord_799330, baseEnd_799330] using wordTrace_append hprefix tailTrace_799330
  have hstable : (prefixWord ++ tailWord_799330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799330).length < 2 ^ (prefixWord ++ tailWord_799330).sum := by decide
  have hdescent : baseEnd_799330 < baseStart_799330 := by decide
  rcases family_descends (prefixWord ++ tailWord_799330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799354 : List Nat := [3, 1, 1, 1, 1, 1, 1, 2, 4, 7]
def baseStart_799354 : Nat := 118140960795 + 799354 * 2 ^ 59
def prefixEnd_799354 : Nat := 4983230072969 + 3 ^ 40 * 799354 * 2
def baseEnd_799354 : Nat := 273635210062780504999229

theorem tailTrace_799354 : CollatzResearch.WordTrace tailWord_799354 prefixEnd_799354 273635210062780504999229 := by
  unfold tailWord_799354
  simp only [CollatzResearch.WordTrace]
  refine ⟨7288708886521112909873279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19436557030722967759662077 7288708886521112909873279)
  ·
    refine ⟨10933063329781669364809919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7288708886521112909873279 10933063329781669364809919)
    ·
      refine ⟨16399594994672504047214879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10933063329781669364809919 16399594994672504047214879)
      ·
        refine ⟨24599392492008756070822319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16399594994672504047214879 24599392492008756070822319)
        ·
          refine ⟨36899088738013134106233479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24599392492008756070822319 36899088738013134106233479)
          ·
            refine ⟨55348633107019701159350219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36899088738013134106233479 55348633107019701159350219)
            ·
              refine ⟨83022949660529551739025329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55348633107019701159350219 83022949660529551739025329)
              ·
                refine ⟨62267212245397163804268997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83022949660529551739025329 62267212245397163804268997)
                ·
                  refine ⟨11675102296011968213300437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62267212245397163804268997 11675102296011968213300437)
                  ·
                    refine ⟨273635210062780504999229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11675102296011968213300437 273635210062780504999229)
                    ·
                      rfl

theorem cell22_799354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 4, 7].length) (baseStart_799354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_799354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_799354 prefixEnd_799354 := by exact prefixLift 799354
  have htrace : WordTrace (prefixWord ++ tailWord_799354) baseStart_799354 baseEnd_799354 := by
    simpa [prefixWord, tailWord_799354, baseEnd_799354] using wordTrace_append hprefix tailTrace_799354
  have hstable : (prefixWord ++ tailWord_799354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799354).length < 2 ^ (prefixWord ++ tailWord_799354).sum := by decide
  have hdescent : baseEnd_799354 < baseStart_799354 := by decide
  rcases family_descends (prefixWord ++ tailWord_799354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799388 : List Nat := [2, 2, 3, 2, 2, 1, 1, 1, 5, 3]
def baseStart_799388 : Nat := 118140960795 + 799388 * 2 ^ 59
def prefixEnd_799388 : Nat := 4983230072969 + 3 ^ 40 * 799388 * 2
def baseEnd_799388 : Nat := 273646848957615749649125

theorem tailTrace_799388 : CollatzResearch.WordTrace tailWord_799388 prefixEnd_799388 273646848957615749649125 := by
  unfold tailWord_799388
  simp only [CollatzResearch.WordTrace]
  refine ⟨14578037813980637723115409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19437383751974183630820545 14578037813980637723115409)
  ·
    refine ⟨10933528360485478292336557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14578037813980637723115409 10933528360485478292336557)
    ·
      refine ⟨4100073135182054359626209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10933528360485478292336557 4100073135182054359626209)
      ·
        refine ⟨3075054851386540769719657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4100073135182054359626209 3075054851386540769719657)
        ·
          refine ⟨2306291138539905577289743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3075054851386540769719657 2306291138539905577289743)
          ·
            refine ⟨3459436707809858365934615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2306291138539905577289743 3459436707809858365934615)
            ·
              refine ⟨5189155061714787548901923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3459436707809858365934615 5189155061714787548901923)
              ·
                refine ⟨7783732592572181323352885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5189155061714787548901923 7783732592572181323352885)
                ·
                  refine ⟨729724930553641999064333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7783732592572181323352885 729724930553641999064333)
                  ·
                    refine ⟨273646848957615749649125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 729724930553641999064333 273646848957615749649125)
                    ·
                      rfl

theorem cell22_799388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 5, 3].length) (baseStart_799388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_799388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_799388 prefixEnd_799388 := by exact prefixLift 799388
  have htrace : WordTrace (prefixWord ++ tailWord_799388) baseStart_799388 baseEnd_799388 := by
    simpa [prefixWord, tailWord_799388, baseEnd_799388] using wordTrace_append hprefix tailTrace_799388
  have hstable : (prefixWord ++ tailWord_799388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799388).length < 2 ^ (prefixWord ++ tailWord_799388).sum := by decide
  have hdescent : baseEnd_799388 < baseStart_799388 := by decide
  rcases family_descends (prefixWord ++ tailWord_799388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799431 : List Nat := [1, 1, 4, 1, 1, 1, 2, 4, 3, 4]
def baseStart_799431 : Nat := 118140960795 + 799431 * 2 ^ 59
def prefixEnd_799431 : Nat := 4983230072969 + 3 ^ 40 * 799431 * 2
def baseEnd_799431 : Nat := 273661568736377970823993

theorem tailTrace_799431 : CollatzResearch.WordTrace tailWord_799431 prefixEnd_799431 273661568736377970823993 := by
  unfold tailWord_799431
  simp only [CollatzResearch.WordTrace]
  refine ⟨29157643966805493790046147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19438429311203662526697431 29157643966805493790046147)
  ·
    refine ⟨43736465950208240685069221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29157643966805493790046147 43736465950208240685069221)
    ·
      refine ⟨8200587365664045128450479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43736465950208240685069221 8200587365664045128450479)
      ·
        refine ⟨12300881048496067692675719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8200587365664045128450479 12300881048496067692675719)
        ·
          refine ⟨18451321572744101539013579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12300881048496067692675719 18451321572744101539013579)
          ·
            refine ⟨27676982359116152308520369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18451321572744101539013579 27676982359116152308520369)
            ·
              refine ⟨20757736769337114231390277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27676982359116152308520369 20757736769337114231390277)
              ·
                refine ⟨3892075644250708918385677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20757736769337114231390277 3892075644250708918385677)
                ·
                  refine ⟨1459528366594015844394629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3892075644250708918385677 1459528366594015844394629)
                  ·
                    refine ⟨273661568736377970823993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1459528366594015844394629 273661568736377970823993)
                    ·
                      rfl

theorem cell22_799431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4, 3, 4].length) (baseStart_799431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_799431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_799431 prefixEnd_799431 := by exact prefixLift 799431
  have htrace : WordTrace (prefixWord ++ tailWord_799431) baseStart_799431 baseEnd_799431 := by
    simpa [prefixWord, tailWord_799431, baseEnd_799431] using wordTrace_append hprefix tailTrace_799431
  have hstable : (prefixWord ++ tailWord_799431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799431).length < 2 ^ (prefixWord ++ tailWord_799431).sum := by decide
  have hdescent : baseEnd_799431 < baseStart_799431 := by decide
  rcases family_descends (prefixWord ++ tailWord_799431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799448 : List Nat := [2, 1, 2, 2, 3, 2, 1, 4, 1, 4]
def baseStart_799448 : Nat := 118140960795 + 799448 * 2 ^ 59
def prefixEnd_799448 : Nat := 4983230072969 + 3 ^ 40 * 799448 * 2
def baseEnd_799448 : Nat := 273667388183795593148941

theorem tailTrace_799448 : CollatzResearch.WordTrace tailWord_799448 prefixEnd_799448 273667388183795593148941 := by
  unfold tailWord_799448
  simp only [CollatzResearch.WordTrace]
  refine ⟨14579132003871952846707499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19438842671829270462276665 14579132003871952846707499)
  ·
    refine ⟨21868698005807929270061249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14579132003871952846707499 21868698005807929270061249)
    ·
      refine ⟨16401523504355946952545937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21868698005807929270061249 16401523504355946952545937)
      ·
        refine ⟨12301142628266960214409453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16401523504355946952545937 12301142628266960214409453)
        ·
          refine ⟨4612928485600110080403545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12301142628266960214409453 4612928485600110080403545)
          ·
            refine ⟨3459696364200082560302659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4612928485600110080403545 3459696364200082560302659)
            ·
              refine ⟨5189544546300123840453989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3459696364200082560302659 5189544546300123840453989)
              ·
                refine ⟨973039602431273220085123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5189544546300123840453989 973039602431273220085123)
                ·
                  refine ⟨1459559403646909830127685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 973039602431273220085123 1459559403646909830127685)
                  ·
                    refine ⟨273667388183795593148941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1459559403646909830127685 273667388183795593148941)
                    ·
                      rfl

theorem cell22_799448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 4, 1, 4].length) (baseStart_799448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_799448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_799448 prefixEnd_799448 := by exact prefixLift 799448
  have htrace : WordTrace (prefixWord ++ tailWord_799448) baseStart_799448 baseEnd_799448 := by
    simpa [prefixWord, tailWord_799448, baseEnd_799448] using wordTrace_append hprefix tailTrace_799448
  have hstable : (prefixWord ++ tailWord_799448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799448).length < 2 ^ (prefixWord ++ tailWord_799448).sum := by decide
  have hdescent : baseEnd_799448 < baseStart_799448 := by decide
  rcases family_descends (prefixWord ++ tailWord_799448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799480 : List Nat := [2, 1, 2, 1, 1, 2, 7, 2, 4]
def baseStart_799480 : Nat := 118140960795 + 799480 * 2 ^ 59
def prefixEnd_799480 : Nat := 4983230072969 + 3 ^ 40 * 799480 * 2
def baseEnd_799480 : Nat := 91226114145919392116281

theorem tailTrace_799480 : CollatzResearch.WordTrace tailWord_799480 prefixEnd_799480 91226114145919392116281 := by
  unfold tailWord_799480
  simp only [CollatzResearch.WordTrace]
  refine ⟨14579715571813987579289947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19439620762418650105719929 14579715571813987579289947)
  ·
    refine ⟨21869573357720981368934921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14579715571813987579289947 21869573357720981368934921)
    ·
      refine ⟨16402180018290736026701191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21869573357720981368934921 16402180018290736026701191)
      ·
        refine ⟨24603270027436104040051787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16402180018290736026701191 24603270027436104040051787)
        ·
          refine ⟨36904905041154156060077681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24603270027436104040051787 36904905041154156060077681)
          ·
            refine ⟨27678678780865617045058261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36904905041154156060077681 27678678780865617045058261)
            ·
              refine ⟨648719033926537899493553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 27678678780865617045058261 648719033926537899493553)
              ·
                refine ⟨486539275444903424620165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 648719033926537899493553 486539275444903424620165)
                ·
                  refine ⟨91226114145919392116281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 486539275444903424620165 91226114145919392116281)
                  ·
                    rfl

theorem cell22_799480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 7, 2, 4].length) (baseStart_799480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_799480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_799480 prefixEnd_799480 := by exact prefixLift 799480
  have htrace : WordTrace (prefixWord ++ tailWord_799480) baseStart_799480 baseEnd_799480 := by
    simpa [prefixWord, tailWord_799480, baseEnd_799480] using wordTrace_append hprefix tailTrace_799480
  have hstable : (prefixWord ++ tailWord_799480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799480).length < 2 ^ (prefixWord ++ tailWord_799480).sum := by decide
  have hdescent : baseEnd_799480 < baseStart_799480 := by decide
  rcases family_descends (prefixWord ++ tailWord_799480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799536 : List Nat := [2, 1, 1, 1, 2, 2, 1, 5, 7]
def baseStart_799536 : Nat := 118140960795 + 799536 * 2 ^ 59
def prefixEnd_799536 : Nat := 4983230072969 + 3 ^ 40 * 799536 * 2
def baseEnd_799536 : Nat := 91232504127397565649557

theorem tailTrace_799536 : CollatzResearch.WordTrace tailWord_799536 prefixEnd_799536 91232504127397565649557 := by
  unfold tailWord_799536
  simp only [CollatzResearch.WordTrace]
  refine ⟨14580736815712548361309231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19440982420950064481745641 14580736815712548361309231)
  ·
    refine ⟨21871105223568822541963847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14580736815712548361309231 21871105223568822541963847)
    ·
      refine ⟨32806657835353233812945771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21871105223568822541963847 32806657835353233812945771)
      ·
        refine ⟨49209986753029850719418657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32806657835353233812945771 49209986753029850719418657)
        ·
          refine ⟨36907490064772388039563993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49209986753029850719418657 36907490064772388039563993)
          ·
            refine ⟨27680617548579291029672995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36907490064772388039563993 27680617548579291029672995)
            ·
              refine ⟨41520926322868936544509493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27680617548579291029672995 41520926322868936544509493)
              ·
                refine ⟨3892586842768962801047765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41520926322868936544509493 3892586842768962801047765)
                ·
                  refine ⟨91232504127397565649557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3892586842768962801047765 91232504127397565649557)
                  ·
                    rfl

theorem cell22_799536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5, 7].length) (baseStart_799536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_799536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_799536 prefixEnd_799536 := by exact prefixLift 799536
  have htrace : WordTrace (prefixWord ++ tailWord_799536) baseStart_799536 baseEnd_799536 := by
    simpa [prefixWord, tailWord_799536, baseEnd_799536] using wordTrace_append hprefix tailTrace_799536
  have hstable : (prefixWord ++ tailWord_799536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799536).length < 2 ^ (prefixWord ++ tailWord_799536).sum := by decide
  have hdescent : baseEnd_799536 < baseStart_799536 := by decide
  rcases family_descends (prefixWord ++ tailWord_799536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799542 : List Nat := [5, 1, 2, 2, 2, 2, 1, 7]
def baseStart_799542 : Nat := 118140960795 + 799542 * 2 ^ 59
def prefixEnd_799542 : Nat := 4983230072969 + 3 ^ 40 * 799542 * 2
def baseEnd_799542 : Nat := 30411062922756742366517

theorem tailTrace_799542 : CollatzResearch.WordTrace tailWord_799542 prefixEnd_799542 30411062922756742366517 := by
  unfold tailWord_799542
  simp only [CollatzResearch.WordTrace]
  refine ⟨1822605779337709984208555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19441128312935573164891253 1822605779337709984208555)
  ·
    refine ⟨2733908669006564976312833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1822605779337709984208555 2733908669006564976312833)
    ·
      refine ⟨2050431501754923732234625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2733908669006564976312833 2050431501754923732234625)
      ·
        refine ⟨1537823626316192799175969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2050431501754923732234625 1537823626316192799175969)
        ·
          refine ⟨1153367719737144599381977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1537823626316192799175969 1153367719737144599381977)
          ·
            refine ⟨865025789802858449536483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1153367719737144599381977 865025789802858449536483)
            ·
              refine ⟨1297538684704287674304725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 865025789802858449536483 1297538684704287674304725)
              ·
                refine ⟨30411062922756742366517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1297538684704287674304725 30411062922756742366517)
                ·
                  rfl

theorem cell22_799542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 7].length) (baseStart_799542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_799542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_799542 prefixEnd_799542 := by exact prefixLift 799542
  have htrace : WordTrace (prefixWord ++ tailWord_799542) baseStart_799542 baseEnd_799542 := by
    simpa [prefixWord, tailWord_799542, baseEnd_799542] using wordTrace_append hprefix tailTrace_799542
  have hstable : (prefixWord ++ tailWord_799542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799542).length < 2 ^ (prefixWord ++ tailWord_799542).sum := by decide
  have hdescent : baseEnd_799542 < baseStart_799542 := by decide
  rcases family_descends (prefixWord ++ tailWord_799542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799628 : List Nat := [2, 2, 1, 2, 1, 2, 4, 1, 1, 6]
def baseStart_799628 : Nat := 118140960795 + 799628 * 2 ^ 59
def prefixEnd_799628 : Nat := 4983230072969 + 3 ^ 40 * 799628 * 2
def baseEnd_799628 : Nat := 273729005862335123648389

theorem tailTrace_799628 : CollatzResearch.WordTrace tailWord_799628 prefixEnd_799628 273729005862335123648389 := by
  unfold tailWord_799628
  simp only [CollatzResearch.WordTrace]
  refine ⟨14582414573545898217483769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19443219431394530956645025 14582414573545898217483769)
  ·
    refine ⟨10936810930159423663112827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14582414573545898217483769 10936810930159423663112827)
    ·
      refine ⟨16405216395239135494669241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10936810930159423663112827 16405216395239135494669241)
      ·
        refine ⟨12303912296429351621001931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16405216395239135494669241 12303912296429351621001931)
        ·
          refine ⟨18455868444644027431502897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12303912296429351621001931 18455868444644027431502897)
          ·
            refine ⟨13841901333483020573627173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18455868444644027431502897 13841901333483020573627173)
            ·
              refine ⟨2595356500028066357555095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13841901333483020573627173 2595356500028066357555095)
              ·
                refine ⟨3893034750042099536332643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2595356500028066357555095 3893034750042099536332643)
                ·
                  refine ⟨5839552125063149304498965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3893034750042099536332643 5839552125063149304498965)
                  ·
                    refine ⟨273729005862335123648389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5839552125063149304498965 273729005862335123648389)
                    ·
                      rfl

theorem cell22_799628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 1, 1, 6].length) (baseStart_799628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_799628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_799628 prefixEnd_799628 := by exact prefixLift 799628
  have htrace : WordTrace (prefixWord ++ tailWord_799628) baseStart_799628 baseEnd_799628 := by
    simpa [prefixWord, tailWord_799628, baseEnd_799628] using wordTrace_append hprefix tailTrace_799628
  have hstable : (prefixWord ++ tailWord_799628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799628).length < 2 ^ (prefixWord ++ tailWord_799628).sum := by decide
  have hdescent : baseEnd_799628 < baseStart_799628 := by decide
  rcases family_descends (prefixWord ++ tailWord_799628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799645 : List Nat := [1, 4, 2, 1, 2, 1, 3, 2, 2, 4]
def baseStart_799645 : Nat := 118140960795 + 799645 * 2 ^ 59
def prefixEnd_799645 : Nat := 4983230072969 + 3 ^ 40 * 799645 * 2
def baseEnd_799645 : Nat := 273734825309752745973337

theorem tailTrace_799645 : CollatzResearch.WordTrace tailWord_799645 prefixEnd_799645 273734825309752745973337 := by
  unfold tailWord_799645
  simp only [CollatzResearch.WordTrace]
  refine ⟨29165449188030208338336389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19443632792020138892224259 29165449188030208338336389)
  ·
    refine ⟨5468521722755664063438073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29165449188030208338336389 5468521722755664063438073)
    ·
      refine ⟨4101391292066748047578555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5468521722755664063438073 4101391292066748047578555)
      ·
        refine ⟨6152086938100122071367833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4101391292066748047578555 6152086938100122071367833)
        ·
          refine ⟨4614065203575091553525875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6152086938100122071367833 4614065203575091553525875)
          ·
            refine ⟨6921097805362637330288813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4614065203575091553525875 6921097805362637330288813)
            ·
              refine ⟨2595411677010988998858305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6921097805362637330288813 2595411677010988998858305)
              ·
                refine ⟨1946558757758241749143729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2595411677010988998858305 1946558757758241749143729)
                ·
                  refine ⟨1459919068318681311857797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1946558757758241749143729 1459919068318681311857797)
                  ·
                    refine ⟨273734825309752745973337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1459919068318681311857797 273734825309752745973337)
                    ·
                      rfl

theorem cell22_799645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_799645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_799645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_799645 prefixEnd_799645 := by exact prefixLift 799645
  have htrace : WordTrace (prefixWord ++ tailWord_799645) baseStart_799645 baseEnd_799645 := by
    simpa [prefixWord, tailWord_799645, baseEnd_799645] using wordTrace_append hprefix tailTrace_799645
  have hstable : (prefixWord ++ tailWord_799645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799645).length < 2 ^ (prefixWord ++ tailWord_799645).sum := by decide
  have hdescent : baseEnd_799645 < baseStart_799645 := by decide
  rcases family_descends (prefixWord ++ tailWord_799645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799649 : List Nat := [1, 2, 3, 4, 1, 2, 3, 2, 4]
def baseStart_799649 : Nat := 118140960795 + 799649 * 2 ^ 59
def prefixEnd_799649 : Nat := 4983230072969 + 3 ^ 40 * 799649 * 2
def baseEnd_799649 : Nat := 91245398197166022957775

theorem tailTrace_799649 : CollatzResearch.WordTrace tailWord_799649 prefixEnd_799649 91245398197166022957775 := by
  unfold tailWord_799649
  simp only [CollatzResearch.WordTrace]
  refine ⟨29165595080015717021482001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19443730053343811347654667 29165595080015717021482001)
  ·
    refine ⟨21874196310011787766111501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29165595080015717021482001 21874196310011787766111501)
    ·
      refine ⟨8202823616254420412291813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21874196310011787766111501 8202823616254420412291813)
      ·
        refine ⟨1538029428047703827304715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8202823616254420412291813 1538029428047703827304715)
        ·
          refine ⟨2307044142071555740957073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1538029428047703827304715 2307044142071555740957073)
          ·
            refine ⟨1730283106553666805717805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2307044142071555740957073 1730283106553666805717805)
            ·
              refine ⟨648856164957625052144177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1730283106553666805717805 648856164957625052144177)
              ·
                refine ⟨486642123718218789108133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 648856164957625052144177 486642123718218789108133)
                ·
                  refine ⟨91245398197166022957775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 486642123718218789108133 91245398197166022957775)
                  ·
                    rfl

theorem cell22_799649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 3, 2, 4].length) (baseStart_799649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_799649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_799649 prefixEnd_799649 := by exact prefixLift 799649
  have htrace : WordTrace (prefixWord ++ tailWord_799649) baseStart_799649 baseEnd_799649 := by
    simpa [prefixWord, tailWord_799649, baseEnd_799649] using wordTrace_append hprefix tailTrace_799649
  have hstable : (prefixWord ++ tailWord_799649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799649).length < 2 ^ (prefixWord ++ tailWord_799649).sum := by decide
  have hdescent : baseEnd_799649 < baseStart_799649 := by decide
  rcases family_descends (prefixWord ++ tailWord_799649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799705 : List Nat := [1, 2, 1, 2, 5, 1, 1, 4, 5]
def baseStart_799705 : Nat := 118140960795 + 799705 * 2 ^ 59
def prefixEnd_799705 : Nat := 4983230072969 + 3 ^ 40 * 799705 * 2
def baseEnd_799705 : Nat := 91251788178644196491051

theorem tailTrace_799705 : CollatzResearch.WordTrace tailWord_799705 prefixEnd_799705 91251788178644196491051 := by
  unfold tailWord_799705
  simp only [CollatzResearch.WordTrace]
  refine ⟨29167637567812838585520569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19445091711875225723680379 29167637567812838585520569)
  ·
    refine ⟨21875728175859628939140427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29167637567812838585520569 21875728175859628939140427)
    ·
      refine ⟨32813592263789443408710641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21875728175859628939140427 32813592263789443408710641)
      ·
        refine ⟨24610194197842082556532981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32813592263789443408710641 24610194197842082556532981)
        ·
          refine ⟨2307205706047695239674967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24610194197842082556532981 2307205706047695239674967)
          ·
            refine ⟨3460808559071542859512451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2307205706047695239674967 3460808559071542859512451)
            ·
              refine ⟨5191212838607314289268677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3460808559071542859512451 5191212838607314289268677)
              ·
                refine ⟨973352407238871429237877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5191212838607314289268677 973352407238871429237877)
                ·
                  refine ⟨91251788178644196491051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 973352407238871429237877 91251788178644196491051)
                  ·
                    rfl

theorem cell22_799705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 4, 5].length) (baseStart_799705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_799705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_799705 prefixEnd_799705 := by exact prefixLift 799705
  have htrace : WordTrace (prefixWord ++ tailWord_799705) baseStart_799705 baseEnd_799705 := by
    simpa [prefixWord, tailWord_799705, baseEnd_799705] using wordTrace_append hprefix tailTrace_799705
  have hstable : (prefixWord ++ tailWord_799705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799705).length < 2 ^ (prefixWord ++ tailWord_799705).sum := by decide
  have hdescent : baseEnd_799705 < baseStart_799705 := by decide
  rcases family_descends (prefixWord ++ tailWord_799705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799752 : List Nat := [2, 1, 3, 2, 1, 4, 1, 3, 1, 4]
def baseStart_799752 : Nat := 118140960795 + 799752 * 2 ^ 59
def prefixEnd_799752 : Nat := 4983230072969 + 3 ^ 40 * 799752 * 2
def baseEnd_799752 : Nat := 273771453596440133548009

theorem tailTrace_799752 : CollatzResearch.WordTrace tailWord_799752 prefixEnd_799752 273771453596440133548009 := by
  unfold tailWord_799752
  simp only [CollatzResearch.WordTrace]
  refine ⟨14584675899321282806240755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19446234532428377074987673 14584675899321282806240755)
  ·
    refine ⟨21877013848981924209361133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14584675899321282806240755 21877013848981924209361133)
    ·
      refine ⟨8203880193368221578510425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21877013848981924209361133 8203880193368221578510425)
      ·
        refine ⟨6152910145026166183882819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8203880193368221578510425 6152910145026166183882819)
        ·
          refine ⟨9229365217539249275824229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6152910145026166183882819 9229365217539249275824229)
          ·
            refine ⟨1730505978288609239217043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9229365217539249275824229 1730505978288609239217043)
            ·
              refine ⟨2595758967432913858825565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1730505978288609239217043 2595758967432913858825565)
              ·
                refine ⟨973409612787342697059587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2595758967432913858825565 973409612787342697059587)
                ·
                  refine ⟨1460114419181014045589381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 973409612787342697059587 1460114419181014045589381)
                  ·
                    refine ⟨273771453596440133548009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1460114419181014045589381 273771453596440133548009)
                    ·
                      rfl

theorem cell22_799752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 3, 1, 4].length) (baseStart_799752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_799752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_799752 prefixEnd_799752 := by exact prefixLift 799752
  have htrace : WordTrace (prefixWord ++ tailWord_799752) baseStart_799752 baseEnd_799752 := by
    simpa [prefixWord, tailWord_799752, baseEnd_799752] using wordTrace_append hprefix tailTrace_799752
  have hstable : (prefixWord ++ tailWord_799752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799752).length < 2 ^ (prefixWord ++ tailWord_799752).sum := by decide
  have hdescent : baseEnd_799752 < baseStart_799752 := by decide
  rcases family_descends (prefixWord ++ tailWord_799752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799767 : List Nat := [1, 1, 3, 5, 1, 2, 2, 1, 6]
def baseStart_799767 : Nat := 118140960795 + 799767 * 2 ^ 59
def prefixEnd_799767 : Nat := 4983230072969 + 3 ^ 40 * 799767 * 2
def baseEnd_799767 : Nat := 91258862800995031474321

theorem tailTrace_799767 : CollatzResearch.WordTrace tailWord_799767 prefixEnd_799767 91258862800995031474321 := by
  unfold tailWord_799767
  simp only [CollatzResearch.WordTrace]
  refine ⟨29169898893588223174277555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19446599262392148782851703 29169898893588223174277555)
  ·
    refine ⟨43754848340382334761416333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29169898893588223174277555 43754848340382334761416333)
    ·
      refine ⟨16408068127643375535531125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43754848340382334761416333 16408068127643375535531125)
      ·
        refine ⟨1538256386966566456456043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16408068127643375535531125 1538256386966566456456043)
        ·
          refine ⟨2307384580449849684684065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1538256386966566456456043 2307384580449849684684065)
          ·
            refine ⟨1730538435337387263513049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2307384580449849684684065 1730538435337387263513049)
            ·
              refine ⟨1297903826503040447634787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1730538435337387263513049 1297903826503040447634787)
              ·
                refine ⟨1946855739754560671452181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1297903826503040447634787 1946855739754560671452181)
                ·
                  refine ⟨91258862800995031474321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1946855739754560671452181 91258862800995031474321)
                  ·
                    rfl

theorem cell22_799767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 1, 6].length) (baseStart_799767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_799767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_799767 prefixEnd_799767 := by exact prefixLift 799767
  have htrace : WordTrace (prefixWord ++ tailWord_799767) baseStart_799767 baseEnd_799767 := by
    simpa [prefixWord, tailWord_799767, baseEnd_799767] using wordTrace_append hprefix tailTrace_799767
  have hstable : (prefixWord ++ tailWord_799767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799767).length < 2 ^ (prefixWord ++ tailWord_799767).sum := by decide
  have hdescent : baseEnd_799767 < baseStart_799767 := by decide
  rcases family_descends (prefixWord ++ tailWord_799767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799814 : List Nat := [6, 1, 1, 1, 1, 2, 1, 1, 4, 4]
def baseStart_799814 : Nat := 118140960795 + 799814 * 2 ^ 59
def prefixEnd_799814 : Nat := 4983230072969 + 3 ^ 40 * 799814 * 2
def baseEnd_799814 : Nat := 273792677463492638497819

theorem tailTrace_799814 : CollatzResearch.WordTrace tailWord_799814 prefixEnd_799814 273792677463492638497819 := by
  unfold tailWord_799814
  simp only [CollatzResearch.WordTrace]
  refine ⟨911612910138060943788703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 19447742082945300134158997 911612910138060943788703)
  ·
    refine ⟨1367419365207091415683055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 911612910138060943788703 1367419365207091415683055)
    ·
      refine ⟨2051129047810637123524583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1367419365207091415683055 2051129047810637123524583)
      ·
        refine ⟨3076693571715955685286875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2051129047810637123524583 3076693571715955685286875)
        ·
          refine ⟨4615040357573933527930313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3076693571715955685286875 4615040357573933527930313)
          ·
            refine ⟨3461280268180450145947735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4615040357573933527930313 3461280268180450145947735)
            ·
              refine ⟨5191920402270675218921603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3461280268180450145947735 5191920402270675218921603)
              ·
                refine ⟨7787880603406012828382405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5191920402270675218921603 7787880603406012828382405)
                ·
                  refine ⟨1460227613138627405321701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7787880603406012828382405 1460227613138627405321701)
                  ·
                    refine ⟨273792677463492638497819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1460227613138627405321701 273792677463492638497819)
                    ·
                      rfl

theorem cell22_799814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_799814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_799814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_799814 prefixEnd_799814 := by exact prefixLift 799814
  have htrace : WordTrace (prefixWord ++ tailWord_799814) baseStart_799814 baseEnd_799814 := by
    simpa [prefixWord, tailWord_799814, baseEnd_799814] using wordTrace_append hprefix tailTrace_799814
  have hstable : (prefixWord ++ tailWord_799814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799814).length < 2 ^ (prefixWord ++ tailWord_799814).sum := by decide
  have hdescent : baseEnd_799814 < baseStart_799814 := by decide
  rcases family_descends (prefixWord ++ tailWord_799814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799921 : List Nat := [1, 2, 2, 5, 1, 1, 4, 1, 1, 4]
def baseStart_799921 : Nat := 118140960795 + 799921 * 2 ^ 59
def prefixEnd_799921 : Nat := 4983230072969 + 3 ^ 40 * 799921 * 2
def baseEnd_799921 : Nat := 273829305750180026072491

theorem tailTrace_799921 : CollatzResearch.WordTrace tailWord_799921 prefixEnd_799921 273829305750180026072491 := by
  unfold tailWord_799921
  simp only [CollatzResearch.WordTrace]
  refine ⟨29175515735030307475383617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19450343823353538316922411 29175515735030307475383617)
  ·
    refine ⟨21881636801272730606537713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29175515735030307475383617 21881636801272730606537713)
    ·
      refine ⟨16411227600954547954903285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21881636801272730606537713 16411227600954547954903285)
      ·
        refine ⟨1538552587589488870772183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16411227600954547954903285 1538552587589488870772183)
        ·
          refine ⟨2307828881384233306158275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1538552587589488870772183 2307828881384233306158275)
          ·
            refine ⟨3461743322076349959237413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2307828881384233306158275 3461743322076349959237413)
            ·
              refine ⟨649076872889315617357015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3461743322076349959237413 649076872889315617357015)
              ·
                refine ⟨973615309333973426035523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 649076872889315617357015 973615309333973426035523)
                ·
                  refine ⟨1460422964000960139053285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 973615309333973426035523 1460422964000960139053285)
                  ·
                    refine ⟨273829305750180026072491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1460422964000960139053285 273829305750180026072491)
                    ·
                      rfl

theorem cell22_799921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 4, 1, 1, 4].length) (baseStart_799921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_799921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_799921 prefixEnd_799921 := by exact prefixLift 799921
  have htrace : WordTrace (prefixWord ++ tailWord_799921) baseStart_799921 baseEnd_799921 := by
    simpa [prefixWord, tailWord_799921, baseEnd_799921] using wordTrace_append hprefix tailTrace_799921
  have hstable : (prefixWord ++ tailWord_799921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799921).length < 2 ^ (prefixWord ++ tailWord_799921).sum := by decide
  have hdescent : baseEnd_799921 < baseStart_799921 := by decide
  rcases family_descends (prefixWord ++ tailWord_799921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800002 : List Nat := [3, 4, 1, 1, 4, 1, 2, 1, 2, 3]
def baseStart_800002 : Nat := 118140960795 + 800002 * 2 ^ 59
def prefixEnd_800002 : Nat := 4983230072969 + 3 ^ 40 * 800002 * 2
def baseEnd_800002 : Nat := 273857033705522814797243

theorem tailTrace_800002 : CollatzResearch.WordTrace tailWord_800002 prefixEnd_800002 273857033705522814797243 := by
  unfold tailWord_800002
  simp only [CollatzResearch.WordTrace]
  refine ⟨7294617511934214577270565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19452313365157905539388173 7294617511934214577270565)
  ·
    refine ⟨1367740783487665233238231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7294617511934214577270565 1367740783487665233238231)
    ·
      refine ⟨2051611175231497849857347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1367740783487665233238231 2051611175231497849857347)
      ·
        refine ⟨3077416762847246774786021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2051611175231497849857347 3077416762847246774786021)
        ·
          refine ⟨577015643033858770272379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3077416762847246774786021 577015643033858770272379)
          ·
            refine ⟨865523464550788155408569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 577015643033858770272379 865523464550788155408569)
            ·
              refine ⟨649142598413091116556427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 865523464550788155408569 649142598413091116556427)
              ·
                refine ⟨973713897619636674834641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 649142598413091116556427 973713897619636674834641)
                ·
                  refine ⟨730285423214727506125981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 973713897619636674834641 730285423214727506125981)
                  ·
                    refine ⟨273857033705522814797243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 730285423214727506125981 273857033705522814797243)
                    ·
                      rfl

theorem cell22_800002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_800002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_800002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_800002 prefixEnd_800002 := by exact prefixLift 800002
  have htrace : WordTrace (prefixWord ++ tailWord_800002) baseStart_800002 baseEnd_800002 := by
    simpa [prefixWord, tailWord_800002, baseEnd_800002] using wordTrace_append hprefix tailTrace_800002
  have hstable : (prefixWord ++ tailWord_800002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800002).length < 2 ^ (prefixWord ++ tailWord_800002).sum := by decide
  have hdescent : baseEnd_800002 < baseStart_800002 := by decide
  rcases family_descends (prefixWord ++ tailWord_800002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800067 : List Nat := [1, 1, 1, 3, 1, 3, 1, 4, 1, 6]
def baseStart_800067 : Nat := 118140960795 + 800067 * 2 ^ 59
def prefixEnd_800067 : Nat := 4983230072969 + 3 ^ 40 * 800067 * 2
def baseEnd_800067 : Nat := 273879284533884311922043

theorem tailTrace_800067 : CollatzResearch.WordTrace tailWord_800067 prefixEnd_800067 273879284533884311922043 := by
  unfold tailWord_800067
  simp only [CollatzResearch.WordTrace]
  refine ⟨29180840792501374410198455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19453893861667582940132303 29180840792501374410198455)
  ·
    refine ⟨43771261188752061615297683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29180840792501374410198455 43771261188752061615297683)
    ·
      refine ⟨65656891783128092422946525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43771261188752061615297683 65656891783128092422946525)
      ·
        refine ⟨24621334418673034658604947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65656891783128092422946525 24621334418673034658604947)
        ·
          refine ⟨36932001628009551987907421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24621334418673034658604947 36932001628009551987907421)
          ·
            refine ⟨13849500610503581995465283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36932001628009551987907421 13849500610503581995465283)
            ·
              refine ⟨20774250915755372993197925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13849500610503581995465283 20774250915755372993197925)
              ·
                refine ⟨3895172046704132436224611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20774250915755372993197925 3895172046704132436224611)
                ·
                  refine ⟨5842758070056198654336917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3895172046704132436224611 5842758070056198654336917)
                  ·
                    refine ⟨273879284533884311922043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5842758070056198654336917 273879284533884311922043)
                    ·
                      rfl

theorem cell22_800067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4, 1, 6].length) (baseStart_800067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_800067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_800067 prefixEnd_800067 := by exact prefixLift 800067
  have htrace : WordTrace (prefixWord ++ tailWord_800067) baseStart_800067 baseEnd_800067 := by
    simpa [prefixWord, tailWord_800067, baseEnd_800067] using wordTrace_append hprefix tailTrace_800067
  have hstable : (prefixWord ++ tailWord_800067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800067).length < 2 ^ (prefixWord ++ tailWord_800067).sum := by decide
  have hdescent : baseEnd_800067 < baseStart_800067 := by decide
  rcases family_descends (prefixWord ++ tailWord_800067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800084 : List Nat := [2, 4, 1, 1, 2, 1, 3, 1, 1, 6]
def baseStart_800084 : Nat := 118140960795 + 800084 * 2 ^ 59
def prefixEnd_800084 : Nat := 4983230072969 + 3 ^ 40 * 800084 * 2
def baseEnd_800084 : Nat := 273885103981301934246991

theorem tailTrace_800084 : CollatzResearch.WordTrace tailWord_800084 prefixEnd_800084 273885103981301934246991 := by
  unfold tailWord_800084
  simp only [CollatzResearch.WordTrace]
  refine ⟨14590730416719893156783653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19454307222293190875711537 14590730416719893156783653)
  ·
    refine ⟨2735761953134979966896935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14590730416719893156783653 2735761953134979966896935)
    ·
      refine ⟨4103642929702469950345403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2735761953134979966896935 4103642929702469950345403)
      ·
        refine ⟨6155464394553704925518105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4103642929702469950345403 6155464394553704925518105)
        ·
          refine ⟨4616598295915278694138579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6155464394553704925518105 4616598295915278694138579)
          ·
            refine ⟨6924897443872918041207869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4616598295915278694138579 6924897443872918041207869)
            ·
              refine ⟨2596836541452344265452951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6924897443872918041207869 2596836541452344265452951)
              ·
                refine ⟨3895254812178516398179427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2596836541452344265452951 3895254812178516398179427)
                ·
                  refine ⟨5842882218267774597269141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3895254812178516398179427 5842882218267774597269141)
                  ·
                    refine ⟨273885103981301934246991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5842882218267774597269141 273885103981301934246991)
                    ·
                      rfl

theorem cell22_800084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_800084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_800084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_800084 prefixEnd_800084 := by exact prefixLift 800084
  have htrace : WordTrace (prefixWord ++ tailWord_800084) baseStart_800084 baseEnd_800084 := by
    simpa [prefixWord, tailWord_800084, baseEnd_800084] using wordTrace_append hprefix tailTrace_800084
  have hstable : (prefixWord ++ tailWord_800084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800084).length < 2 ^ (prefixWord ++ tailWord_800084).sum := by decide
  have hdescent : baseEnd_800084 < baseStart_800084 := by decide
  rcases family_descends (prefixWord ++ tailWord_800084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800097 : List Nat := [1, 2, 3, 1, 1, 1, 1, 2, 1, 9]
def baseStart_800097 : Nat := 118140960795 + 800097 * 2 ^ 59
def prefixEnd_800097 : Nat := 4983230072969 + 3 ^ 40 * 800097 * 2
def baseEnd_800097 : Nat := 273889554146974233671951

theorem tailTrace_800097 : CollatzResearch.WordTrace tailWord_800097 prefixEnd_800097 273889554146974233671951 := by
  unfold tailWord_800097
  simp only [CollatzResearch.WordTrace]
  refine ⟨29181934982392689533790545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19454623321595126355860363 29181934982392689533790545)
  ·
    refine ⟨21886451236794517150342909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29181934982392689533790545 21886451236794517150342909)
    ·
      refine ⟨8207419213797943931378591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21886451236794517150342909 8207419213797943931378591)
      ·
        refine ⟨12311128820696915897067887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8207419213797943931378591 12311128820696915897067887)
        ·
          refine ⟨18466693231045373845601831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12311128820696915897067887 18466693231045373845601831)
          ·
            refine ⟨27700039846568060768402747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18466693231045373845601831 27700039846568060768402747)
            ·
              refine ⟨41550059769852091152604121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27700039846568060768402747 41550059769852091152604121)
              ·
                refine ⟨31162544827389068364453091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41550059769852091152604121 31162544827389068364453091)
                ·
                  refine ⟨46743817241083602546679637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31162544827389068364453091 46743817241083602546679637)
                  ·
                    refine ⟨273889554146974233671951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 46743817241083602546679637 273889554146974233671951)
                    ·
                      rfl

theorem cell22_800097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 9].length) (baseStart_800097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_800097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_800097 prefixEnd_800097 := by exact prefixLift 800097
  have htrace : WordTrace (prefixWord ++ tailWord_800097) baseStart_800097 baseEnd_800097 := by
    simpa [prefixWord, tailWord_800097, baseEnd_800097] using wordTrace_append hprefix tailTrace_800097
  have hstable : (prefixWord ++ tailWord_800097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800097).length < 2 ^ (prefixWord ++ tailWord_800097).sum := by decide
  have hdescent : baseEnd_800097 < baseStart_800097 := by decide
  rcases family_descends (prefixWord ++ tailWord_800097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800127 : List Nat := [1, 1, 2, 2, 1, 1, 2, 1, 11]
def baseStart_800127 : Nat := 118140960795 + 800127 * 2 ^ 59
def prefixEnd_800127 : Nat := 4983230072969 + 3 ^ 40 * 800127 * 2
def baseEnd_800127 : Nat := 91299941253354718473953

theorem tailTrace_800127 : CollatzResearch.WordTrace tailWord_800127 prefixEnd_800127 91299941253354718473953 := by
  unfold tailWord_800127
  simp only [CollatzResearch.WordTrace]
  refine ⟨29183029172284004657382635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19455352781522669771588423 29183029172284004657382635)
  ·
    refine ⟨43774543758426006986073953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29183029172284004657382635 43774543758426006986073953)
    ·
      refine ⟨32830907818819505239555465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43774543758426006986073953 32830907818819505239555465)
      ·
        refine ⟨24623180864114628929666599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32830907818819505239555465 24623180864114628929666599)
        ·
          refine ⟨36934771296171943394499899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24623180864114628929666599 36934771296171943394499899)
          ·
            refine ⟨55402156944257915091749849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36934771296171943394499899 55402156944257915091749849)
            ·
              refine ⟨41551617708193436318812387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55402156944257915091749849 41551617708193436318812387)
              ·
                refine ⟨62327426562290154478218581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41551617708193436318812387 62327426562290154478218581)
                ·
                  refine ⟨91299941253354718473953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 62327426562290154478218581 91299941253354718473953)
                  ·
                    rfl

theorem cell22_800127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 11].length) (baseStart_800127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_800127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_800127 prefixEnd_800127 := by exact prefixLift 800127
  have htrace : WordTrace (prefixWord ++ tailWord_800127) baseStart_800127 baseEnd_800127 := by
    simpa [prefixWord, tailWord_800127, baseEnd_800127] using wordTrace_append hprefix tailTrace_800127
  have hstable : (prefixWord ++ tailWord_800127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800127).length < 2 ^ (prefixWord ++ tailWord_800127).sum := by decide
  have hdescent : baseEnd_800127 < baseStart_800127 := by decide
  rcases family_descends (prefixWord ++ tailWord_800127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800131 : List Nat := [1, 1, 1, 3, 5, 1, 2, 2, 3, 3]
def baseStart_800131 : Nat := 118140960795 + 800131 * 2 ^ 59
def prefixEnd_800131 : Nat := 4983230072969 + 3 ^ 40 * 800131 * 2
def baseEnd_800131 : Nat := 273901193041809478321847

theorem tailTrace_800131 : CollatzResearch.WordTrace tailWord_800131 prefixEnd_800131 273901193041809478321847 := by
  unfold tailWord_800131
  simp only [CollatzResearch.WordTrace]
  refine ⟨29183175064269513340528247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19455450042846342227018831 29183175064269513340528247)
  ·
    refine ⟨43774762596404270010792371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29183175064269513340528247 43774762596404270010792371)
    ·
      refine ⟨65662143894606405016188557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43774762596404270010792371 65662143894606405016188557)
      ·
        refine ⟨24623303960477401881070709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65662143894606405016188557 24623303960477401881070709)
        ·
          refine ⟨2308434746294756426350379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24623303960477401881070709 2308434746294756426350379)
          ·
            refine ⟨3462652119442134639525569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2308434746294756426350379 3462652119442134639525569)
            ·
              refine ⟨2596989089581600979644177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3462652119442134639525569 2596989089581600979644177)
              ·
                refine ⟨1947741817186200734733133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2596989089581600979644177 1947741817186200734733133)
                ·
                  refine ⟨730403181444825275524925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1947741817186200734733133 730403181444825275524925)
                  ·
                    refine ⟨273901193041809478321847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 730403181444825275524925 273901193041809478321847)
                    ·
                      rfl

theorem cell22_800131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 2, 3, 3].length) (baseStart_800131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_800131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_800131 prefixEnd_800131 := by exact prefixLift 800131
  have htrace : WordTrace (prefixWord ++ tailWord_800131) baseStart_800131 baseEnd_800131 := by
    simpa [prefixWord, tailWord_800131, baseEnd_800131] using wordTrace_append hprefix tailTrace_800131
  have hstable : (prefixWord ++ tailWord_800131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800131).length < 2 ^ (prefixWord ++ tailWord_800131).sum := by decide
  have hdescent : baseEnd_800131 < baseStart_800131 := by decide
  rcases family_descends (prefixWord ++ tailWord_800131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800189 : List Nat := [1, 4, 1, 2, 2, 1, 2, 1, 8]
def baseStart_800189 : Nat := 118140960795 + 800189 * 2 ^ 59
def prefixEnd_800189 : Nat := 4983230072969 + 3 ^ 40 * 800189 * 2
def baseEnd_800189 : Nat := 91307015875705553457223

theorem tailTrace_800189 : CollatzResearch.WordTrace tailWord_800189 prefixEnd_800189 91307015875705553457223 := by
  unfold tailWord_800189
  simp only [CollatzResearch.WordTrace]
  refine ⟨29185290498059389246139621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19456860332039592830759747 29185290498059389246139621)
  ·
    refine ⟨5472241968386135483651179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29185290498059389246139621 5472241968386135483651179)
    ·
      refine ⟨8208362952579203225476769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5472241968386135483651179 8208362952579203225476769)
      ·
        refine ⟨6156272214434402419107577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8208362952579203225476769 6156272214434402419107577)
        ·
          refine ⟨4617204160825801814330683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6156272214434402419107577 4617204160825801814330683)
          ·
            refine ⟨6925806241238702721496025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4617204160825801814330683 6925806241238702721496025)
            ·
              refine ⟨5194354680929027041122019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6925806241238702721496025 5194354680929027041122019)
              ·
                refine ⟨7791532021393540561683029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5194354680929027041122019 7791532021393540561683029)
                ·
                  refine ⟨91307015875705553457223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7791532021393540561683029 91307015875705553457223)
                  ·
                    rfl

theorem cell22_800189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 8].length) (baseStart_800189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_800189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_800189 prefixEnd_800189 := by exact prefixLift 800189
  have htrace : WordTrace (prefixWord ++ tailWord_800189) baseStart_800189 baseEnd_800189 := by
    simpa [prefixWord, tailWord_800189, baseEnd_800189] using wordTrace_append hprefix tailTrace_800189
  have hstable : (prefixWord ++ tailWord_800189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800189).length < 2 ^ (prefixWord ++ tailWord_800189).sum := by decide
  have hdescent : baseEnd_800189 < baseStart_800189 := by decide
  rcases family_descends (prefixWord ++ tailWord_800189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800238 : List Nat := [4, 1, 2, 1, 2, 1, 1, 5, 2, 3]
def baseStart_800238 : Nat := 118140960795 + 800238 * 2 ^ 59
def prefixEnd_800238 : Nat := 4983230072969 + 3 ^ 40 * 800238 * 2
def baseEnd_800238 : Nat := 273937821328496865896519

theorem tailTrace_800238 : CollatzResearch.WordTrace tailWord_800238 prefixEnd_800238 273937821328496865896519 := by
  unfold tailWord_800238
  simp only [CollatzResearch.WordTrace]
  refine ⟨3648384709360233826834171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19458051783254580409782245 3648384709360233826834171)
  ·
    refine ⟨5472577064040350740251257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3648384709360233826834171 5472577064040350740251257)
    ·
      refine ⟨4104432798030263055188443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5472577064040350740251257 4104432798030263055188443)
      ·
        refine ⟨6156649197045394582782665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4104432798030263055188443 6156649197045394582782665)
        ·
          refine ⟨4617486897784045937086999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6156649197045394582782665 4617486897784045937086999)
          ·
            refine ⟨6926230346676068905630499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4617486897784045937086999 6926230346676068905630499)
            ·
              refine ⟨10389345520014103358445749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6926230346676068905630499 10389345520014103358445749)
              ·
                refine ⟨974001142501322189854289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10389345520014103358445749 974001142501322189854289)
                ·
                  refine ⟨730500856875991642390717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 974001142501322189854289 730500856875991642390717)
                  ·
                    refine ⟨273937821328496865896519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 730500856875991642390717 273937821328496865896519)
                    ·
                      rfl

theorem cell22_800238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 5, 2, 3].length) (baseStart_800238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_800238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_800238 prefixEnd_800238 := by exact prefixLift 800238
  have htrace : WordTrace (prefixWord ++ tailWord_800238) baseStart_800238 baseEnd_800238 := by
    simpa [prefixWord, tailWord_800238, baseEnd_800238] using wordTrace_append hprefix tailTrace_800238
  have hstable : (prefixWord ++ tailWord_800238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800238).length < 2 ^ (prefixWord ++ tailWord_800238).sum := by decide
  have hdescent : baseEnd_800238 < baseStart_800238 := by decide
  rcases family_descends (prefixWord ++ tailWord_800238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800253 : List Nat := [1, 4, 1, 1, 1, 6, 1, 1, 2, 4]
def baseStart_800253 : Nat := 118140960795 + 800253 * 2 ^ 59
def prefixEnd_800253 : Nat := 4983230072969 + 3 ^ 40 * 800253 * 2
def baseEnd_800253 : Nat := 273942956135041826771473

theorem tailTrace_800253 : CollatzResearch.WordTrace tailWord_800253 prefixEnd_800253 273942956135041826771473 := by
  unfold tailWord_800253
  simp only [CollatzResearch.WordTrace]
  refine ⟨29187624769827528176469413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19458416513218352117646275 29187624769827528176469413)
  ·
    refine ⟨5472679644342661533088015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29187624769827528176469413 5472679644342661533088015)
    ·
      refine ⟨8209019466513992299632023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5472679644342661533088015 8209019466513992299632023)
      ·
        refine ⟨12313529199770988449448035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8209019466513992299632023 12313529199770988449448035)
        ·
          refine ⟨18470293799656482674172053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12313529199770988449448035 18470293799656482674172053)
          ·
            refine ⟨865795021858897625351815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 18470293799656482674172053 865795021858897625351815)
            ·
              refine ⟨1298692532788346438027723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 865795021858897625351815 1298692532788346438027723)
              ·
                refine ⟨1948038799182519657041585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1298692532788346438027723 1948038799182519657041585)
                ·
                  refine ⟨1461029099386889742781189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1948038799182519657041585 1461029099386889742781189)
                  ·
                    refine ⟨273942956135041826771473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1461029099386889742781189 273942956135041826771473)
                    ·
                      rfl

theorem cell22_800253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 1, 2, 4].length) (baseStart_800253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_800253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_800253 prefixEnd_800253 := by exact prefixLift 800253
  have htrace : WordTrace (prefixWord ++ tailWord_800253) baseStart_800253 baseEnd_800253 := by
    simpa [prefixWord, tailWord_800253, baseEnd_800253] using wordTrace_append hprefix tailTrace_800253
  have hstable : (prefixWord ++ tailWord_800253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800253).length < 2 ^ (prefixWord ++ tailWord_800253).sum := by decide
  have hdescent : baseEnd_800253 < baseStart_800253 := by decide
  rcases family_descends (prefixWord ++ tailWord_800253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800360 : List Nat := [2, 1, 4, 3, 1, 1, 3, 2, 1, 4]
def baseStart_800360 : Nat := 118140960795 + 800360 * 2 ^ 59
def prefixEnd_800360 : Nat := 4983230072969 + 3 ^ 40 * 800360 * 2
def baseEnd_800360 : Nat := 273979584421729214346145

theorem tailTrace_800360 : CollatzResearch.WordTrace tailWord_800360 prefixEnd_800360 273979584421729214346145 := by
  unfold tailWord_800360
  simp only [CollatzResearch.WordTrace]
  refine ⟨14595763690219942725307267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19461018253626590300409689 14595763690219942725307267)
  ·
    refine ⟨21893645535329914087960901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14595763690219942725307267 21893645535329914087960901)
    ·
      refine ⟨4105058537874358891492669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21893645535329914087960901 4105058537874358891492669)
      ·
        refine ⟨1539396951702884584309751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4105058537874358891492669 1539396951702884584309751)
        ·
          refine ⟨2309095427554326876464627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1539396951702884584309751 2309095427554326876464627)
          ·
            refine ⟨3463643141331490314696941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2309095427554326876464627 3463643141331490314696941)
            ·
              refine ⟨1298866177999308868011353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3463643141331490314696941 1298866177999308868011353)
              ·
                refine ⟨974149633499481651008515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1298866177999308868011353 974149633499481651008515)
                ·
                  refine ⟨1461224450249222476512773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 974149633499481651008515 1461224450249222476512773)
                  ·
                    refine ⟨273979584421729214346145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1461224450249222476512773 273979584421729214346145)
                    ·
                      rfl

theorem cell22_800360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_800360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_800360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_800360 prefixEnd_800360 := by exact prefixLift 800360
  have htrace : WordTrace (prefixWord ++ tailWord_800360) baseStart_800360 baseEnd_800360 := by
    simpa [prefixWord, tailWord_800360, baseEnd_800360] using wordTrace_append hprefix tailTrace_800360
  have hstable : (prefixWord ++ tailWord_800360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800360).length < 2 ^ (prefixWord ++ tailWord_800360).sum := by decide
  have hdescent : baseEnd_800360 < baseStart_800360 := by decide
  rcases family_descends (prefixWord ++ tailWord_800360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800373 : List Nat := [1, 3, 4, 2, 1, 1, 1, 1, 3, 5]
def baseStart_800373 : Nat := 118140960795 + 800373 * 2 ^ 59
def prefixEnd_800373 : Nat := 4983230072969 + 3 ^ 40 * 800373 * 2
def baseEnd_800373 : Nat := 273984034587401513771105

theorem tailTrace_800373 : CollatzResearch.WordTrace tailWord_800373 prefixEnd_800373 273984034587401513771105 := by
  unfold tailWord_800373
  simp only [CollatzResearch.WordTrace]
  refine ⟨29192001529392788670837773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19461334352928525780558515 29192001529392788670837773)
  ·
    refine ⟨10947000573522295751564165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29192001529392788670837773 10947000573522295751564165)
    ·
      refine ⟨2052562607535430453418281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10947000573522295751564165 2052562607535430453418281)
      ·
        refine ⟨1539421955651572840063711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2052562607535430453418281 1539421955651572840063711)
        ·
          refine ⟨2309132933477359260095567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1539421955651572840063711 2309132933477359260095567)
          ·
            refine ⟨3463699400216038890143351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2309132933477359260095567 3463699400216038890143351)
            ·
              refine ⟨5195549100324058335215027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3463699400216038890143351 5195549100324058335215027)
              ·
                refine ⟨7793323650486087502822541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5195549100324058335215027 7793323650486087502822541)
                ·
                  refine ⟨2922496368932282813558453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7793323650486087502822541 2922496368932282813558453)
                  ·
                    refine ⟨273984034587401513771105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2922496368932282813558453 273984034587401513771105)
                    ·
                      rfl

theorem cell22_800373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_800373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_800373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_800373 prefixEnd_800373 := by exact prefixLift 800373
  have htrace : WordTrace (prefixWord ++ tailWord_800373) baseStart_800373 baseEnd_800373 := by
    simpa [prefixWord, tailWord_800373, baseEnd_800373] using wordTrace_append hprefix tailTrace_800373
  have hstable : (prefixWord ++ tailWord_800373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800373).length < 2 ^ (prefixWord ++ tailWord_800373).sum := by decide
  have hdescent : baseEnd_800373 < baseStart_800373 := by decide
  rcases family_descends (prefixWord ++ tailWord_800373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800392 : List Nat := [2, 1, 3, 5, 1, 1, 1, 4, 4]
def baseStart_800392 : Nat := 118140960795 + 800392 * 2 ^ 59
def prefixEnd_800392 : Nat := 4983230072969 + 3 ^ 40 * 800392 * 2
def baseEnd_800392 : Nat := 91330179558563932515349

theorem tailTrace_800392 : CollatzResearch.WordTrace tailWord_800392 prefixEnd_800392 91330179558563932515349 := by
  unfold tailWord_800392
  simp only [CollatzResearch.WordTrace]
  refine ⟨14596347258161977457889715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19461796344215969943852953 14596347258161977457889715)
  ·
    refine ⟨21894520887242966186834573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14596347258161977457889715 21894520887242966186834573)
    ·
      refine ⟨8210445332716112320062965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21894520887242966186834573 8210445332716112320062965)
      ·
        refine ⟨769729249942135530005903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8210445332716112320062965 769729249942135530005903)
        ·
          refine ⟨1154593874913203295008855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 769729249942135530005903 1154593874913203295008855)
          ·
            refine ⟨1731890812369804942513283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1154593874913203295008855 1731890812369804942513283)
            ·
              refine ⟨2597836218554707413769925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1731890812369804942513283 2597836218554707413769925)
              ·
                refine ⟨487094290979007640081861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2597836218554707413769925 487094290979007640081861)
                ·
                  refine ⟨91330179558563932515349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 487094290979007640081861 91330179558563932515349)
                  ·
                    rfl

theorem cell22_800392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 4, 4].length) (baseStart_800392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_800392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_800392 prefixEnd_800392 := by exact prefixLift 800392
  have htrace : WordTrace (prefixWord ++ tailWord_800392) baseStart_800392 baseEnd_800392 := by
    simpa [prefixWord, tailWord_800392, baseEnd_800392] using wordTrace_append hprefix tailTrace_800392
  have hstable : (prefixWord ++ tailWord_800392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800392).length < 2 ^ (prefixWord ++ tailWord_800392).sum := by decide
  have hdescent : baseEnd_800392 < baseStart_800392 := by decide
  rcases family_descends (prefixWord ++ tailWord_800392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800431 : List Nat := [1, 1, 2, 1, 2, 4, 2, 2, 7]
def baseStart_800431 : Nat := 118140960795 + 800431 * 2 ^ 59
def prefixEnd_800431 : Nat := 4983230072969 + 3 ^ 40 * 800431 * 2
def baseEnd_800431 : Nat := 91334629724236231940309

theorem tailTrace_800431 : CollatzResearch.WordTrace tailWord_800431 prefixEnd_800431 91334629724236231940309 := by
  unfold tailWord_800431
  simp only [CollatzResearch.WordTrace]
  refine ⟨29194116963182664576449147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19462744642121776384299431 29194116963182664576449147)
  ·
    refine ⟨43791175444773996864673721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29194116963182664576449147 43791175444773996864673721)
    ·
      refine ⟨32843381583580497648505291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43791175444773996864673721 32843381583580497648505291)
      ·
        refine ⟨49265072375370746472757937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32843381583580497648505291 49265072375370746472757937)
        ·
          refine ⟨36948804281528059854568453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49265072375370746472757937 36948804281528059854568453)
          ·
            refine ⟨6927900802786511222731585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36948804281528059854568453 6927900802786511222731585)
            ·
              refine ⟨5195925602089883417048689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6927900802786511222731585 5195925602089883417048689)
              ·
                refine ⟨3896944201567412562786517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5195925602089883417048689 3896944201567412562786517)
                ·
                  refine ⟨91334629724236231940309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3896944201567412562786517 91334629724236231940309)
                  ·
                    rfl

theorem cell22_800431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2, 7].length) (baseStart_800431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_800431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_800431 prefixEnd_800431 := by exact prefixLift 800431
  have htrace : WordTrace (prefixWord ++ tailWord_800431) baseStart_800431 baseEnd_800431 := by
    simpa [prefixWord, tailWord_800431, baseEnd_800431] using wordTrace_append hprefix tailTrace_800431
  have hstable : (prefixWord ++ tailWord_800431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800431).length < 2 ^ (prefixWord ++ tailWord_800431).sum := by decide
  have hdescent : baseEnd_800431 < baseStart_800431 := by decide
  rcases family_descends (prefixWord ++ tailWord_800431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800452 : List Nat := [2, 3, 3, 1, 1, 1, 1, 6, 1, 3]
def baseStart_800452 : Nat := 118140960795 + 800452 * 2 ^ 59
def prefixEnd_800452 : Nat := 4983230072969 + 3 ^ 40 * 800452 * 2
def baseEnd_800452 : Nat := 274011077901871641045863

theorem tailTrace_800452 : CollatzResearch.WordTrace tailWord_800452 prefixEnd_800452 274011077901871641045863 := by
  unfold tailWord_800452
  simp only [CollatzResearch.WordTrace]
  refine ⟨14597441448053292581481805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19463255264071056775309073 14597441448053292581481805)
  ·
    refine ⟨5474040543019984718055677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14597441448053292581481805 5474040543019984718055677)
    ·
      refine ⟨2052765203632494269270879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5474040543019984718055677 2052765203632494269270879)
      ·
        refine ⟨3079147805448741403906319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2052765203632494269270879 3079147805448741403906319)
        ·
          refine ⟨4618721708173112105859479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3079147805448741403906319 4618721708173112105859479)
          ·
            refine ⟨6928082562259668158789219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4618721708173112105859479 6928082562259668158789219)
            ·
              refine ⟨10392123843389502238183829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6928082562259668158789219 10392123843389502238183829)
              ·
                refine ⟨487130805158882917414867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10392123843389502238183829 487130805158882917414867)
                ·
                  refine ⟨730696207738324376122301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 487130805158882917414867 730696207738324376122301)
                  ·
                    refine ⟨274011077901871641045863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 730696207738324376122301 274011077901871641045863)
                    ·
                      rfl

theorem cell22_800452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_800452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_800452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_800452 prefixEnd_800452 := by exact prefixLift 800452
  have htrace : WordTrace (prefixWord ++ tailWord_800452) baseStart_800452 baseEnd_800452 := by
    simpa [prefixWord, tailWord_800452, baseEnd_800452] using wordTrace_append hprefix tailTrace_800452
  have hstable : (prefixWord ++ tailWord_800452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800452).length < 2 ^ (prefixWord ++ tailWord_800452).sum := by decide
  have hdescent : baseEnd_800452 < baseStart_800452 := by decide
  rcases family_descends (prefixWord ++ tailWord_800452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800465 : List Nat := [1, 2, 2, 1, 2, 5, 3, 1, 5]
def baseStart_800465 : Nat := 118140960795 + 800465 * 2 ^ 59
def prefixEnd_800465 : Nat := 4983230072969 + 3 ^ 40 * 800465 * 2
def baseEnd_800465 : Nat := 91338509355847980156941

theorem tailTrace_800465 : CollatzResearch.WordTrace tailWord_800465 prefixEnd_800465 91338509355847980156941 := by
  unfold tailWord_800465
  simp only [CollatzResearch.WordTrace]
  refine ⟨29195357045059488383186849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19463571363372992255457899 29195357045059488383186849)
  ·
    refine ⟨21896517783794616287390137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29195357045059488383186849 21896517783794616287390137)
    ·
      refine ⟨16422388337845962215542603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21896517783794616287390137 16422388337845962215542603)
      ·
        refine ⟨24633582506768943323313905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16422388337845962215542603 24633582506768943323313905)
        ·
          refine ⟨18475186880076707492485429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24633582506768943323313905 18475186880076707492485429)
          ·
            refine ⟨1732048770007191327420509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18475186880076707492485429 1732048770007191327420509)
            ·
              refine ⟨649518288752696747782691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1732048770007191327420509 649518288752696747782691)
              ·
                refine ⟨974277433129045121674037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 649518288752696747782691 974277433129045121674037)
                ·
                  refine ⟨91338509355847980156941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 974277433129045121674037 91338509355847980156941)
                  ·
                    rfl

theorem cell22_800465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 3, 1, 5].length) (baseStart_800465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_800465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_800465 prefixEnd_800465 := by exact prefixLift 800465
  have htrace : WordTrace (prefixWord ++ tailWord_800465) baseStart_800465 baseEnd_800465 := by
    simpa [prefixWord, tailWord_800465, baseEnd_800465] using wordTrace_append hprefix tailTrace_800465
  have hstable : (prefixWord ++ tailWord_800465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800465).length < 2 ^ (prefixWord ++ tailWord_800465).sum := by decide
  have hdescent : baseEnd_800465 < baseStart_800465 := by decide
  rcases family_descends (prefixWord ++ tailWord_800465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800538 : List Nat := [3, 1, 1, 3, 2, 2, 2, 8]
def baseStart_800538 : Nat := 118140960795 + 800538 * 2 ^ 59
def prefixEnd_800538 : Nat := 4983230072969 + 3 ^ 40 * 800538 * 2
def baseEnd_800538 : Nat := 30448946384377342599511

theorem tailTrace_800538 : CollatzResearch.WordTrace tailWord_800538 prefixEnd_800538 30448946384377342599511 := by
  unfold tailWord_800538
  simp only [CollatzResearch.WordTrace]
  refine ⟨7299504893448755462648567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19465346382530014567062845 7299504893448755462648567)
  ·
    refine ⟨10949257340173133193972851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7299504893448755462648567 10949257340173133193972851)
    ·
      refine ⟨16423886010259699790959277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10949257340173133193972851 16423886010259699790959277)
      ·
        refine ⟨6158957253847387421609729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16423886010259699790959277 6158957253847387421609729)
        ·
          refine ⟨4619217940385540566207297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6158957253847387421609729 4619217940385540566207297)
          ·
            refine ⟨3464413455289155424655473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4619217940385540566207297 3464413455289155424655473)
            ·
              refine ⟨2598310091466866568491605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3464413455289155424655473 2598310091466866568491605)
              ·
                refine ⟨30448946384377342599511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2598310091466866568491605 30448946384377342599511)
                ·
                  rfl

theorem cell22_800538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 8].length) (baseStart_800538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_800538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_800538 prefixEnd_800538 := by exact prefixLift 800538
  have htrace : WordTrace (prefixWord ++ tailWord_800538) baseStart_800538 baseEnd_800538 := by
    simpa [prefixWord, tailWord_800538, baseEnd_800538] using wordTrace_append hprefix tailTrace_800538
  have hstable : (prefixWord ++ tailWord_800538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800538).length < 2 ^ (prefixWord ++ tailWord_800538).sum := by decide
  have hdescent : baseEnd_800538 < baseStart_800538 := by decide
  rcases family_descends (prefixWord ++ tailWord_800538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800540 : List Nat := [2, 2, 3, 1, 1, 2, 4, 1, 2, 4]
def baseStart_800540 : Nat := 118140960795 + 800540 * 2 ^ 59
def prefixEnd_800540 : Nat := 4983230072969 + 3 ^ 40 * 800540 * 2
def baseEnd_800540 : Nat := 274041202100268744845593

theorem tailTrace_800540 : CollatzResearch.WordTrace tailWord_800540 prefixEnd_800540 274041202100268744845593 := by
  unfold tailWord_800540
  simp only [CollatzResearch.WordTrace]
  refine ⟨14599046259893888096083537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19465395013191850794778049 14599046259893888096083537)
  ·
    refine ⟨10949284694920416072062653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14599046259893888096083537 10949284694920416072062653)
    ·
      refine ⟨4105981760595156027023495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10949284694920416072062653 4105981760595156027023495)
      ·
        refine ⟨6158972640892734040535243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4105981760595156027023495 6158972640892734040535243)
        ·
          refine ⟨9238458961339101060802865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6158972640892734040535243 9238458961339101060802865)
          ·
            refine ⟨6928844221004325795602149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9238458961339101060802865 6928844221004325795602149)
            ·
              refine ⟨1299158291438311086675403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6928844221004325795602149 1299158291438311086675403)
              ·
                refine ⟨1948737437157466630013105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1299158291438311086675403 1948737437157466630013105)
                ·
                  refine ⟨1461553077868099972509829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1948737437157466630013105 1461553077868099972509829)
                  ·
                    refine ⟨274041202100268744845593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1461553077868099972509829 274041202100268744845593)
                    ·
                      rfl

theorem cell22_800540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_800540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_800540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_800540 prefixEnd_800540 := by exact prefixLift 800540
  have htrace : WordTrace (prefixWord ++ tailWord_800540) baseStart_800540 baseEnd_800540 := by
    simpa [prefixWord, tailWord_800540, baseEnd_800540] using wordTrace_append hprefix tailTrace_800540
  have hstable : (prefixWord ++ tailWord_800540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800540).length < 2 ^ (prefixWord ++ tailWord_800540).sum := by decide
  have hdescent : baseEnd_800540 < baseStart_800540 := by decide
  rcases family_descends (prefixWord ++ tailWord_800540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800568 : List Nat := [2, 1, 2, 1, 3, 3, 1, 1, 2, 6]
def baseStart_800568 : Nat := 118140960795 + 800568 * 2 ^ 59
def prefixEnd_800568 : Nat := 4983230072969 + 3 ^ 40 * 800568 * 2
def baseEnd_800568 : Nat := 274050787072486005145507

theorem tailTrace_800568 : CollatzResearch.WordTrace tailWord_800568 prefixEnd_800568 274050787072486005145507 := by
  unfold tailWord_800568
  simp only [CollatzResearch.WordTrace]
  refine ⟨14599556881843168487093179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19466075842457557982790905 14599556881843168487093179)
  ·
    refine ⟨21899335322764752730639769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14599556881843168487093179 21899335322764752730639769)
    ·
      refine ⟨16424501492073564547979827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21899335322764752730639769 16424501492073564547979827)
      ·
        refine ⟨24636752238110346821969741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16424501492073564547979827 24636752238110346821969741)
        ·
          refine ⟨9238782089291380058238653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24636752238110346821969741 9238782089291380058238653)
          ·
            refine ⟨3464543283484267521839495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9238782089291380058238653 3464543283484267521839495)
            ·
              refine ⟨5196814925226401282759243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3464543283484267521839495 5196814925226401282759243)
              ·
                refine ⟨7795222387839601924138865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5196814925226401282759243 7795222387839601924138865)
                ·
                  refine ⟨5846416790879701443104149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7795222387839601924138865 5846416790879701443104149)
                  ·
                    refine ⟨274050787072486005145507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5846416790879701443104149 274050787072486005145507)
                    ·
                      rfl

theorem cell22_800568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 2, 6].length) (baseStart_800568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_800568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_800568 prefixEnd_800568 := by exact prefixLift 800568
  have htrace : WordTrace (prefixWord ++ tailWord_800568) baseStart_800568 baseEnd_800568 := by
    simpa [prefixWord, tailWord_800568, baseEnd_800568] using wordTrace_append hprefix tailTrace_800568
  have hstable : (prefixWord ++ tailWord_800568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800568).length < 2 ^ (prefixWord ++ tailWord_800568).sum := by decide
  have hdescent : baseEnd_800568 < baseStart_800568 := by decide
  rcases family_descends (prefixWord ++ tailWord_800568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800780 : List Nat := [2, 2, 1, 2, 3, 1, 1, 2, 8]
def baseStart_800780 : Nat := 118140960795 + 800780 * 2 ^ 59
def prefixEnd_800780 : Nat := 4983230072969 + 3 ^ 40 * 800780 * 2
def baseEnd_800780 : Nat := 91374453001662706281619

theorem tailTrace_800780 : CollatzResearch.WordTrace tailWord_800780 prefixEnd_800780 91374453001662706281619 := by
  unfold tailWord_800780
  simp only [CollatzResearch.WordTrace]
  refine ⟨14603423019459148590451897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19471230692612198120602529 14603423019459148590451897)
  ·
    refine ⟨10952567264594361442838923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14603423019459148590451897 10952567264594361442838923)
    ·
      refine ⟨16428850896891542164258385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10952567264594361442838923 16428850896891542164258385)
      ·
        refine ⟨12321638172668656623193789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16428850896891542164258385 12321638172668656623193789)
        ·
          refine ⟨4620614314750746233697671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12321638172668656623193789 4620614314750746233697671)
          ·
            refine ⟨6930921472126119350546507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4620614314750746233697671 6930921472126119350546507)
            ·
              refine ⟨10396382208189179025819761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6930921472126119350546507 10396382208189179025819761)
              ·
                refine ⟨7797286656141884269364821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10396382208189179025819761 7797286656141884269364821)
                ·
                  refine ⟨91374453001662706281619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7797286656141884269364821 91374453001662706281619)
                  ·
                    rfl

theorem cell22_800780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 8].length) (baseStart_800780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_800780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_800780 prefixEnd_800780 := by exact prefixLift 800780
  have htrace : WordTrace (prefixWord ++ tailWord_800780) baseStart_800780 baseEnd_800780 := by
    simpa [prefixWord, tailWord_800780, baseEnd_800780] using wordTrace_append hprefix tailTrace_800780
  have hstable : (prefixWord ++ tailWord_800780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800780).length < 2 ^ (prefixWord ++ tailWord_800780).sum := by decide
  have hdescent : baseEnd_800780 < baseStart_800780 := by decide
  rcases family_descends (prefixWord ++ tailWord_800780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800797 : List Nat := [1, 4, 2, 2, 2, 1, 1, 3, 6]
def baseStart_800797 : Nat := 118140960795 + 800797 * 2 ^ 59
def prefixEnd_800797 : Nat := 4983230072969 + 3 ^ 40 * 800797 * 2
def baseEnd_800797 : Nat := 91376392817468580389935

theorem tailTrace_800797 : CollatzResearch.WordTrace tailWord_800797 prefixEnd_800797 91376392817468580389935 := by
  unfold tailWord_800797
  simp only [CollatzResearch.WordTrace]
  refine ⟨29207466079856709084272645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19471644053237806056181763 29207466079856709084272645)
  ·
    refine ⟨5476399889973132953301121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29207466079856709084272645 5476399889973132953301121)
    ·
      refine ⟨4107299917479849714975841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5476399889973132953301121 4107299917479849714975841)
      ·
        refine ⟨3080474938109887286231881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4107299917479849714975841 3080474938109887286231881)
        ·
          refine ⟨2310356203582415464673911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3080474938109887286231881 2310356203582415464673911)
          ·
            refine ⟨3465534305373623197010867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2310356203582415464673911 3465534305373623197010867)
            ·
              refine ⟨5198301458060434795516301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3465534305373623197010867 5198301458060434795516301)
              ·
                refine ⟨1949363046772663048318613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5198301458060434795516301 1949363046772663048318613)
                ·
                  refine ⟨91376392817468580389935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1949363046772663048318613 91376392817468580389935)
                  ·
                    rfl

theorem cell22_800797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 3, 6].length) (baseStart_800797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_800797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_800797 prefixEnd_800797 := by exact prefixLift 800797
  have htrace : WordTrace (prefixWord ++ tailWord_800797) baseStart_800797 baseEnd_800797 := by
    simpa [prefixWord, tailWord_800797, baseEnd_800797] using wordTrace_append hprefix tailTrace_800797
  have hstable : (prefixWord ++ tailWord_800797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800797).length < 2 ^ (prefixWord ++ tailWord_800797).sum := by decide
  have hdescent : baseEnd_800797 < baseStart_800797 := by decide
  rcases family_descends (prefixWord ++ tailWord_800797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800904 : List Nat := [2, 1, 3, 4, 1, 1, 1, 4, 5]
def baseStart_800904 : Nat := 118140960795 + 800904 * 2 ^ 59
def prefixEnd_800904 : Nat := 4983230072969 + 3 ^ 40 * 800904 * 2
def baseEnd_800904 : Nat := 91388602246364376248159

theorem tailTrace_800904 : CollatzResearch.WordTrace tailWord_800904 prefixEnd_800904 91388602246364376248159 := by
  unfold tailWord_800904
  simp only [CollatzResearch.WordTrace]
  refine ⟨14605684345234533179208883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19474245793646044238945177 14605684345234533179208883)
  ·
    refine ⟨21908526517851799768813325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14605684345234533179208883 21908526517851799768813325)
    ·
      refine ⟨8215697444194424913304997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21908526517851799768813325 8215697444194424913304997)
      ·
        refine ⟨1540443270786454671244687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8215697444194424913304997 1540443270786454671244687)
        ·
          refine ⟨2310664906179682006867031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1540443270786454671244687 2310664906179682006867031)
          ·
            refine ⟨3465997359269523010300547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2310664906179682006867031 3465997359269523010300547)
            ·
              refine ⟨5198996038904284515450821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3465997359269523010300547 5198996038904284515450821)
              ·
                refine ⟨974811757294553346647029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5198996038904284515450821 974811757294553346647029)
                ·
                  refine ⟨91388602246364376248159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 974811757294553346647029 91388602246364376248159)
                  ·
                    rfl

theorem cell22_800904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 4, 5].length) (baseStart_800904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_800904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_800904 prefixEnd_800904 := by exact prefixLift 800904
  have htrace : WordTrace (prefixWord ++ tailWord_800904) baseStart_800904 baseEnd_800904 := by
    simpa [prefixWord, tailWord_800904, baseEnd_800904] using wordTrace_append hprefix tailTrace_800904
  have hstable : (prefixWord ++ tailWord_800904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800904).length < 2 ^ (prefixWord ++ tailWord_800904).sum := by decide
  have hdescent : baseEnd_800904 < baseStart_800904 := by decide
  rcases family_descends (prefixWord ++ tailWord_800904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800917 : List Nat := [1, 3, 2, 1, 1, 1, 3, 1, 5, 4]
def baseStart_800917 : Nat := 118140960795 + 800917 * 2 ^ 59
def prefixEnd_800917 : Nat := 4983230072969 + 3 ^ 40 * 800917 * 2
def baseEnd_800917 : Nat := 274170256904765428169437

theorem tailTrace_800917 : CollatzResearch.WordTrace tailWord_800917 prefixEnd_800917 274170256904765428169437 := by
  unfold tailWord_800917
  simp only [CollatzResearch.WordTrace]
  refine ⟨29211842839421969578641005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19474561892947979719094003 29211842839421969578641005)
  ·
    refine ⟨10954441064783238591990377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29211842839421969578641005 10954441064783238591990377)
    ·
      refine ⟨8215830798587428943992783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10954441064783238591990377 8215830798587428943992783)
      ·
        refine ⟨12323746197881143415989175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8215830798587428943992783 12323746197881143415989175)
        ·
          refine ⟨18485619296821715123983763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12323746197881143415989175 18485619296821715123983763)
          ·
            refine ⟨27728428945232572685975645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18485619296821715123983763 27728428945232572685975645)
            ·
              refine ⟨10398160854462214757240867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27728428945232572685975645 10398160854462214757240867)
              ·
                refine ⟨15597241281693322135861301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10398160854462214757240867 15597241281693322135861301)
                ·
                  refine ⟨1462241370158748950236997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15597241281693322135861301 1462241370158748950236997)
                  ·
                    refine ⟨274170256904765428169437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1462241370158748950236997 274170256904765428169437)
                    ·
                      rfl

theorem cell22_800917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 5, 4].length) (baseStart_800917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_800917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_800917 prefixEnd_800917 := by exact prefixLift 800917
  have htrace : WordTrace (prefixWord ++ tailWord_800917) baseStart_800917 baseEnd_800917 := by
    simpa [prefixWord, tailWord_800917, baseEnd_800917] using wordTrace_append hprefix tailTrace_800917
  have hstable : (prefixWord ++ tailWord_800917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800917).length < 2 ^ (prefixWord ++ tailWord_800917).sum := by decide
  have hdescent : baseEnd_800917 < baseStart_800917 := by decide
  rcases family_descends (prefixWord ++ tailWord_800917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800919 : List Nat := [1, 1, 3, 3, 4, 1, 1, 1, 2, 5]
def baseStart_800919 : Nat := 118140960795 + 800919 * 2 ^ 59
def prefixEnd_800919 : Nat := 4983230072969 + 3 ^ 40 * 800919 * 2
def baseEnd_800919 : Nat := 274170941545638089619431

theorem tailTrace_800919 : CollatzResearch.WordTrace tailWord_800919 prefixEnd_800919 274170941545638089619431 := by
  unfold tailWord_800919
  simp only [CollatzResearch.WordTrace]
  refine ⟨29211915785414723920213811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19474610523609815946809207 29211915785414723920213811)
  ·
    refine ⟨43817873678122085880320717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29211915785414723920213811 43817873678122085880320717)
    ·
      refine ⟨16431702629295782205120269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43817873678122085880320717 16431702629295782205120269)
      ·
        refine ⟨6161888485985918326920101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16431702629295782205120269 6161888485985918326920101)
        ·
          refine ⟨1155354091122359686297519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6161888485985918326920101 1155354091122359686297519)
          ·
            refine ⟨1733031136683539529446279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1155354091122359686297519 1733031136683539529446279)
            ·
              refine ⟨2599546705025309294169419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1733031136683539529446279 2599546705025309294169419)
              ·
                refine ⟨3899320057537963941254129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2599546705025309294169419 3899320057537963941254129)
                ·
                  refine ⟨2924490043153472955940597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3899320057537963941254129 2924490043153472955940597)
                  ·
                    refine ⟨274170941545638089619431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2924490043153472955940597 274170941545638089619431)
                    ·
                      rfl

theorem cell22_800919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 1, 2, 5].length) (baseStart_800919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_800919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_800919 prefixEnd_800919 := by exact prefixLift 800919
  have htrace : WordTrace (prefixWord ++ tailWord_800919) baseStart_800919 baseEnd_800919 := by
    simpa [prefixWord, tailWord_800919, baseEnd_800919] using wordTrace_append hprefix tailTrace_800919
  have hstable : (prefixWord ++ tailWord_800919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800919).length < 2 ^ (prefixWord ++ tailWord_800919).sum := by decide
  have hdescent : baseEnd_800919 < baseStart_800919 := by decide
  rcases family_descends (prefixWord ++ tailWord_800919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800942 : List Nat := [4, 1, 4, 2, 1, 1, 2, 3, 1, 3]
def baseStart_800942 : Nat := 118140960795 + 800942 * 2 ^ 59
def prefixEnd_800942 : Nat := 4983230072969 + 3 ^ 40 * 800942 * 2
def baseEnd_800942 : Nat := 274178814915673696294361

theorem tailTrace_800942 : CollatzResearch.WordTrace tailWord_800942 prefixEnd_800942 274178814915673696294361 := by
  unfold tailWord_800942
  simp only [CollatzResearch.WordTrace]
  refine ⟨3651594333041424856037635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19475169776220932565534053 3651594333041424856037635)
  ·
    refine ⟨5477391499562137284056453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3651594333041424856037635 5477391499562137284056453)
    ·
      refine ⟨1027010906167900740760585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5477391499562137284056453 1027010906167900740760585)
      ·
        refine ⟨770258179625925555570439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1027010906167900740760585 770258179625925555570439)
        ·
          refine ⟨1155387269438888333355659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 770258179625925555570439 1155387269438888333355659)
          ·
            refine ⟨1733080904158332500033489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1155387269438888333355659 1733080904158332500033489)
            ·
              refine ⟨1299810678118749375025117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1733080904158332500033489 1299810678118749375025117)
              ·
                refine ⟨487429004294531015634419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1299810678118749375025117 487429004294531015634419)
                ·
                  refine ⟨731143506441796523451629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 487429004294531015634419 731143506441796523451629)
                  ·
                    refine ⟨274178814915673696294361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 731143506441796523451629 274178814915673696294361)
                    ·
                      rfl

theorem cell22_800942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_800942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_800942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_800942 prefixEnd_800942 := by exact prefixLift 800942
  have htrace : WordTrace (prefixWord ++ tailWord_800942) baseStart_800942 baseEnd_800942 := by
    simpa [prefixWord, tailWord_800942, baseEnd_800942] using wordTrace_append hprefix tailTrace_800942
  have hstable : (prefixWord ++ tailWord_800942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800942).length < 2 ^ (prefixWord ++ tailWord_800942).sum := by decide
  have hdescent : baseEnd_800942 < baseStart_800942 := by decide
  rcases family_descends (prefixWord ++ tailWord_800942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800951 : List Nat := [1, 1, 3, 1, 4, 2, 4, 1, 1, 4]
def baseStart_800951 : Nat := 118140960795 + 800951 * 2 ^ 59
def prefixEnd_800951 : Nat := 4983230072969 + 3 ^ 40 * 800951 * 2
def baseEnd_800951 : Nat := 274181895799600672819333

theorem tailTrace_800951 : CollatzResearch.WordTrace tailWord_800951 prefixEnd_800951 274181895799600672819333 := by
  unfold tailWord_800951
  simp only [CollatzResearch.WordTrace]
  refine ⟨29213082921298793385378707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19475388614199195590252471 29213082921298793385378707)
  ·
    refine ⟨43819624381948190078068061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29213082921298793385378707 43819624381948190078068061)
    ·
      refine ⟨16432359143230571279275523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43819624381948190078068061 16432359143230571279275523)
      ·
        refine ⟨24648538714845856918913285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16432359143230571279275523 24648538714845856918913285)
        ·
          refine ⟨4621601009033598172296241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24648538714845856918913285 4621601009033598172296241)
          ·
            refine ⟨3466200756775198629222181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4621601009033598172296241 3466200756775198629222181)
            ·
              refine ⟨649912641895349742979159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3466200756775198629222181 649912641895349742979159)
              ·
                refine ⟨974868962843024614468739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 649912641895349742979159 974868962843024614468739)
                ·
                  refine ⟨1462303444264536921703109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 974868962843024614468739 1462303444264536921703109)
                  ·
                    refine ⟨274181895799600672819333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1462303444264536921703109 274181895799600672819333)
                    ·
                      rfl

theorem cell22_800951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 4, 1, 1, 4].length) (baseStart_800951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_800951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_800951 prefixEnd_800951 := by exact prefixLift 800951
  have htrace : WordTrace (prefixWord ++ tailWord_800951) baseStart_800951 baseEnd_800951 := by
    simpa [prefixWord, tailWord_800951, baseEnd_800951] using wordTrace_append hprefix tailTrace_800951
  have hstable : (prefixWord ++ tailWord_800951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800951).length < 2 ^ (prefixWord ++ tailWord_800951).sum := by decide
  have hdescent : baseEnd_800951 < baseStart_800951 := by decide
  rcases family_descends (prefixWord ++ tailWord_800951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800992 : List Nat := [2, 1, 1, 3, 1, 3, 1, 1, 2, 7]
def baseStart_800992 : Nat := 118140960795 + 800992 * 2 ^ 59
def prefixEnd_800992 : Nat := 4983230072969 + 3 ^ 40 * 800992 * 2
def baseEnd_800992 : Nat := 274195930937490232544207

theorem tailTrace_800992 : CollatzResearch.WordTrace tailWord_800992 prefixEnd_800992 274195930937490232544207 := by
  unfold tailWord_800992
  simp only [CollatzResearch.WordTrace]
  refine ⟨14607289157075128693810615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19476385542766838258414153 14607289157075128693810615)
  ·
    refine ⟨21910933735612693040715923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14607289157075128693810615 21910933735612693040715923)
    ·
      refine ⟨32866400603419039561073885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21910933735612693040715923 32866400603419039561073885)
      ·
        refine ⟨12324900226282139835402707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32866400603419039561073885 12324900226282139835402707)
        ·
          refine ⟨18487350339423209753104061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12324900226282139835402707 18487350339423209753104061)
          ·
            refine ⟨6932756377283703657414023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18487350339423209753104061 6932756377283703657414023)
            ·
              refine ⟨10399134565925555486121035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6932756377283703657414023 10399134565925555486121035)
              ·
                refine ⟨15598701848888333229181553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10399134565925555486121035 15598701848888333229181553)
                ·
                  refine ⟨11699026386666249921886165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15598701848888333229181553 11699026386666249921886165)
                  ·
                    refine ⟨274195930937490232544207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11699026386666249921886165 274195930937490232544207)
                    ·
                      rfl

theorem cell22_800992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 2, 7].length) (baseStart_800992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_800992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_800992 prefixEnd_800992 := by exact prefixLift 800992
  have htrace : WordTrace (prefixWord ++ tailWord_800992) baseStart_800992 baseEnd_800992 := by
    simpa [prefixWord, tailWord_800992, baseEnd_800992] using wordTrace_append hprefix tailTrace_800992
  have hstable : (prefixWord ++ tailWord_800992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800992).length < 2 ^ (prefixWord ++ tailWord_800992).sum := by decide
  have hdescent : baseEnd_800992 < baseStart_800992 := by decide
  rcases family_descends (prefixWord ++ tailWord_800992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801009 : List Nat := [1, 2, 2, 2, 2, 1, 2, 2, 5, 3]
def baseStart_801009 : Nat := 118140960795 + 801009 * 2 ^ 59
def prefixEnd_801009 : Nat := 4983230072969 + 3 ^ 40 * 801009 * 2
def baseEnd_801009 : Nat := 274201750384907854869155

theorem tailTrace_801009 : CollatzResearch.WordTrace tailWord_801009 prefixEnd_801009 274201750384907854869155 := by
  unfold tailWord_801009
  simp only [CollatzResearch.WordTrace]
  refine ⟨29215198355088669290990081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19476798903392446193993387 29215198355088669290990081)
  ·
    refine ⟨21911398766316501968242561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29215198355088669290990081 21911398766316501968242561)
    ·
      refine ⟨16433549074737376476181921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21911398766316501968242561 16433549074737376476181921)
      ·
        refine ⟨12325161806053032357136441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16433549074737376476181921 12325161806053032357136441)
        ·
          refine ⟨9243871354539774267852331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12325161806053032357136441 9243871354539774267852331)
          ·
            refine ⟨13865807031809661401778497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9243871354539774267852331 13865807031809661401778497)
            ·
              refine ⟨10399355273857246051333873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13865807031809661401778497 10399355273857246051333873)
              ·
                refine ⟨7799516455392934538500405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10399355273857246051333873 7799516455392934538500405)
                ·
                  refine ⟨731204667693087612984413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7799516455392934538500405 731204667693087612984413)
                  ·
                    refine ⟨274201750384907854869155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 731204667693087612984413 274201750384907854869155)
                    ·
                      rfl

theorem cell22_801009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 5, 3].length) (baseStart_801009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_801009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_801009 prefixEnd_801009 := by exact prefixLift 801009
  have htrace : WordTrace (prefixWord ++ tailWord_801009) baseStart_801009 baseEnd_801009 := by
    simpa [prefixWord, tailWord_801009, baseEnd_801009] using wordTrace_append hprefix tailTrace_801009
  have hstable : (prefixWord ++ tailWord_801009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801009).length < 2 ^ (prefixWord ++ tailWord_801009).sum := by decide
  have hdescent : baseEnd_801009 < baseStart_801009 := by decide
  rcases family_descends (prefixWord ++ tailWord_801009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801084 : List Nat := [2, 2, 2, 2, 1, 2, 2, 3, 6]
def baseStart_801084 : Nat := 118140960795 + 801084 * 2 ^ 59
def prefixEnd_801084 : Nat := 4983230072969 + 3 ^ 40 * 801084 * 2
def baseEnd_801084 : Nat := 91409141472544219747975

theorem tailTrace_801084 : CollatzResearch.WordTrace tailWord_801084 prefixEnd_801084 91409141472544219747975 := by
  unfold tailWord_801084
  simp only [CollatzResearch.WordTrace]
  refine ⟨14608966914908478549985153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19478622553211304733313537 14608966914908478549985153)
  ·
    refine ⟨10956725186181358912488865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14608966914908478549985153 10956725186181358912488865)
    ·
      refine ⟨8217543889636019184366649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10956725186181358912488865 8217543889636019184366649)
      ·
        refine ⟨6163157917227014388274987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8217543889636019184366649 6163157917227014388274987)
        ·
          refine ⟨9244736875840521582412481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6163157917227014388274987 9244736875840521582412481)
          ·
            refine ⟨6933552656880391186809361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9244736875840521582412481 6933552656880391186809361)
            ·
              refine ⟨5200164492660293390107021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6933552656880391186809361 5200164492660293390107021)
              ·
                refine ⟨1950061684747610021290133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5200164492660293390107021 1950061684747610021290133)
                ·
                  refine ⟨91409141472544219747975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1950061684747610021290133 91409141472544219747975)
                  ·
                    rfl

theorem cell22_801084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 3, 6].length) (baseStart_801084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_801084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_801084 prefixEnd_801084 := by exact prefixLift 801084
  have htrace : WordTrace (prefixWord ++ tailWord_801084) baseStart_801084 baseEnd_801084 := by
    simpa [prefixWord, tailWord_801084, baseEnd_801084] using wordTrace_append hprefix tailTrace_801084
  have hstable : (prefixWord ++ tailWord_801084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801084).length < 2 ^ (prefixWord ++ tailWord_801084).sum := by decide
  have hdescent : baseEnd_801084 < baseStart_801084 := by decide
  rcases family_descends (prefixWord ++ tailWord_801084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801086 : List Nat := [4, 2, 1, 2, 1, 2, 1, 2, 3, 4]
def baseStart_801086 : Nat := 118140960795 + 801086 * 2 ^ 59
def prefixEnd_801086 : Nat := 4983230072969 + 3 ^ 40 * 801086 * 2
def baseEnd_801086 : Nat := 274228109058505320693919

theorem tailTrace_801086 : CollatzResearch.WordTrace tailWord_801086 prefixEnd_801086 274228109058505320693919 := by
  unfold tailWord_801086
  simp only [CollatzResearch.WordTrace]
  refine ⟨3652250846976213930192889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19478671183873140961028741 3652250846976213930192889)
  ·
    refine ⟨2739188135232160447644667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3652250846976213930192889 2739188135232160447644667)
    ·
      refine ⟨4108782202848240671467001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2739188135232160447644667 4108782202848240671467001)
      ·
        refine ⟨3081586652136180503600251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4108782202848240671467001 3081586652136180503600251)
        ·
          refine ⟨4622379978204270755400377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3081586652136180503600251 4622379978204270755400377)
          ·
            refine ⟨3466784983653203066550283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4622379978204270755400377 3466784983653203066550283)
            ·
              refine ⟨5200177475479804599825425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3466784983653203066550283 5200177475479804599825425)
              ·
                refine ⟨3900133106609853449869069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5200177475479804599825425 3900133106609853449869069)
                ·
                  refine ⟨1462549914978695043700901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3900133106609853449869069 1462549914978695043700901)
                  ·
                    refine ⟨274228109058505320693919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1462549914978695043700901 274228109058505320693919)
                    ·
                      rfl

theorem cell22_801086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_801086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_801086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_801086 prefixEnd_801086 := by exact prefixLift 801086
  have htrace : WordTrace (prefixWord ++ tailWord_801086) baseStart_801086 baseEnd_801086 := by
    simpa [prefixWord, tailWord_801086, baseEnd_801086] using wordTrace_append hprefix tailTrace_801086
  have hstable : (prefixWord ++ tailWord_801086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801086).length < 2 ^ (prefixWord ++ tailWord_801086).sum := by decide
  have hdescent : baseEnd_801086 < baseStart_801086 := by decide
  rcases family_descends (prefixWord ++ tailWord_801086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801120 : List Nat := [2, 1, 1, 3, 5, 2, 2, 1, 1, 4]
def baseStart_801120 : Nat := 118140960795 + 801120 * 2 ^ 59
def prefixEnd_801120 : Nat := 4983230072969 + 3 ^ 40 * 801120 * 2
def baseEnd_801120 : Nat := 274239747953340565343815

theorem tailTrace_801120 : CollatzResearch.WordTrace tailWord_801120 prefixEnd_801120 274239747953340565343815 := by
  unfold tailWord_801120
  simp only [CollatzResearch.WordTrace]
  refine ⟨14609623428843267624140407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19479497905124356832187209 14609623428843267624140407)
  ·
    refine ⟨21914435143264901436210611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14609623428843267624140407 21914435143264901436210611)
    ·
      refine ⟨32871652714897352154315917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21914435143264901436210611 32871652714897352154315917)
      ·
        refine ⟨12326869768086507057868469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32871652714897352154315917 12326869768086507057868469)
        ·
          refine ⟨1155644040758110036675169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12326869768086507057868469 1155644040758110036675169)
          ·
            refine ⟨866733030568582527506377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1155644040758110036675169 866733030568582527506377)
            ·
              refine ⟨650049772926436895629783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 866733030568582527506377 650049772926436895629783)
              ·
                refine ⟨975074659389655343444675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 650049772926436895629783 975074659389655343444675)
                ·
                  refine ⟨1462611989084483015167013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 975074659389655343444675 1462611989084483015167013)
                  ·
                    refine ⟨274239747953340565343815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1462611989084483015167013 274239747953340565343815)
                    ·
                      rfl

theorem cell22_801120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 2, 1, 1, 4].length) (baseStart_801120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_801120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_801120 prefixEnd_801120 := by exact prefixLift 801120
  have htrace : WordTrace (prefixWord ++ tailWord_801120) baseStart_801120 baseEnd_801120 := by
    simpa [prefixWord, tailWord_801120, baseEnd_801120] using wordTrace_append hprefix tailTrace_801120
  have hstable : (prefixWord ++ tailWord_801120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801120).length < 2 ^ (prefixWord ++ tailWord_801120).sum := by decide
  have hdescent : baseEnd_801120 < baseStart_801120 := by decide
  rcases family_descends (prefixWord ++ tailWord_801120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801191 : List Nat := [1, 1, 6, 1, 1, 2, 2, 1, 7]
def baseStart_801191 : Nat := 118140960795 + 801191 * 2 ^ 59
def prefixEnd_801191 : Nat := 4983230072969 + 3 ^ 40 * 801191 * 2
def baseEnd_801191 : Nat := 91421350901440015606199

theorem tailTrace_801191 : CollatzResearch.WordTrace tailWord_801191 prefixEnd_801191 91421350901440015606199 := by
  unfold tailWord_801191
  simp only [CollatzResearch.WordTrace]
  refine ⟨29221836440429314374115427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19481224293619542916076951 29221836440429314374115427)
  ·
    refine ⟨43832754660643971561173141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29221836440429314374115427 43832754660643971561173141)
    ·
      refine ⟨2054660374717686166929991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 43832754660643971561173141 2054660374717686166929991)
      ·
        refine ⟨3081990562076529250394987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2054660374717686166929991 3081990562076529250394987)
        ·
          refine ⟨4622985843114793875592481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3081990562076529250394987 4622985843114793875592481)
          ·
            refine ⟨3467239382336095406694361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4622985843114793875592481 3467239382336095406694361)
            ·
              refine ⟨2600429536752071555020771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3467239382336095406694361 2600429536752071555020771)
              ·
                refine ⟨3900644305128107332531157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2600429536752071555020771 3900644305128107332531157)
                ·
                  refine ⟨91421350901440015606199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3900644305128107332531157 91421350901440015606199)
                  ·
                    rfl

theorem cell22_801191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 1, 7].length) (baseStart_801191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_801191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_801191 prefixEnd_801191 := by exact prefixLift 801191
  have htrace : WordTrace (prefixWord ++ tailWord_801191) baseStart_801191 baseEnd_801191 := by
    simpa [prefixWord, tailWord_801191, baseEnd_801191] using wordTrace_append hprefix tailTrace_801191
  have hstable : (prefixWord ++ tailWord_801191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801191).length < 2 ^ (prefixWord ++ tailWord_801191).sum := by decide
  have hdescent : baseEnd_801191 < baseStart_801191 := by decide
  rcases family_descends (prefixWord ++ tailWord_801191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801219 : List Nat := [1, 1, 1, 3, 1, 1, 3, 3, 8]
def baseStart_801219 : Nat := 118140960795 + 801219 * 2 ^ 59
def prefixEnd_801219 : Nat := 4983230072969 + 3 ^ 40 * 801219 * 2
def baseEnd_801219 : Nat := 91424545892179102372837

theorem tailTrace_801219 : CollatzResearch.WordTrace tailWord_801219 prefixEnd_801219 91424545892179102372837 := by
  unfold tailWord_801219
  simp only [CollatzResearch.WordTrace]
  refine ⟨29222857684327875156134711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19481905122885250104089807 29222857684327875156134711)
  ·
    refine ⟨43834286526491812734202067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29222857684327875156134711 43834286526491812734202067)
    ·
      refine ⟨65751429789737719101303101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43834286526491812734202067 65751429789737719101303101)
      ·
        refine ⟨24656786171151644662988663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65751429789737719101303101 24656786171151644662988663)
        ·
          refine ⟨36985179256727466994482995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24656786171151644662988663 36985179256727466994482995)
          ·
            refine ⟨55477768885091200491724493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36985179256727466994482995 55477768885091200491724493)
            ·
              refine ⟨20804163331909200184396685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55477768885091200491724493 20804163331909200184396685)
              ·
                refine ⟨7801561249465950069148757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20804163331909200184396685 7801561249465950069148757)
                ·
                  refine ⟨91424545892179102372837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7801561249465950069148757 91424545892179102372837)
                  ·
                    rfl

theorem cell22_801219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 8].length) (baseStart_801219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_801219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_801219 prefixEnd_801219 := by exact prefixLift 801219
  have htrace : WordTrace (prefixWord ++ tailWord_801219) baseStart_801219 baseEnd_801219 := by
    simpa [prefixWord, tailWord_801219, baseEnd_801219] using wordTrace_append hprefix tailTrace_801219
  have hstable : (prefixWord ++ tailWord_801219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801219).length < 2 ^ (prefixWord ++ tailWord_801219).sum := by decide
  have hdescent : baseEnd_801219 < baseStart_801219 := by decide
  rcases family_descends (prefixWord ++ tailWord_801219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801319 : List Nat := [1, 1, 7, 2, 2, 1, 1, 1, 1, 5]
def baseStart_801319 : Nat := 118140960795 + 801319 * 2 ^ 59
def prefixEnd_801319 : Nat := 4983230072969 + 3 ^ 40 * 801319 * 2
def baseEnd_801319 : Nat := 274307869720170379618205

theorem tailTrace_801319 : CollatzResearch.WordTrace tailWord_801319 prefixEnd_801319 274307869720170379618205 := by
  unfold tailWord_801319
  simp only [CollatzResearch.WordTrace]
  refine ⟨29226504983965592234775011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19484336655977061489850007 29226504983965592234775011)
  ·
    refine ⟨43839757475948388352162517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29226504983965592234775011 43839757475948388352162517)
    ·
      refine ⟨1027494315842540352003809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 43839757475948388352162517 1027494315842540352003809)
      ·
        refine ⟨770620736881905264002857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1027494315842540352003809 770620736881905264002857)
        ·
          refine ⟨577965552661428948002143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 770620736881905264002857 577965552661428948002143)
          ·
            refine ⟨866948328992143422003215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 577965552661428948002143 866948328992143422003215)
            ·
              refine ⟨1300422493488215133004823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 866948328992143422003215 1300422493488215133004823)
              ·
                refine ⟨1950633740232322699507235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1300422493488215133004823 1950633740232322699507235)
                ·
                  refine ⟨2925950610348484049260853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1950633740232322699507235 2925950610348484049260853)
                  ·
                    refine ⟨274307869720170379618205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2925950610348484049260853 274307869720170379618205)
                    ·
                      rfl

theorem cell22_801319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_801319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_801319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_801319 prefixEnd_801319 := by exact prefixLift 801319
  have htrace : WordTrace (prefixWord ++ tailWord_801319) baseStart_801319 baseEnd_801319 := by
    simpa [prefixWord, tailWord_801319, baseEnd_801319] using wordTrace_append hprefix tailTrace_801319
  have hstable : (prefixWord ++ tailWord_801319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801319).length < 2 ^ (prefixWord ++ tailWord_801319).sum := by decide
  have hdescent : baseEnd_801319 < baseStart_801319 := by decide
  rcases family_descends (prefixWord ++ tailWord_801319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801364 : List Nat := [2, 4, 1, 1, 1, 4, 3, 2, 1, 3]
def baseStart_801364 : Nat := 118140960795 + 801364 * 2 ^ 59
def prefixEnd_801364 : Nat := 4983230072969 + 3 ^ 40 * 801364 * 2
def baseEnd_801364 : Nat := 274323274139805262243067

theorem tailTrace_801364 : CollatzResearch.WordTrace tailWord_801364 prefixEnd_801364 274323274139805262243067 := by
  unfold tailWord_801364
  simp only [CollatzResearch.WordTrace]
  refine ⟨14614073134401282460081573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19485430845868376613442097 14614073134401282460081573)
  ·
    refine ⟨2740138712700240461265295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14614073134401282460081573 2740138712700240461265295)
    ·
      refine ⟨4110208069050360691897943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2740138712700240461265295 4110208069050360691897943)
      ·
        refine ⟨6165312103575541037846915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4110208069050360691897943 6165312103575541037846915)
        ·
          refine ⟨9247968155363311556770373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6165312103575541037846915 9247968155363311556770373)
          ·
            refine ⟨1733994029130620916894445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9247968155363311556770373 1733994029130620916894445)
            ·
              refine ⟨650247760923982843835417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1733994029130620916894445 650247760923982843835417)
              ·
                refine ⟨487685820692987132876563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 650247760923982843835417 487685820692987132876563)
                ·
                  refine ⟨731528731039480699314845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 487685820692987132876563 731528731039480699314845)
                  ·
                    refine ⟨274323274139805262243067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 731528731039480699314845 274323274139805262243067)
                    ·
                      rfl

theorem cell22_801364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 3, 2, 1, 3].length) (baseStart_801364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_801364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_801364 prefixEnd_801364 := by exact prefixLift 801364
  have htrace : WordTrace (prefixWord ++ tailWord_801364) baseStart_801364 baseEnd_801364 := by
    simpa [prefixWord, tailWord_801364, baseEnd_801364] using wordTrace_append hprefix tailTrace_801364
  have hstable : (prefixWord ++ tailWord_801364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801364).length < 2 ^ (prefixWord ++ tailWord_801364).sum := by decide
  have hdescent : baseEnd_801364 < baseStart_801364 := by decide
  rcases family_descends (prefixWord ++ tailWord_801364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801390 : List Nat := [4, 1, 2, 2, 2, 2, 1, 1, 3, 4]
def baseStart_801390 : Nat := 118140960795 + 801390 * 2 ^ 59
def prefixEnd_801390 : Nat := 4983230072969 + 3 ^ 40 * 801390 * 2
def baseEnd_801390 : Nat := 274332174471149861092987

theorem tailTrace_801390 : CollatzResearch.WordTrace tailWord_801390 prefixEnd_801390 274332174471149861092987 := by
  unfold tailWord_801390
  simp only [CollatzResearch.WordTrace]
  refine ⟨3653636820838546420076203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19486063044472247573739749 3653636820838546420076203)
  ·
    refine ⟨5480455231257819630114305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3653636820838546420076203 5480455231257819630114305)
    ·
      refine ⟨4110341423443364722585729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5480455231257819630114305 4110341423443364722585729)
      ·
        refine ⟨3082756067582523541939297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4110341423443364722585729 3082756067582523541939297)
        ·
          refine ⟨2312067050686892656454473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3082756067582523541939297 2312067050686892656454473)
          ·
            refine ⟨1734050288015169492340855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2312067050686892656454473 1734050288015169492340855)
            ·
              refine ⟨2601075432022754238511283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1734050288015169492340855 2601075432022754238511283)
              ·
                refine ⟨3901613148034131357766925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2601075432022754238511283 3901613148034131357766925)
                ·
                  refine ⟨1463104930512799259162597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3901613148034131357766925 1463104930512799259162597)
                  ·
                    refine ⟨274332174471149861092987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1463104930512799259162597 274332174471149861092987)
                    ·
                      rfl

theorem cell22_801390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_801390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_801390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_801390 prefixEnd_801390 := by exact prefixLift 801390
  have htrace : WordTrace (prefixWord ++ tailWord_801390) baseStart_801390 baseEnd_801390 := by
    simpa [prefixWord, tailWord_801390, baseEnd_801390] using wordTrace_append hprefix tailTrace_801390
  have hstable : (prefixWord ++ tailWord_801390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801390).length < 2 ^ (prefixWord ++ tailWord_801390).sum := by decide
  have hdescent : baseEnd_801390 < baseStart_801390 := by decide
  rcases family_descends (prefixWord ++ tailWord_801390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801403 : List Nat := [1, 1, 1, 1, 1, 4, 2, 4, 4, 3]
def baseStart_801403 : Nat := 118140960795 + 801403 * 2 ^ 59
def prefixEnd_801403 : Nat := 4983230072969 + 3 ^ 40 * 801403 * 2
def baseEnd_801403 : Nat := 274336624636822160517947

theorem tailTrace_801403 : CollatzResearch.WordTrace tailWord_801403 prefixEnd_801403 274336624636822160517947 := by
  unfold tailWord_801403
  simp only [CollatzResearch.WordTrace]
  refine ⟨29229568715661274580832863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19486379143774183053888575 29229568715661274580832863)
  ·
    refine ⟨43844353073491911871249295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29229568715661274580832863 43844353073491911871249295)
    ·
      refine ⟨65766529610237867806873943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43844353073491911871249295 65766529610237867806873943)
      ·
        refine ⟨98649794415356801710310915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65766529610237867806873943 98649794415356801710310915)
        ·
          refine ⟨147974691623035202565466373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98649794415356801710310915 147974691623035202565466373)
          ·
            refine ⟨27745254679319100481024945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 147974691623035202565466373 27745254679319100481024945)
            ·
              refine ⟨20808941009489325360768709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27745254679319100481024945 20808941009489325360768709)
              ·
                refine ⟨3901676439279248505144133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20808941009489325360768709 3901676439279248505144133)
                ·
                  refine ⟨731564332364859094714525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3901676439279248505144133 731564332364859094714525)
                  ·
                    refine ⟨274336624636822160517947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 731564332364859094714525 274336624636822160517947)
                    ·
                      rfl

theorem cell22_801403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4, 4, 3].length) (baseStart_801403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_801403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_801403 prefixEnd_801403 := by exact prefixLift 801403
  have htrace : WordTrace (prefixWord ++ tailWord_801403) baseStart_801403 baseEnd_801403 := by
    simpa [prefixWord, tailWord_801403, baseEnd_801403] using wordTrace_append hprefix tailTrace_801403
  have hstable : (prefixWord ++ tailWord_801403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801403).length < 2 ^ (prefixWord ++ tailWord_801403).sum := by decide
  have hdescent : baseEnd_801403 < baseStart_801403 := by decide
  rcases family_descends (prefixWord ++ tailWord_801403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801416 : List Nat := [2, 1, 3, 16]
def baseStart_801416 : Nat := 118140960795 + 801416 * 2 ^ 59
def prefixEnd_801416 : Nat := 4983230072969 + 3 ^ 40 * 801416 * 2
def baseEnd_801416 : Nat := 376325205490390205683

theorem tailTrace_801416 : CollatzResearch.WordTrace tailWord_801416 prefixEnd_801416 376325205490390205683 := by
  unfold tailWord_801416
  simp only [CollatzResearch.WordTrace]
  refine ⟨14615021432307088900528051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19486695243076118534037401 14615021432307088900528051)
  ·
    refine ⟨21922532148460633350792077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14615021432307088900528051 21922532148460633350792077)
    ·
      refine ⟨8220949555672737506547029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21922532148460633350792077 8220949555672737506547029)
      ·
        refine ⟨376325205490390205683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 16 8220949555672737506547029 376325205490390205683)
        ·
          rfl

theorem cell22_801416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 16].length) (baseStart_801416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_801416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_801416 prefixEnd_801416 := by exact prefixLift 801416
  have htrace : WordTrace (prefixWord ++ tailWord_801416) baseStart_801416 baseEnd_801416 := by
    simpa [prefixWord, tailWord_801416, baseEnd_801416] using wordTrace_append hprefix tailTrace_801416
  have hstable : (prefixWord ++ tailWord_801416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801416).length < 2 ^ (prefixWord ++ tailWord_801416).sum := by decide
  have hdescent : baseEnd_801416 < baseStart_801416 := by decide
  rcases family_descends (prefixWord ++ tailWord_801416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801482 : List Nat := [3, 1, 2, 1, 4, 2, 2, 1, 3, 3]
def baseStart_801482 : Nat := 118140960795 + 801482 * 2 ^ 59
def prefixEnd_801482 : Nat := 4983230072969 + 3 ^ 40 * 801482 * 2
def baseEnd_801482 : Nat := 274363667951292287792705

theorem tailTrace_801482 : CollatzResearch.WordTrace tailWord_801482 prefixEnd_801482 274363667951292287792705 := by
  unfold tailWord_801482
  simp only [CollatzResearch.WordTrace]
  refine ⟨7308112520593767768239675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19488300054916714048639133 7308112520593767768239675)
  ·
    refine ⟨10962168780890651652359513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7308112520593767768239675 10962168780890651652359513)
    ·
      refine ⟨8221626585667988739269635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10962168780890651652359513 8221626585667988739269635)
      ·
        refine ⟨12332439878501983108904453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8221626585667988739269635 12332439878501983108904453)
        ·
          refine ⟨2312332477219121832919585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12332439878501983108904453 2312332477219121832919585)
          ·
            refine ⟨1734249357914341374689689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2312332477219121832919585 1734249357914341374689689)
            ·
              refine ⟨1300687018435756031017267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1734249357914341374689689 1300687018435756031017267)
              ·
                refine ⟨1951030527653634046525901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1300687018435756031017267 1951030527653634046525901)
                ·
                  refine ⟨731636447870112767447213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1951030527653634046525901 731636447870112767447213)
                  ·
                    refine ⟨274363667951292287792705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 731636447870112767447213 274363667951292287792705)
                    ·
                      rfl

theorem cell22_801482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 1, 3, 3].length) (baseStart_801482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_801482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_801482 prefixEnd_801482 := by exact prefixLift 801482
  have htrace : WordTrace (prefixWord ++ tailWord_801482) baseStart_801482 baseEnd_801482 := by
    simpa [prefixWord, tailWord_801482, baseEnd_801482] using wordTrace_append hprefix tailTrace_801482
  have hstable : (prefixWord ++ tailWord_801482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801482).length < 2 ^ (prefixWord ++ tailWord_801482).sum := by decide
  have hdescent : baseEnd_801482 < baseStart_801482 := by decide
  rcases family_descends (prefixWord ++ tailWord_801482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801553 : List Nat := [1, 2, 2, 1, 1, 3, 2, 1, 3, 6]
def baseStart_801553 : Nat := 118140960795 + 801553 * 2 ^ 59
def prefixEnd_801553 : Nat := 4983230072969 + 3 ^ 40 * 801553 * 2
def baseEnd_801553 : Nat := 274387972702271769267487

theorem tailTrace_801553 : CollatzResearch.WordTrace tailWord_801553 prefixEnd_801553 274387972702271769267487 := by
  unfold tailWord_801553
  simp only [CollatzResearch.WordTrace]
  refine ⟨29235039665117850198793313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19490026443411900132528875 29235039665117850198793313)
  ·
    refine ⟨21926279748838387649094985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29235039665117850198793313 21926279748838387649094985)
    ·
      refine ⟨16444709811628790736821239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21926279748838387649094985 16444709811628790736821239)
      ·
        refine ⟨24667064717443186105231859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16444709811628790736821239 24667064717443186105231859)
        ·
          refine ⟨37000597076164779157847789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24667064717443186105231859 37000597076164779157847789)
          ·
            refine ⟨13875223903561792184192921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37000597076164779157847789 13875223903561792184192921)
            ·
              refine ⟨10406417927671344138144691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13875223903561792184192921 10406417927671344138144691)
              ·
                refine ⟨15609626891507016207217037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10406417927671344138144691 15609626891507016207217037)
                ·
                  refine ⟨5853610084315131077706389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15609626891507016207217037 5853610084315131077706389)
                  ·
                    refine ⟨274387972702271769267487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5853610084315131077706389 274387972702271769267487)
                    ·
                      rfl

theorem cell22_801553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 6].length) (baseStart_801553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_801553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_801553 prefixEnd_801553 := by exact prefixLift 801553
  have htrace : WordTrace (prefixWord ++ tailWord_801553) baseStart_801553 baseEnd_801553 := by
    simpa [prefixWord, tailWord_801553, baseEnd_801553] using wordTrace_append hprefix tailTrace_801553
  have hstable : (prefixWord ++ tailWord_801553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801553).length < 2 ^ (prefixWord ++ tailWord_801553).sum := by decide
  have hdescent : baseEnd_801553 < baseStart_801553 := by decide
  rcases family_descends (prefixWord ++ tailWord_801553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801559 : List Nat := [1, 1, 3, 4, 3, 2, 1, 2, 1, 4]
def baseStart_801559 : Nat := 118140960795 + 801559 * 2 ^ 59
def prefixEnd_801559 : Nat := 4983230072969 + 3 ^ 40 * 801559 * 2
def baseEnd_801559 : Nat := 274390026624889753617469

theorem tailTrace_801559 : CollatzResearch.WordTrace tailWord_801559 prefixEnd_801559 274390026624889753617469 := by
  unfold tailWord_801559
  simp only [CollatzResearch.WordTrace]
  refine ⟨29235258503096113223511731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19490172335397408815674487 29235258503096113223511731)
  ·
    refine ⟨43852887754644169835267597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29235258503096113223511731 43852887754644169835267597)
    ·
      refine ⟨16444832907991563688225349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43852887754644169835267597 16444832907991563688225349)
      ·
        refine ⟨3083406170248418191542253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16444832907991563688225349 3083406170248418191542253)
        ·
          refine ⟨1156277313843156821828345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3083406170248418191542253 1156277313843156821828345)
          ·
            refine ⟨867207985382367616371259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1156277313843156821828345 867207985382367616371259)
            ·
              refine ⟨1300811978073551424556889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 867207985382367616371259 1300811978073551424556889)
              ·
                refine ⟨975608983555163568417667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1300811978073551424556889 975608983555163568417667)
                ·
                  refine ⟨1463413475332745352626501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 975608983555163568417667 1463413475332745352626501)
                  ·
                    refine ⟨274390026624889753617469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1463413475332745352626501 274390026624889753617469)
                    ·
                      rfl

theorem cell22_801559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 2, 1, 4].length) (baseStart_801559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_801559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_801559 prefixEnd_801559 := by exact prefixLift 801559
  have htrace : WordTrace (prefixWord ++ tailWord_801559) baseStart_801559 baseEnd_801559 := by
    simpa [prefixWord, tailWord_801559, baseEnd_801559] using wordTrace_append hprefix tailTrace_801559
  have hstable : (prefixWord ++ tailWord_801559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801559).length < 2 ^ (prefixWord ++ tailWord_801559).sum := by decide
  have hdescent : baseEnd_801559 < baseStart_801559 := by decide
  rcases family_descends (prefixWord ++ tailWord_801559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801572 : List Nat := [2, 3, 1, 3, 3, 1, 1, 2, 1, 5]
def baseStart_801572 : Nat := 118140960795 + 801572 * 2 ^ 59
def prefixEnd_801572 : Nat := 4983230072969 + 3 ^ 40 * 801572 * 2
def baseEnd_801572 : Nat := 274394476790562053042429

theorem tailTrace_801572 : CollatzResearch.WordTrace tailWord_801572 prefixEnd_801572 274394476790562053042429 := by
  unfold tailWord_801572
  simp only [CollatzResearch.WordTrace]
  refine ⟨14617866326024508221867485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19490488434699344295823313 14617866326024508221867485)
  ·
    refine ⟨5481699872259190583200307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14617866326024508221867485 5481699872259190583200307)
    ·
      refine ⟨8222549808388785874800461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5481699872259190583200307 8222549808388785874800461)
      ·
        refine ⟨3083456178145794703050173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8222549808388785874800461 3083456178145794703050173)
        ·
          refine ⟨1156296066804673013643815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3083456178145794703050173 1156296066804673013643815)
          ·
            refine ⟨1734444100207009520465723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1156296066804673013643815 1734444100207009520465723)
            ·
              refine ⟨2601666150310514280698585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1734444100207009520465723 2601666150310514280698585)
              ·
                refine ⟨1951249612732885710523939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2601666150310514280698585 1951249612732885710523939)
                ·
                  refine ⟨2926874419099328565785909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1951249612732885710523939 2926874419099328565785909)
                  ·
                    refine ⟨274394476790562053042429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2926874419099328565785909 274394476790562053042429)
                    ·
                      rfl

theorem cell22_801572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 2, 1, 5].length) (baseStart_801572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_801572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_801572 prefixEnd_801572 := by exact prefixLift 801572
  have htrace : WordTrace (prefixWord ++ tailWord_801572) baseStart_801572 baseEnd_801572 := by
    simpa [prefixWord, tailWord_801572, baseEnd_801572] using wordTrace_append hprefix tailTrace_801572
  have hstable : (prefixWord ++ tailWord_801572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801572).length < 2 ^ (prefixWord ++ tailWord_801572).sum := by decide
  have hdescent : baseEnd_801572 < baseStart_801572 := by decide
  rcases family_descends (prefixWord ++ tailWord_801572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801589 : List Nat := [1, 3, 3, 1, 3, 2, 2, 2, 2, 3]
def baseStart_801589 : Nat := 118140960795 + 801589 * 2 ^ 59
def prefixEnd_801589 : Nat := 4983230072969 + 3 ^ 40 * 801589 * 2
def baseEnd_801589 : Nat := 274400296237979675367377

theorem tailTrace_801589 : CollatzResearch.WordTrace tailWord_801589 prefixEnd_801589 274400296237979675367377 := by
  unfold tailWord_801589
  simp only [CollatzResearch.WordTrace]
  refine ⟨29236352692987428347103821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19490901795324952231402547 29236352692987428347103821)
  ·
    refine ⟨10963632259870285630163933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29236352692987428347103821 10963632259870285630163933)
    ·
      refine ⟨4111362097451357111311475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10963632259870285630163933 4111362097451357111311475)
      ·
        refine ⟨6167043146177035666967213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4111362097451357111311475 6167043146177035666967213)
        ·
          refine ⟨2312641179816388375112705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6167043146177035666967213 2312641179816388375112705)
          ·
            refine ⟨1734480884862291281334529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2312641179816388375112705 1734480884862291281334529)
            ·
              refine ⟨1300860663646718461000897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1734480884862291281334529 1300860663646718461000897)
              ·
                refine ⟨975645497735038845750673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1300860663646718461000897 975645497735038845750673)
                ·
                  refine ⟨731734123301279134313005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 975645497735038845750673 731734123301279134313005)
                  ·
                    refine ⟨274400296237979675367377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 731734123301279134313005 274400296237979675367377)
                    ·
                      rfl

theorem cell22_801589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 2, 2, 3].length) (baseStart_801589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_801589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_801589 prefixEnd_801589 := by exact prefixLift 801589
  have htrace : WordTrace (prefixWord ++ tailWord_801589) baseStart_801589 baseEnd_801589 := by
    simpa [prefixWord, tailWord_801589, baseEnd_801589] using wordTrace_append hprefix tailTrace_801589
  have hstable : (prefixWord ++ tailWord_801589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801589).length < 2 ^ (prefixWord ++ tailWord_801589).sum := by decide
  have hdescent : baseEnd_801589 < baseStart_801589 := by decide
  rcases family_descends (prefixWord ++ tailWord_801589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801600 : List Nat := [2, 1, 1, 2, 2, 1, 1, 2, 7, 3]
def baseStart_801600 : Nat := 118140960795 + 801600 * 2 ^ 59
def prefixEnd_801600 : Nat := 4983230072969 + 3 ^ 40 * 801600 * 2
def baseEnd_801600 : Nat := 274404061762779313342343

theorem tailTrace_801600 : CollatzResearch.WordTrace tailWord_801600 prefixEnd_801600 274404061762779313342343 := by
  unfold tailWord_801600
  simp only [CollatzResearch.WordTrace]
  refine ⟨14618376947973788612877127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19491169263965051483836169 14618376947973788612877127)
  ·
    refine ⟨21927565421960682919315691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14618376947973788612877127 21927565421960682919315691)
    ·
      refine ⟨32891348132941024378973537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21927565421960682919315691 32891348132941024378973537)
      ·
        refine ⟨24668511099705768284230153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32891348132941024378973537 24668511099705768284230153)
        ·
          refine ⟨18501383324779326213172615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24668511099705768284230153 18501383324779326213172615)
          ·
            refine ⟨27752074987168989319758923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18501383324779326213172615 27752074987168989319758923)
            ·
              refine ⟨41628112480753483979638385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27752074987168989319758923 41628112480753483979638385)
              ·
                refine ⟨31221084360565112984728789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41628112480753483979638385 31221084360565112984728789)
                ·
                  refine ⟨731744164700744835579581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 31221084360565112984728789 731744164700744835579581)
                  ·
                    refine ⟨274404061762779313342343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 731744164700744835579581 274404061762779313342343)
                    ·
                      rfl

theorem cell22_801600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 7, 3].length) (baseStart_801600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_801600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_801600 prefixEnd_801600 := by exact prefixLift 801600
  have htrace : WordTrace (prefixWord ++ tailWord_801600) baseStart_801600 baseEnd_801600 := by
    simpa [prefixWord, tailWord_801600, baseEnd_801600] using wordTrace_append hprefix tailTrace_801600
  have hstable : (prefixWord ++ tailWord_801600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801600).length < 2 ^ (prefixWord ++ tailWord_801600).sum := by decide
  have hdescent : baseEnd_801600 < baseStart_801600 := by decide
  rcases family_descends (prefixWord ++ tailWord_801600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801606 : List Nat := [6, 1, 1, 2, 2, 1, 2, 1, 1, 5]
def baseStart_801606 : Nat := 118140960795 + 801606 * 2 ^ 59
def prefixEnd_801606 : Nat := 4983230072969 + 3 ^ 40 * 801606 * 2
def baseEnd_801606 : Nat := 274406115685397297692325

theorem tailTrace_801606 : CollatzResearch.WordTrace tailWord_801606 prefixEnd_801606 274406115685397297692325 := by
  unfold tailWord_801606
  simp only [CollatzResearch.WordTrace]
  refine ⟨913655397935182507827271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 19491315155950560166981781 913655397935182507827271)
  ·
    refine ⟨1370483096902773761740907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 913655397935182507827271 1370483096902773761740907)
    ·
      refine ⟨2055724645354160642611361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1370483096902773761740907 2055724645354160642611361)
      ·
        refine ⟨1541793484015620481958521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2055724645354160642611361 1541793484015620481958521)
        ·
          refine ⟨1156345113011715361468891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1541793484015620481958521 1156345113011715361468891)
          ·
            refine ⟨1734517669517573042203337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1156345113011715361468891 1734517669517573042203337)
            ·
              refine ⟨1300888252138179781652503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1734517669517573042203337 1300888252138179781652503)
              ·
                refine ⟨1951332378207269672478755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1300888252138179781652503 1951332378207269672478755)
                ·
                  refine ⟨2926998567310904508718133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1951332378207269672478755 2926998567310904508718133)
                  ·
                    refine ⟨274406115685397297692325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2926998567310904508718133 274406115685397297692325)
                    ·
                      rfl

theorem cell22_801606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_801606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_801606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_801606 prefixEnd_801606 := by exact prefixLift 801606
  have htrace : WordTrace (prefixWord ++ tailWord_801606) baseStart_801606 baseEnd_801606 := by
    simpa [prefixWord, tailWord_801606, baseEnd_801606] using wordTrace_append hprefix tailTrace_801606
  have hstable : (prefixWord ++ tailWord_801606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801606).length < 2 ^ (prefixWord ++ tailWord_801606).sum := by decide
  have hdescent : baseEnd_801606 < baseStart_801606 := by decide
  rcases family_descends (prefixWord ++ tailWord_801606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801660 : List Nat := [2, 2, 2, 1, 1, 1, 1, 3, 5, 4]
def baseStart_801660 : Nat := 118140960795 + 801660 * 2 ^ 59
def prefixEnd_801660 : Nat := 4983230072969 + 3 ^ 40 * 801660 * 2
def baseEnd_801660 : Nat := 274424600988959156842159

theorem tailTrace_801660 : CollatzResearch.WordTrace tailWord_801660 prefixEnd_801660 274424600988959156842159 := by
  unfold tailWord_801660
  simp only [CollatzResearch.WordTrace]
  refine ⟨14619471137865103736469217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19492628183820138315292289 14619471137865103736469217)
  ·
    refine ⟨10964603353398827802351913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14619471137865103736469217 10964603353398827802351913)
    ·
      refine ⟨8223452515049120851763935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10964603353398827802351913 8223452515049120851763935)
      ·
        refine ⟨12335178772573681277645903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8223452515049120851763935 12335178772573681277645903)
        ·
          refine ⟨18502768158860521916468855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12335178772573681277645903 18502768158860521916468855)
          ·
            refine ⟨27754152238290782874703283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18502768158860521916468855 27754152238290782874703283)
            ·
              refine ⟨41631228357436174312054925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27754152238290782874703283 41631228357436174312054925)
              ·
                refine ⟨15611710634038565367020597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41631228357436174312054925 15611710634038565367020597)
                ·
                  refine ⟨1463597871941115503158181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15611710634038565367020597 1463597871941115503158181)
                  ·
                    refine ⟨274424600988959156842159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1463597871941115503158181 274424600988959156842159)
                    ·
                      rfl

theorem cell22_801660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 5, 4].length) (baseStart_801660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_801660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_801660 prefixEnd_801660 := by exact prefixLift 801660
  have htrace : WordTrace (prefixWord ++ tailWord_801660) baseStart_801660 baseEnd_801660 := by
    simpa [prefixWord, tailWord_801660, baseEnd_801660] using wordTrace_append hprefix tailTrace_801660
  have hstable : (prefixWord ++ tailWord_801660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801660).length < 2 ^ (prefixWord ++ tailWord_801660).sum := by decide
  have hdescent : baseEnd_801660 < baseStart_801660 := by decide
  rcases family_descends (prefixWord ++ tailWord_801660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801675 : List Nat := [1, 1, 1, 1, 4, 2, 4, 2, 6]
def baseStart_801675 : Nat := 118140960795 + 801675 * 2 ^ 59
def prefixEnd_801675 : Nat := 4983230072969 + 3 ^ 40 * 801675 * 2
def baseEnd_801675 : Nat := 91476578598501372572371

theorem tailTrace_801675 : CollatzResearch.WordTrace tailWord_801675 prefixEnd_801675 91476578598501372572371 := by
  unfold tailWord_801675
  simp only [CollatzResearch.WordTrace]
  refine ⟨29239489370675865034734479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19492992913783910023156319 29239489370675865034734479)
  ·
    refine ⟨43859234056013797552101719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29239489370675865034734479 43859234056013797552101719)
    ·
      refine ⟨65788851084020696328152579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43859234056013797552101719 65788851084020696328152579)
      ·
        refine ⟨98683276626031044492228869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65788851084020696328152579 98683276626031044492228869)
        ·
          refine ⟨18503114367380820842292913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98683276626031044492228869 18503114367380820842292913)
          ·
            refine ⟨13877335775535615631719685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18503114367380820842292913 13877335775535615631719685)
            ·
              refine ⟨2602000457912927930947441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13877335775535615631719685 2602000457912927930947441)
              ·
                refine ⟨1951500343434695948210581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2602000457912927930947441 1951500343434695948210581)
                ·
                  refine ⟨91476578598501372572371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1951500343434695948210581 91476578598501372572371)
                  ·
                    rfl

theorem cell22_801675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 2, 6].length) (baseStart_801675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_801675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_801675 prefixEnd_801675 := by exact prefixLift 801675
  have htrace : WordTrace (prefixWord ++ tailWord_801675) baseStart_801675 baseEnd_801675 := by
    simpa [prefixWord, tailWord_801675, baseEnd_801675] using wordTrace_append hprefix tailTrace_801675
  have hstable : (prefixWord ++ tailWord_801675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801675).length < 2 ^ (prefixWord ++ tailWord_801675).sum := by decide
  have hdescent : baseEnd_801675 < baseStart_801675 := by decide
  rcases family_descends (prefixWord ++ tailWord_801675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801720 : List Nat := [2, 1, 2, 1, 2, 4, 1, 9]
def baseStart_801720 : Nat := 118140960795 + 801720 * 2 ^ 59
def prefixEnd_801720 : Nat := 4983230072969 + 3 ^ 40 * 801720 * 2
def baseEnd_801720 : Nat := 30493904468348777815775

theorem tailTrace_801720 : CollatzResearch.WordTrace tailWord_801720 prefixEnd_801720 30493904468348777815775 := by
  unfold tailWord_801720
  simp only [CollatzResearch.WordTrace]
  refine ⟨14620565327756418860061307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19494087103675225146748409 14620565327756418860061307)
  ·
    refine ⟨21930847991634628290091961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14620565327756418860061307 21930847991634628290091961)
    ·
      refine ⟨16448135993725971217568971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21930847991634628290091961 16448135993725971217568971)
      ·
        refine ⟨24672203990588956826353457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16448135993725971217568971 24672203990588956826353457)
        ·
          refine ⟨18504152992941717619765093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24672203990588956826353457 18504152992941717619765093)
          ·
            refine ⟨3469528686176572053705955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18504152992941717619765093 3469528686176572053705955)
            ·
              refine ⟨5204293029264858080558933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3469528686176572053705955 5204293029264858080558933)
              ·
                refine ⟨30493904468348777815775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5204293029264858080558933 30493904468348777815775)
                ·
                  rfl

theorem cell22_801720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 9].length) (baseStart_801720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_801720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_801720 prefixEnd_801720 := by exact prefixLift 801720
  have htrace : WordTrace (prefixWord ++ tailWord_801720) baseStart_801720 baseEnd_801720 := by
    simpa [prefixWord, tailWord_801720, baseEnd_801720] using wordTrace_append hprefix tailTrace_801720
  have hstable : (prefixWord ++ tailWord_801720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801720).length < 2 ^ (prefixWord ++ tailWord_801720).sum := by decide
  have hdescent : baseEnd_801720 < baseStart_801720 := by decide
  rcases family_descends (prefixWord ++ tailWord_801720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801735 : List Nat := [1, 1, 4, 1, 1, 2, 2, 1, 2, 7]
def baseStart_801735 : Nat := 118140960795 + 801735 * 2 ^ 59
def prefixEnd_801735 : Nat := 4983230072969 + 3 ^ 40 * 801735 * 2
def baseEnd_801735 : Nat := 274450275021683961216929

theorem tailTrace_801735 : CollatzResearch.WordTrace tailWord_801735 prefixEnd_801735 274450275021683961216929 := by
  unfold tailWord_801735
  simp only [CollatzResearch.WordTrace]
  refine ⟨29241677750458495281918659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19494451833638996854612439 29241677750458495281918659)
  ·
    refine ⟨43862516625687742922877989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29241677750458495281918659 43862516625687742922877989)
    ·
      refine ⟨8224221867316451798039623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43862516625687742922877989 8224221867316451798039623)
      ·
        refine ⟨12336332800974677697059435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8224221867316451798039623 12336332800974677697059435)
        ·
          refine ⟨18504499201462016545589153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12336332800974677697059435 18504499201462016545589153)
          ·
            refine ⟨13878374401096512409191865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18504499201462016545589153 13878374401096512409191865)
            ·
              refine ⟨10408780800822384306893899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13878374401096512409191865 10408780800822384306893899)
              ·
                refine ⟨15613171201233576460340849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10408780800822384306893899 15613171201233576460340849)
                ·
                  refine ⟨11709878400925182345255637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15613171201233576460340849 11709878400925182345255637)
                  ·
                    refine ⟨274450275021683961216929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11709878400925182345255637 274450275021683961216929)
                    ·
                      rfl

theorem cell22_801735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 7].length) (baseStart_801735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_801735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_801735 prefixEnd_801735 := by exact prefixLift 801735
  have htrace : WordTrace (prefixWord ++ tailWord_801735) baseStart_801735 baseEnd_801735 := by
    simpa [prefixWord, tailWord_801735, baseEnd_801735] using wordTrace_append hprefix tailTrace_801735
  have hstable : (prefixWord ++ tailWord_801735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801735).length < 2 ^ (prefixWord ++ tailWord_801735).sum := by decide
  have hdescent : baseEnd_801735 < baseStart_801735 := by decide
  rcases family_descends (prefixWord ++ tailWord_801735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801767 : List Nat := [1, 1, 5, 2, 2, 1, 1, 1, 2, 6]
def baseStart_801767 : Nat := 118140960795 + 801767 * 2 ^ 59
def prefixEnd_801767 : Nat := 4983230072969 + 3 ^ 40 * 801767 * 2
def baseEnd_801767 : Nat := 274461229275646544416831

theorem tailTrace_801767 : CollatzResearch.WordTrace tailWord_801767 prefixEnd_801767 274461229275646544416831 := by
  unfold tailWord_801767
  simp only [CollatzResearch.WordTrace]
  refine ⟨29242844886342564747083555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19495229924228376498055703 29242844886342564747083555)
  ·
    refine ⟨43864267329513847120625333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29242844886342564747083555 43864267329513847120625333)
    ·
      refine ⟨4112275062141923167558625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43864267329513847120625333 4112275062141923167558625)
      ·
        refine ⟨3084206296606442375668969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4112275062141923167558625 3084206296606442375668969)
        ·
          refine ⟨2313154722454831781751727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3084206296606442375668969 2313154722454831781751727)
          ·
            refine ⟨3469732083682247672627591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2313154722454831781751727 3469732083682247672627591)
            ·
              refine ⟨5204598125523371508941387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3469732083682247672627591 5204598125523371508941387)
              ·
                refine ⟨7806897188285057263412081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5204598125523371508941387 7806897188285057263412081)
                ·
                  refine ⟨5855172891213792947559061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7806897188285057263412081 5855172891213792947559061)
                  ·
                    refine ⟨274461229275646544416831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5855172891213792947559061 274461229275646544416831)
                    ·
                      rfl

theorem cell22_801767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_801767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_801767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_801767 prefixEnd_801767 := by exact prefixLift 801767
  have htrace : WordTrace (prefixWord ++ tailWord_801767) baseStart_801767 baseEnd_801767 := by
    simpa [prefixWord, tailWord_801767, baseEnd_801767] using wordTrace_append hprefix tailTrace_801767
  have hstable : (prefixWord ++ tailWord_801767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801767).length < 2 ^ (prefixWord ++ tailWord_801767).sum := by decide
  have hdescent : baseEnd_801767 < baseStart_801767 := by decide
  rcases family_descends (prefixWord ++ tailWord_801767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801827 : List Nat := [1, 1, 1, 4, 3, 2, 1, 3, 6]
def baseStart_801827 : Nat := 118140960795 + 801827 * 2 ^ 59
def prefixEnd_801827 : Nat := 4983230072969 + 3 ^ 40 * 801827 * 2
def baseEnd_801827 : Nat := 91493922833942129305549

theorem tailTrace_801827 : CollatzResearch.WordTrace tailWord_801827 prefixEnd_801827 91493922833942129305549 := by
  unfold tailWord_801827
  simp only [CollatzResearch.WordTrace]
  refine ⟨29245033266125194994267735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19496688844083463329511823 29245033266125194994267735)
  ·
    refine ⟨43867549899187792491401603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29245033266125194994267735 43867549899187792491401603)
    ·
      refine ⟨65801324848781688737102405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43867549899187792491401603 65801324848781688737102405)
      ·
        refine ⟨12337748409146566638206701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65801324848781688737102405 12337748409146566638206701)
        ·
          refine ⟨4626655653429962489327513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12337748409146566638206701 4626655653429962489327513)
          ·
            refine ⟨3469991740072471866995635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4626655653429962489327513 3469991740072471866995635)
            ·
              refine ⟨5204987610108707800493453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3469991740072471866995635 5204987610108707800493453)
              ·
                refine ⟨1951870353790765425185045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5204987610108707800493453 1951870353790765425185045)
                ·
                  refine ⟨91493922833942129305549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1951870353790765425185045 91493922833942129305549)
                  ·
                    rfl

theorem cell22_801827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 3, 6].length) (baseStart_801827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_801827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_801827 prefixEnd_801827 := by exact prefixLift 801827
  have htrace : WordTrace (prefixWord ++ tailWord_801827) baseStart_801827 baseEnd_801827 := by
    simpa [prefixWord, tailWord_801827, baseEnd_801827] using wordTrace_append hprefix tailTrace_801827
  have hstable : (prefixWord ++ tailWord_801827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801827).length < 2 ^ (prefixWord ++ tailWord_801827).sum := by decide
  have hdescent : baseEnd_801827 < baseStart_801827 := by decide
  rcases family_descends (prefixWord ++ tailWord_801827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801846 : List Nat := [5, 1, 2, 1, 1, 2, 1, 4, 1, 4]
def baseStart_801846 : Nat := 118140960795 + 801846 * 2 ^ 59
def prefixEnd_801846 : Nat := 4983230072969 + 3 ^ 40 * 801846 * 2
def baseEnd_801846 : Nat := 274488272590116671691589

theorem tailTrace_801846 : CollatzResearch.WordTrace tailWord_801846 prefixEnd_801846 274488272590116671691589 := by
  unfold tailWord_801846
  simp only [CollatzResearch.WordTrace]
  refine ⟨1827857890816022577450587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19497150835370907492806261 1827857890816022577450587)
  ·
    refine ⟨2741786836224033866175881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1827857890816022577450587 2741786836224033866175881)
    ·
      refine ⟨2056340127168025399631911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2741786836224033866175881 2056340127168025399631911)
      ·
        refine ⟨3084510190752038099447867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2056340127168025399631911 3084510190752038099447867)
        ·
          refine ⟨4626765286128057149171801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3084510190752038099447867 4626765286128057149171801)
          ·
            refine ⟨3470073964596042861878851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4626765286128057149171801 3470073964596042861878851)
            ·
              refine ⟨5205110946894064292818277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3470073964596042861878851 5205110946894064292818277)
              ·
                refine ⟨975958302542637054903427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5205110946894064292818277 975958302542637054903427)
                ·
                  refine ⟨1463937453813955582355141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 975958302542637054903427 1463937453813955582355141)
                  ·
                    refine ⟨274488272590116671691589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1463937453813955582355141 274488272590116671691589)
                    ·
                      rfl

theorem cell22_801846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_801846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_801846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_801846 prefixEnd_801846 := by exact prefixLift 801846
  have htrace : WordTrace (prefixWord ++ tailWord_801846) baseStart_801846 baseEnd_801846 := by
    simpa [prefixWord, tailWord_801846, baseEnd_801846] using wordTrace_append hprefix tailTrace_801846
  have hstable : (prefixWord ++ tailWord_801846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801846).length < 2 ^ (prefixWord ++ tailWord_801846).sum := by decide
  have hdescent : baseEnd_801846 < baseStart_801846 := by decide
  rcases family_descends (prefixWord ++ tailWord_801846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801874 : List Nat := [3, 2, 2, 1, 3, 1, 1, 1, 4, 4]
def baseStart_801874 : Nat := 118140960795 + 801874 * 2 ^ 59
def prefixEnd_801874 : Nat := 4983230072969 + 3 ^ 40 * 801874 * 2
def baseEnd_801874 : Nat := 274497857562333931991503

theorem tailTrace_801874 : CollatzResearch.WordTrace tailWord_801874 prefixEnd_801874 274497857562333931991503 := by
  unfold tailWord_801874
  simp only [CollatzResearch.WordTrace]
  refine ⟨7311686874238730505307169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19497831664636614680819117 7311686874238730505307169)
  ·
    refine ⟨5483765155679047878980377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7311686874238730505307169 5483765155679047878980377)
    ·
      refine ⟨4112823866759285909235283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5483765155679047878980377 4112823866759285909235283)
      ·
        refine ⟨6169235800138928863852925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4112823866759285909235283 6169235800138928863852925)
        ·
          refine ⟨2313463425052098323944847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6169235800138928863852925 2313463425052098323944847)
          ·
            refine ⟨3470195137578147485917271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2313463425052098323944847 3470195137578147485917271)
            ·
              refine ⟨5205292706367221228875907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3470195137578147485917271 5205292706367221228875907)
              ·
                refine ⟨7807939059550831843313861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5205292706367221228875907 7807939059550831843313861)
                ·
                  refine ⟨1463988573665780970621349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7807939059550831843313861 1463988573665780970621349)
                  ·
                    refine ⟨274497857562333931991503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1463988573665780970621349 274497857562333931991503)
                    ·
                      rfl

theorem cell22_801874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_801874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_801874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_801874 prefixEnd_801874 := by exact prefixLift 801874
  have htrace : WordTrace (prefixWord ++ tailWord_801874) baseStart_801874 baseEnd_801874 := by
    simpa [prefixWord, tailWord_801874, baseEnd_801874] using wordTrace_append hprefix tailTrace_801874
  have hstable : (prefixWord ++ tailWord_801874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801874).length < 2 ^ (prefixWord ++ tailWord_801874).sum := by decide
  have hdescent : baseEnd_801874 < baseStart_801874 := by decide
  rcases family_descends (prefixWord ++ tailWord_801874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801904 : List Nat := [2, 1, 1, 1, 5, 1, 2, 1, 5, 3]
def baseStart_801904 : Nat := 118140960795 + 801904 * 2 ^ 59
def prefixEnd_801904 : Nat := 4983230072969 + 3 ^ 40 * 801904 * 2
def baseEnd_801904 : Nat := 274508127175423853741411

theorem tailTrace_801904 : CollatzResearch.WordTrace tailWord_801904 prefixEnd_801904 274508127175423853741411 := by
  unfold tailWord_801904
  simp only [CollatzResearch.WordTrace]
  refine ⟨14623920843423118572410383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19498561124564158096547177 14623920843423118572410383)
  ·
    refine ⟨21935881265134677858615575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14623920843423118572410383 21935881265134677858615575)
    ·
      refine ⟨32903821897702016787923363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21935881265134677858615575 32903821897702016787923363)
      ·
        refine ⟨49355732846553025181885045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32903821897702016787923363 49355732846553025181885045)
        ·
          refine ⟨4627099954364346110801723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49355732846553025181885045 4627099954364346110801723)
          ·
            refine ⟨6940649931546519166202585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4627099954364346110801723 6940649931546519166202585)
            ·
              refine ⟨5205487448659889374651939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6940649931546519166202585 5205487448659889374651939)
              ·
                refine ⟨7808231172989834061977909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5205487448659889374651939 7808231172989834061977909)
                ·
                  refine ⟨732021672467796943310429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7808231172989834061977909 732021672467796943310429)
                  ·
                    refine ⟨274508127175423853741411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 732021672467796943310429 274508127175423853741411)
                    ·
                      rfl

theorem cell22_801904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 5, 3].length) (baseStart_801904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_801904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_801904 prefixEnd_801904 := by exact prefixLift 801904
  have htrace : WordTrace (prefixWord ++ tailWord_801904) baseStart_801904 baseEnd_801904 := by
    simpa [prefixWord, tailWord_801904, baseEnd_801904] using wordTrace_append hprefix tailTrace_801904
  have hstable : (prefixWord ++ tailWord_801904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801904).length < 2 ^ (prefixWord ++ tailWord_801904).sum := by decide
  have hdescent : baseEnd_801904 < baseStart_801904 := by decide
  rcases family_descends (prefixWord ++ tailWord_801904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801932 : List Nat := [2, 2, 1, 2, 1, 1, 1, 2, 3, 7]
def baseStart_801932 : Nat := 118140960795 + 801932 * 2 ^ 59
def prefixEnd_801932 : Nat := 4983230072969 + 3 ^ 40 * 801932 * 2
def baseEnd_801932 : Nat := 274517712147641114041325

theorem tailTrace_801932 : CollatzResearch.WordTrace tailWord_801932 prefixEnd_801932 274517712147641114041325 := by
  unfold tailWord_801932
  simp only [CollatzResearch.WordTrace]
  refine ⟨14624431465372398963420025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19499241953829865284560033 14624431465372398963420025)
  ·
    refine ⟨10968323599029299222565019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14624431465372398963420025 10968323599029299222565019)
    ·
      refine ⟨16452485398543948833847529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10968323599029299222565019 16452485398543948833847529)
      ·
        refine ⟨12339364048907961625385647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16452485398543948833847529 12339364048907961625385647)
        ·
          refine ⟨18509046073361942438078471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12339364048907961625385647 18509046073361942438078471)
          ·
            refine ⟨27763569110042913657117707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18509046073361942438078471 27763569110042913657117707)
            ·
              refine ⟨41645353665064370485676561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27763569110042913657117707 41645353665064370485676561)
              ·
                refine ⟨31234015248798277864257421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41645353665064370485676561 31234015248798277864257421)
                ·
                  refine ⟨11712755718299354199096533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31234015248798277864257421 11712755718299354199096533)
                  ·
                    refine ⟨274517712147641114041325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11712755718299354199096533 274517712147641114041325)
                    ·
                      rfl

theorem cell22_801932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 3, 7].length) (baseStart_801932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_801932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_801932 prefixEnd_801932 := by exact prefixLift 801932
  have htrace : WordTrace (prefixWord ++ tailWord_801932) baseStart_801932 baseEnd_801932 := by
    simpa [prefixWord, tailWord_801932, baseEnd_801932] using wordTrace_append hprefix tailTrace_801932
  have hstable : (prefixWord ++ tailWord_801932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801932).length < 2 ^ (prefixWord ++ tailWord_801932).sum := by decide
  have hdescent : baseEnd_801932 < baseStart_801932 := by decide
  rcases family_descends (prefixWord ++ tailWord_801932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801949 : List Nat := [1, 4, 2, 1, 1, 2, 3, 1, 2, 5]
def baseStart_801949 : Nat := 118140960795 + 801949 * 2 ^ 59
def prefixEnd_801949 : Nat := 4983230072969 + 3 ^ 40 * 801949 * 2
def baseEnd_801949 : Nat := 274523531595058736366273

theorem tailTrace_801949 : CollatzResearch.WordTrace tailWord_801949 prefixEnd_801949 274523531595058736366273 := by
  unfold tailWord_801949
  simp only [CollatzResearch.WordTrace]
  refine ⟨29249482971683209830208901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19499655314455473220139267 29249482971683209830208901)
  ·
    refine ⟨5484278057190601843164169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29249482971683209830208901 5484278057190601843164169)
    ·
      refine ⟨4113208542892951382373127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5484278057190601843164169 4113208542892951382373127)
      ·
        refine ⟨6169812814339427073559691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4113208542892951382373127 6169812814339427073559691)
        ·
          refine ⟨9254719221509140610339537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6169812814339427073559691 9254719221509140610339537)
          ·
            refine ⟨6941039416131855457754653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9254719221509140610339537 6941039416131855457754653)
            ·
              refine ⟨2602889781049445796657995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6941039416131855457754653 2602889781049445796657995)
              ·
                refine ⟨3904334671574168694986993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2602889781049445796657995 3904334671574168694986993)
                ·
                  refine ⟨2928251003680626521240245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3904334671574168694986993 2928251003680626521240245)
                  ·
                    refine ⟨274523531595058736366273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2928251003680626521240245 274523531595058736366273)
                    ·
                      rfl

theorem cell22_801949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_801949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_801949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_801949 prefixEnd_801949 := by exact prefixLift 801949
  have htrace : WordTrace (prefixWord ++ tailWord_801949) baseStart_801949 baseEnd_801949 := by
    simpa [prefixWord, tailWord_801949, baseEnd_801949] using wordTrace_append hprefix tailTrace_801949
  have hstable : (prefixWord ++ tailWord_801949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801949).length < 2 ^ (prefixWord ++ tailWord_801949).sum := by decide
  have hdescent : baseEnd_801949 < baseStart_801949 := by decide
  rcases family_descends (prefixWord ++ tailWord_801949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802024 : List Nat := [2, 1, 4, 1, 2, 1, 3, 8]
def baseStart_802024 : Nat := 118140960795 + 802024 * 2 ^ 59
def prefixEnd_802024 : Nat := 4983230072969 + 3 ^ 40 * 802024 * 2
def baseEnd_802024 : Nat := 30505467291975948971227

theorem tailTrace_802024 : CollatzResearch.WordTrace tailWord_802024 prefixEnd_802024 30505467291975948971227 := by
  unfold tailWord_802024
  simp only [CollatzResearch.WordTrace]
  refine ⟨14626109223205748819594563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19501478964274331759459417 14626109223205748819594563)
  ·
    refine ⟨21939163834808623229391845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14626109223205748819594563 21939163834808623229391845)
    ·
      refine ⟨4113593219026616855510971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21939163834808623229391845 4113593219026616855510971)
      ·
        refine ⟨6170389828539925283266457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4113593219026616855510971 6170389828539925283266457)
        ·
          refine ⟨4627792371404943962449843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6170389828539925283266457 4627792371404943962449843)
          ·
            refine ⟨6941688557107415943674765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4627792371404943962449843 6941688557107415943674765)
            ·
              refine ⟨2603133208915280978878037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6941688557107415943674765 2603133208915280978878037)
              ·
                refine ⟨30505467291975948971227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2603133208915280978878037 30505467291975948971227)
                ·
                  rfl

theorem cell22_802024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 8].length) (baseStart_802024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_802024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_802024 prefixEnd_802024 := by exact prefixLift 802024
  have htrace : WordTrace (prefixWord ++ tailWord_802024) baseStart_802024 baseEnd_802024 := by
    simpa [prefixWord, tailWord_802024, baseEnd_802024] using wordTrace_append hprefix tailTrace_802024
  have hstable : (prefixWord ++ tailWord_802024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802024).length < 2 ^ (prefixWord ++ tailWord_802024).sum := by decide
  have hdescent : baseEnd_802024 < baseStart_802024 := by decide
  rcases family_descends (prefixWord ++ tailWord_802024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802141 : List Nat := [1, 4, 5, 1, 1, 1, 2, 3, 1, 3]
def baseStart_802141 : Nat := 118140960795 + 802141 * 2 ^ 59
def prefixEnd_802141 : Nat := 4983230072969 + 3 ^ 40 * 802141 * 2
def baseEnd_802141 : Nat := 274589257118834235565685

theorem tailTrace_802141 : CollatzResearch.WordTrace tailWord_802141 prefixEnd_802141 274589257118834235565685 := by
  unfold tailWord_802141
  simp only [CollatzResearch.WordTrace]
  refine ⟨29256485786987626621198277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19504323857991751080798851 29256485786987626621198277)
  ·
    refine ⟨5485591085060179991474677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29256485786987626621198277 5485591085060179991474677)
    ·
      refine ⟨514274164224391874200751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5485591085060179991474677 514274164224391874200751)
      ·
        refine ⟨771411246336587811301127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 514274164224391874200751 771411246336587811301127)
        ·
          refine ⟨1157116869504881716951691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 771411246336587811301127 1157116869504881716951691)
          ·
            refine ⟨1735675304257322575427537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1157116869504881716951691 1735675304257322575427537)
            ·
              refine ⟨1301756478192991931570653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1735675304257322575427537 1301756478192991931570653)
              ·
                refine ⟨488158679322371974338995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1301756478192991931570653 488158679322371974338995)
                ·
                  refine ⟨732238018983557961508493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 488158679322371974338995 732238018983557961508493)
                  ·
                    refine ⟨274589257118834235565685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 732238018983557961508493 274589257118834235565685)
                    ·
                      rfl

theorem cell22_802141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_802141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_802141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_802141 prefixEnd_802141 := by exact prefixLift 802141
  have htrace : WordTrace (prefixWord ++ tailWord_802141) baseStart_802141 baseEnd_802141 := by
    simpa [prefixWord, tailWord_802141, baseEnd_802141] using wordTrace_append hprefix tailTrace_802141
  have hstable : (prefixWord ++ tailWord_802141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802141).length < 2 ^ (prefixWord ++ tailWord_802141).sum := by decide
  have hdescent : baseEnd_802141 < baseStart_802141 := by decide
  rcases family_descends (prefixWord ++ tailWord_802141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802148 : List Nat := [2, 3, 1, 1, 3, 2, 1, 5, 4]
def baseStart_802148 : Nat := 118140960795 + 802148 * 2 ^ 59
def prefixEnd_802148 : Nat := 4983230072969 + 3 ^ 40 * 802148 * 2
def baseEnd_802148 : Nat := 91530551120629516880221

theorem tailTrace_802148 : CollatzResearch.WordTrace tailWord_802148 prefixEnd_802148 91530551120629516880221 := by
  unfold tailWord_802148
  simp only [CollatzResearch.WordTrace]
  refine ⟨14628370548981133408351549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19504494065308177877802065 14628370548981133408351549)
  ·
    refine ⟨5485638955867925028131831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14628370548981133408351549 5485638955867925028131831)
    ·
      refine ⟨8228458433801887542197747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5485638955867925028131831 8228458433801887542197747)
      ·
        refine ⟨12342687650702831313296621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8228458433801887542197747 12342687650702831313296621)
        ·
          refine ⟨4628507869013561742486233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12342687650702831313296621 4628507869013561742486233)
          ·
            refine ⟨3471380901760171306864675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4628507869013561742486233 3471380901760171306864675)
            ·
              refine ⟨5207071352640256960297013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3471380901760171306864675 5207071352640256960297013)
              ·
                refine ⟨488162939310024090027845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5207071352640256960297013 488162939310024090027845)
                ·
                  refine ⟨91530551120629516880221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 488162939310024090027845 91530551120629516880221)
                  ·
                    rfl

theorem cell22_802148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 5, 4].length) (baseStart_802148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_802148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_802148 prefixEnd_802148 := by exact prefixLift 802148
  have htrace : WordTrace (prefixWord ++ tailWord_802148) baseStart_802148 baseEnd_802148 := by
    simpa [prefixWord, tailWord_802148, baseEnd_802148] using wordTrace_append hprefix tailTrace_802148
  have hstable : (prefixWord ++ tailWord_802148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802148).length < 2 ^ (prefixWord ++ tailWord_802148).sum := by decide
  have hdescent : baseEnd_802148 < baseStart_802148 := by decide
  rcases family_descends (prefixWord ++ tailWord_802148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802159 : List Nat := [1, 1, 2, 1, 3, 1, 13]
def baseStart_802159 : Nat := 118140960795 + 802159 * 2 ^ 59
def prefixEnd_802159 : Nat := 4983230072969 + 3 ^ 40 * 802159 * 2
def baseEnd_802159 : Nat := 10170200699506969948727

theorem tailTrace_802159 : CollatzResearch.WordTrace tailWord_802159 prefixEnd_802159 10170200699506969948727 := by
  unfold tailWord_802159
  simp only [CollatzResearch.WordTrace]
  refine ⟨29257142300922415695353531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19504761533948277130235687 29257142300922415695353531)
  ·
    refine ⟨43885713451383623543030297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29257142300922415695353531 43885713451383623543030297)
    ·
      refine ⟨32914285088537717657272723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43885713451383623543030297 32914285088537717657272723)
      ·
        refine ⟨49371427632806576485909085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32914285088537717657272723 49371427632806576485909085)
        ·
          refine ⟨18514285362302466182215907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49371427632806576485909085 18514285362302466182215907)
          ·
            refine ⟨27771428043453699273323861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18514285362302466182215907 27771428043453699273323861)
            ·
              refine ⟨10170200699506969948727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 27771428043453699273323861 10170200699506969948727)
              ·
                rfl

theorem cell22_802159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 13].length) (baseStart_802159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_802159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_802159 prefixEnd_802159 := by exact prefixLift 802159
  have htrace : WordTrace (prefixWord ++ tailWord_802159) baseStart_802159 baseEnd_802159 := by
    simpa [prefixWord, tailWord_802159, baseEnd_802159] using wordTrace_append hprefix tailTrace_802159
  have hstable : (prefixWord ++ tailWord_802159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802159).length < 2 ^ (prefixWord ++ tailWord_802159).sum := by decide
  have hdescent : baseEnd_802159 < baseStart_802159 := by decide
  rcases family_descends (prefixWord ++ tailWord_802159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802161 : List Nat := [1, 2, 2, 2, 1, 2, 2, 4, 2, 4]
def baseStart_802161 : Nat := 118140960795 + 802161 * 2 ^ 59
def prefixEnd_802161 : Nat := 4983230072969 + 3 ^ 40 * 802161 * 2
def baseEnd_802161 : Nat := 274596103527560850065623

theorem tailTrace_802161 : CollatzResearch.WordTrace tailWord_802161 prefixEnd_802161 274596103527560850065623 := by
  unfold tailWord_802161
  simp only [CollatzResearch.WordTrace]
  refine ⟨29257215246915170036926337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19504810164610113357950891 29257215246915170036926337)
  ·
    refine ⟨21942911435186377527694753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29257215246915170036926337 21942911435186377527694753)
    ·
      refine ⟨16457183576389783145771065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21942911435186377527694753 16457183576389783145771065)
      ·
        refine ⟨12342887682292337359328299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16457183576389783145771065 12342887682292337359328299)
        ·
          refine ⟨18514331523438506038992449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12342887682292337359328299 18514331523438506038992449)
          ·
            refine ⟨13885748642578879529244337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18514331523438506038992449 13885748642578879529244337)
            ·
              refine ⟨10414311481934159646933253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13885748642578879529244337 10414311481934159646933253)
              ·
                refine ⟨1952683402862654933799985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10414311481934159646933253 1952683402862654933799985)
                ·
                  refine ⟨1464512552146991200349989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1952683402862654933799985 1464512552146991200349989)
                  ·
                    refine ⟨274596103527560850065623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1464512552146991200349989 274596103527560850065623)
                    ·
                      rfl

theorem cell22_802161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 4, 2, 4].length) (baseStart_802161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_802161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_802161 prefixEnd_802161 := by exact prefixLift 802161
  have htrace : WordTrace (prefixWord ++ tailWord_802161) baseStart_802161 baseEnd_802161 := by
    simpa [prefixWord, tailWord_802161, baseEnd_802161] using wordTrace_append hprefix tailTrace_802161
  have hstable : (prefixWord ++ tailWord_802161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802161).length < 2 ^ (prefixWord ++ tailWord_802161).sum := by decide
  have hdescent : baseEnd_802161 < baseStart_802161 := by decide
  rcases family_descends (prefixWord ++ tailWord_802161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802298 : List Nat := [3, 1, 1, 1, 1, 2, 6, 1, 1, 5]
def baseStart_802298 : Nat := 118140960795 + 802298 * 2 ^ 59
def prefixEnd_802298 : Nat := 4983230072969 + 3 ^ 40 * 802298 * 2
def baseEnd_802298 : Nat := 274643001427338159390203

theorem tailTrace_802298 : CollatzResearch.WordTrace tailWord_802298 prefixEnd_802298 274643001427338159390203 := by
  unfold tailWord_802298
  simp only [CollatzResearch.WordTrace]
  refine ⟨7315553011854710608665887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19508141364945894956442365 7315553011854710608665887)
  ·
    refine ⟨10973329517782065912998831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7315553011854710608665887 10973329517782065912998831)
    ·
      refine ⟨16459994276673098869498247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10973329517782065912998831 16459994276673098869498247)
      ·
        refine ⟨24689991415009648304247371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16459994276673098869498247 24689991415009648304247371)
        ·
          refine ⟨37034987122514472456371057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24689991415009648304247371 37034987122514472456371057)
          ·
            refine ⟨27776240341885854342278293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37034987122514472456371057 27776240341885854342278293)
            ·
              refine ⟨1302011266025899422294295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 27776240341885854342278293 1302011266025899422294295)
              ·
                refine ⟨1953016899038849133441443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1302011266025899422294295 1953016899038849133441443)
                ·
                  refine ⟨2929525348558273700162165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1953016899038849133441443 2929525348558273700162165)
                  ·
                    refine ⟨274643001427338159390203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2929525348558273700162165 274643001427338159390203)
                    ·
                      rfl

theorem cell22_802298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 1, 1, 5].length) (baseStart_802298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_802298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_802298 prefixEnd_802298 := by exact prefixLift 802298
  have htrace : WordTrace (prefixWord ++ tailWord_802298) baseStart_802298 baseEnd_802298 := by
    simpa [prefixWord, tailWord_802298, baseEnd_802298] using wordTrace_append hprefix tailTrace_802298
  have hstable : (prefixWord ++ tailWord_802298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802298).length < 2 ^ (prefixWord ++ tailWord_802298).sum := by decide
  have hdescent : baseEnd_802298 < baseStart_802298 := by decide
  rcases family_descends (prefixWord ++ tailWord_802298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802328 : List Nat := [2, 1, 2, 3, 4, 1, 9]
def baseStart_802328 : Nat := 118140960795 + 802328 * 2 ^ 59
def prefixEnd_802328 : Nat := 4983230072969 + 3 ^ 40 * 802328 * 2
def baseEnd_802328 : Nat := 10172343371867706708893

theorem tailTrace_802328 : CollatzResearch.WordTrace tailWord_802328 prefixEnd_802328 10172343371867706708893 := by
  unfold tailWord_802328
  simp only [CollatzResearch.WordTrace]
  refine ⟨14631653118655078779127819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19508870824873438372170425 14631653118655078779127819)
  ·
    refine ⟨21947479677982618168691729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14631653118655078779127819 21947479677982618168691729)
    ·
      refine ⟨16460609758486963626518797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21947479677982618168691729 16460609758486963626518797)
      ·
        refine ⟨6172728659432611359944549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16460609758486963626518797 6172728659432611359944549)
        ·
          refine ⟨1157386623643614629989603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6172728659432611359944549 1157386623643614629989603)
          ·
            refine ⟨1736079935465421944984405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1157386623643614629989603 1736079935465421944984405)
            ·
              refine ⟨10172343371867706708893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1736079935465421944984405 10172343371867706708893)
              ·
                rfl

theorem cell22_802328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 9].length) (baseStart_802328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_802328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_802328 prefixEnd_802328 := by exact prefixLift 802328
  have htrace : WordTrace (prefixWord ++ tailWord_802328) baseStart_802328 baseEnd_802328 := by
    simpa [prefixWord, tailWord_802328, baseEnd_802328] using wordTrace_append hprefix tailTrace_802328
  have hstable : (prefixWord ++ tailWord_802328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802328).length < 2 ^ (prefixWord ++ tailWord_802328).sum := by decide
  have hdescent : baseEnd_802328 < baseStart_802328 := by decide
  rcases family_descends (prefixWord ++ tailWord_802328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802360 : List Nat := [2, 1, 2, 1, 4, 2, 2, 2, 3, 3]
def baseStart_802360 : Nat := 118140960795 + 802360 * 2 ^ 59
def prefixEnd_802360 : Nat := 4983230072969 + 3 ^ 40 * 802360 * 2
def baseEnd_802360 : Nat := 274664225294390664340013

theorem tailTrace_802360 : CollatzResearch.WordTrace tailWord_802360 prefixEnd_802360 274664225294390664340013 := by
  unfold tailWord_802360
  simp only [CollatzResearch.WordTrace]
  refine ⟨14632236686597113511710267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19509648915462818015613689 14632236686597113511710267)
  ·
    refine ⟨21948355029895670267565401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14632236686597113511710267 21948355029895670267565401)
    ·
      refine ⟨16461266272421752700674051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21948355029895670267565401 16461266272421752700674051)
      ·
        refine ⟨24691899408632629051011077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16461266272421752700674051 24691899408632629051011077)
        ·
          refine ⟨4629731139118617947064577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24691899408632629051011077 4629731139118617947064577)
          ·
            refine ⟨3472298354338963460298433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4629731139118617947064577 3472298354338963460298433)
            ·
              refine ⟨2604223765754222595223825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3472298354338963460298433 2604223765754222595223825)
              ·
                refine ⟨1953167824315666946417869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2604223765754222595223825 1953167824315666946417869)
                ·
                  refine ⟨732437934118375104906701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1953167824315666946417869 732437934118375104906701)
                  ·
                    refine ⟨274664225294390664340013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 732437934118375104906701 274664225294390664340013)
                    ·
                      rfl

theorem cell22_802360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 2, 3, 3].length) (baseStart_802360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_802360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_802360 prefixEnd_802360 := by exact prefixLift 802360
  have htrace : WordTrace (prefixWord ++ tailWord_802360) baseStart_802360 baseEnd_802360 := by
    simpa [prefixWord, tailWord_802360, baseEnd_802360] using wordTrace_append hprefix tailTrace_802360
  have hstable : (prefixWord ++ tailWord_802360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802360).length < 2 ^ (prefixWord ++ tailWord_802360).sum := by decide
  have hdescent : baseEnd_802360 < baseStart_802360 := by decide
  rcases family_descends (prefixWord ++ tailWord_802360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802435 : List Nat := [1, 1, 1, 3, 3, 1, 1, 7, 4]
def baseStart_802435 : Nat := 118140960795 + 802435 * 2 ^ 59
def prefixEnd_802435 : Nat := 4983230072969 + 3 ^ 40 * 802435 * 2
def baseEnd_802435 : Nat := 91563299775705156238261

theorem tailTrace_802435 : CollatzResearch.WordTrace tailWord_802435 prefixEnd_802435 91563299775705156238261 := by
  unfold tailWord_802435
  simp only [CollatzResearch.WordTrace]
  refine ⟨29267208847922514832400759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19511472565281676554933839 29267208847922514832400759)
  ·
    refine ⟨43900813271883772248601139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29267208847922514832400759 43900813271883772248601139)
    ·
      refine ⟨65851219907825658372901709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43900813271883772248601139 65851219907825658372901709)
      ·
        refine ⟨24694207465434621889838141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65851219907825658372901709 24694207465434621889838141)
        ·
          refine ⟨9260327799537983208689303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24694207465434621889838141 9260327799537983208689303)
          ·
            refine ⟨13890491699306974813033955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9260327799537983208689303 13890491699306974813033955)
            ·
              refine ⟨20835737548960462219550933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13890491699306974813033955 20835737548960462219550933)
              ·
                refine ⟨488337598803760833270725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 20835737548960462219550933 488337598803760833270725)
                ·
                  refine ⟨91563299775705156238261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 488337598803760833270725 91563299775705156238261)
                  ·
                    rfl

theorem cell22_802435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 7, 4].length) (baseStart_802435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_802435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_802435 prefixEnd_802435 := by exact prefixLift 802435
  have htrace : WordTrace (prefixWord ++ tailWord_802435) baseStart_802435 baseEnd_802435 := by
    simpa [prefixWord, tailWord_802435, baseEnd_802435] using wordTrace_append hprefix tailTrace_802435
  have hstable : (prefixWord ++ tailWord_802435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802435).length < 2 ^ (prefixWord ++ tailWord_802435).sum := by decide
  have hdescent : baseEnd_802435 < baseStart_802435 := by decide
  rcases family_descends (prefixWord ++ tailWord_802435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802437 : List Nat := [1, 3, 1, 1, 4, 1, 5, 1, 1, 4]
def baseStart_802437 : Nat := 118140960795 + 802437 * 2 ^ 59
def prefixEnd_802437 : Nat := 4983230072969 + 3 ^ 40 * 802437 * 2
def baseEnd_802437 : Nat := 274690583967988130164777

theorem tailTrace_802437 : CollatzResearch.WordTrace tailWord_802437 prefixEnd_802437 274690583967988130164777 := by
  unfold tailWord_802437
  simp only [CollatzResearch.WordTrace]
  refine ⟨29267281793915269173973565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19511521195943512782649043 29267281793915269173973565)
  ·
    refine ⟨10975230672718225940240087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29267281793915269173973565 10975230672718225940240087)
    ·
      refine ⟨16462846009077338910360131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10975230672718225940240087 16462846009077338910360131)
      ·
        refine ⟨24694269013616008365540197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16462846009077338910360131 24694269013616008365540197)
        ·
          refine ⟨4630175440053001568538787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24694269013616008365540197 4630175440053001568538787)
          ·
            refine ⟨6945263160079502352808181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4630175440053001568538787 6945263160079502352808181)
            ·
              refine ⟨651118421257453345575767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6945263160079502352808181 651118421257453345575767)
              ·
                refine ⟨976677631886180018363651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 651118421257453345575767 976677631886180018363651)
                ·
                  refine ⟨1465016447829270027545477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 976677631886180018363651 1465016447829270027545477)
                  ·
                    refine ⟨274690583967988130164777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1465016447829270027545477 274690583967988130164777)
                    ·
                      rfl

theorem cell22_802437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 5, 1, 1, 4].length) (baseStart_802437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_802437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_802437 prefixEnd_802437 := by exact prefixLift 802437
  have htrace : WordTrace (prefixWord ++ tailWord_802437) baseStart_802437 baseEnd_802437 := by
    simpa [prefixWord, tailWord_802437, baseEnd_802437] using wordTrace_append hprefix tailTrace_802437
  have hstable : (prefixWord ++ tailWord_802437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802437).length < 2 ^ (prefixWord ++ tailWord_802437).sum := by decide
  have hdescent : baseEnd_802437 < baseStart_802437 := by decide
  rcases family_descends (prefixWord ++ tailWord_802437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802486 : List Nat := [5, 1, 3, 1, 1, 2, 2, 3, 4]
def baseStart_802486 : Nat := 118140960795 + 802486 * 2 ^ 59
def prefixEnd_802486 : Nat := 4983230072969 + 3 ^ 40 * 802486 * 2
def baseEnd_802486 : Nat := 91569119223122778563209

theorem tailTrace_802486 : CollatzResearch.WordTrace tailWord_802486 prefixEnd_802486 91569119223122778563209 := by
  unfold tailWord_802486
  simp only [CollatzResearch.WordTrace]
  refine ⟨1829316810671109408906707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19512712647158500361671541 1829316810671109408906707)
  ·
    refine ⟨2743975216006664113360061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1829316810671109408906707 2743975216006664113360061)
    ·
      refine ⟨1028990706002499042510023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2743975216006664113360061 1028990706002499042510023)
      ·
        refine ⟨1543486059003748563765035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1028990706002499042510023 1543486059003748563765035)
        ·
          refine ⟨2315229088505622845647553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1543486059003748563765035 2315229088505622845647553)
          ·
            refine ⟨1736421816379217134235665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2315229088505622845647553 1736421816379217134235665)
            ·
              refine ⟨1302316362284412850676749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1736421816379217134235665 1302316362284412850676749)
              ·
                refine ⟨488368635856654819003781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1302316362284412850676749 488368635856654819003781)
                ·
                  refine ⟨91569119223122778563209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 488368635856654819003781 91569119223122778563209)
                  ·
                    rfl

theorem cell22_802486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 3, 4].length) (baseStart_802486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_802486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_802486 prefixEnd_802486 := by exact prefixLift 802486
  have htrace : WordTrace (prefixWord ++ tailWord_802486) baseStart_802486 baseEnd_802486 := by
    simpa [prefixWord, tailWord_802486, baseEnd_802486] using wordTrace_append hprefix tailTrace_802486
  have hstable : (prefixWord ++ tailWord_802486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802486).length < 2 ^ (prefixWord ++ tailWord_802486).sum := by decide
  have hdescent : baseEnd_802486 < baseStart_802486 := by decide
  rcases family_descends (prefixWord ++ tailWord_802486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802495 : List Nat := [1, 1, 2, 2, 2, 3, 1, 2, 5, 3]
def baseStart_802495 : Nat := 118140960795 + 802495 * 2 ^ 59
def prefixEnd_802495 : Nat := 4983230072969 + 3 ^ 40 * 802495 * 2
def baseEnd_802495 : Nat := 274710438553295312214599

theorem tailTrace_802495 : CollatzResearch.WordTrace tailWord_802495 prefixEnd_802495 274710438553295312214599 := by
  unfold tailWord_802495
  simp only [CollatzResearch.WordTrace]
  refine ⟨29269397227705145079584939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19512931485136763386389959 29269397227705145079584939)
  ·
    refine ⟨43904095841557717619377409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29269397227705145079584939 43904095841557717619377409)
    ·
      refine ⟨32928071881168288214533057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43904095841557717619377409 32928071881168288214533057)
      ·
        refine ⟨24696053910876216160899793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32928071881168288214533057 24696053910876216160899793)
        ·
          refine ⟨18522040433157162120674845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24696053910876216160899793 18522040433157162120674845)
          ·
            refine ⟨6945765162433935795253067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18522040433157162120674845 6945765162433935795253067)
            ·
              refine ⟨10418647743650903692879601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6945765162433935795253067 10418647743650903692879601)
              ·
                refine ⟨7813985807738177769659701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10418647743650903692879601 7813985807738177769659701)
                ·
                  refine ⟨732561169475454165905597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7813985807738177769659701 732561169475454165905597)
                  ·
                    refine ⟨274710438553295312214599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 732561169475454165905597 274710438553295312214599)
                    ·
                      rfl

theorem cell22_802495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 5, 3].length) (baseStart_802495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_802495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_802495 prefixEnd_802495 := by exact prefixLift 802495
  have htrace : WordTrace (prefixWord ++ tailWord_802495) baseStart_802495 baseEnd_802495 := by
    simpa [prefixWord, tailWord_802495, baseEnd_802495] using wordTrace_append hprefix tailTrace_802495
  have hstable : (prefixWord ++ tailWord_802495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802495).length < 2 ^ (prefixWord ++ tailWord_802495).sum := by decide
  have hdescent : baseEnd_802495 < baseStart_802495 := by decide
  rcases family_descends (prefixWord ++ tailWord_802495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802518 : List Nat := [5, 2, 1, 3, 2, 1, 1, 1, 1, 5]
def baseStart_802518 : Nat := 118140960795 + 802518 * 2 ^ 59
def prefixEnd_802518 : Nat := 4983230072969 + 3 ^ 40 * 802518 * 2
def baseEnd_802518 : Nat := 274718311923330918889529

theorem tailTrace_802518 : CollatzResearch.WordTrace tailWord_802518 prefixEnd_802518 274718311923330918889529 := by
  unfold tailWord_802518
  simp only [CollatzResearch.WordTrace]
  refine ⟨1829389756663863750479513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19513490737747880005114805 1829389756663863750479513)
  ·
    refine ⟨1372042317497897812859635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1829389756663863750479513 1372042317497897812859635)
    ·
      refine ⟨2058063476246846719289453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1372042317497897812859635 2058063476246846719289453)
      ·
        refine ⟨771773803592567519733545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2058063476246846719289453 771773803592567519733545)
        ·
          refine ⟨578830352694425639800159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 771773803592567519733545 578830352694425639800159)
          ·
            refine ⟨868245529041638459700239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 578830352694425639800159 868245529041638459700239)
            ·
              refine ⟨1302368293562457689550359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 868245529041638459700239 1302368293562457689550359)
              ·
                refine ⟨1953552440343686534325539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1302368293562457689550359 1953552440343686534325539)
                ·
                  refine ⟨2930328660515529801488309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1953552440343686534325539 2930328660515529801488309)
                  ·
                    refine ⟨274718311923330918889529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2930328660515529801488309 274718311923330918889529)
                    ·
                      rfl

theorem cell22_802518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_802518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_802518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_802518 prefixEnd_802518 := by exact prefixLift 802518
  have htrace : WordTrace (prefixWord ++ tailWord_802518) baseStart_802518 baseEnd_802518 := by
    simpa [prefixWord, tailWord_802518, baseEnd_802518] using wordTrace_append hprefix tailTrace_802518
  have hstable : (prefixWord ++ tailWord_802518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802518).length < 2 ^ (prefixWord ++ tailWord_802518).sum := by decide
  have hdescent : baseEnd_802518 < baseStart_802518 := by decide
  rcases family_descends (prefixWord ++ tailWord_802518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802621 : List Nat := [1, 4, 1, 4, 1, 1, 4, 2, 4]
def baseStart_802621 : Nat := 118140960795 + 802621 * 2 ^ 59
def prefixEnd_802621 : Nat := 4983230072969 + 3 ^ 40 * 802621 * 2
def baseEnd_802621 : Nat := 91584523642757661188071

theorem tailTrace_802621 : CollatzResearch.WordTrace tailWord_802621 prefixEnd_802621 91584523642757661188071 := by
  unfold tailWord_802621
  simp only [CollatzResearch.WordTrace]
  refine ⟨29273992825248668598671717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19515995216832445732447811 29273992825248668598671717)
  ·
    refine ⟨5488873654734125362250947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29273992825248668598671717 5488873654734125362250947)
    ·
      refine ⟨8233310482101188043376421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5488873654734125362250947 8233310482101188043376421)
      ·
        refine ⟨1543745715393972758133079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8233310482101188043376421 1543745715393972758133079)
        ·
          refine ⟨2315618573090959137199619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1543745715393972758133079 2315618573090959137199619)
          ·
            refine ⟨3473427859636438705799429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2315618573090959137199619 3473427859636438705799429)
            ·
              refine ⟨651267723681832257337393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3473427859636438705799429 651267723681832257337393)
              ·
                refine ⟨488450792761374193003045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 651267723681832257337393 488450792761374193003045)
                ·
                  refine ⟨91584523642757661188071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 488450792761374193003045 91584523642757661188071)
                  ·
                    rfl

theorem cell22_802621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 4, 2, 4].length) (baseStart_802621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_802621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_802621 prefixEnd_802621 := by exact prefixLift 802621
  have htrace : WordTrace (prefixWord ++ tailWord_802621) baseStart_802621 baseEnd_802621 := by
    simpa [prefixWord, tailWord_802621, baseEnd_802621] using wordTrace_append hprefix tailTrace_802621
  have hstable : (prefixWord ++ tailWord_802621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802621).length < 2 ^ (prefixWord ++ tailWord_802621).sum := by decide
  have hdescent : baseEnd_802621 < baseStart_802621 := by decide
  rcases family_descends (prefixWord ++ tailWord_802621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802632 : List Nat := [2, 1, 3, 1, 1, 6, 1, 7]
def baseStart_802632 : Nat := 118140960795 + 802632 * 2 ^ 59
def prefixEnd_802632 : Nat := 4983230072969 + 3 ^ 40 * 802632 * 2
def baseEnd_802632 : Nat := 30528592939230291282131

theorem tailTrace_802632 : CollatzResearch.WordTrace tailWord_802632 prefixEnd_802632 30528592939230291282131 := by
  unfold tailWord_802632
  simp only [CollatzResearch.WordTrace]
  refine ⟨14637197014104408738661075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19516262685472544984881433 14637197014104408738661075)
  ·
    refine ⟨21955795521156613107991613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14637197014104408738661075 21955795521156613107991613)
    ·
      refine ⟨8233423320433729915496855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21955795521156613107991613 8233423320433729915496855)
      ·
        refine ⟨12350134980650594873245283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8233423320433729915496855 12350134980650594873245283)
        ·
          refine ⟨18525202470975892309867925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12350134980650594873245283 18525202470975892309867925)
          ·
            refine ⟨868368865826994952025059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 18525202470975892309867925 868368865826994952025059)
            ·
              refine ⟨1302553298740492428037589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 868368865826994952025059 1302553298740492428037589)
              ·
                refine ⟨30528592939230291282131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1302553298740492428037589 30528592939230291282131)
                ·
                  rfl

theorem cell22_802632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 7].length) (baseStart_802632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_802632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_802632 prefixEnd_802632 := by exact prefixLift 802632
  have htrace : WordTrace (prefixWord ++ tailWord_802632) baseStart_802632 baseEnd_802632 := by
    simpa [prefixWord, tailWord_802632, baseEnd_802632] using wordTrace_append hprefix tailTrace_802632
  have hstable : (prefixWord ++ tailWord_802632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802632).length < 2 ^ (prefixWord ++ tailWord_802632).sum := by decide
  have hdescent : baseEnd_802632 < baseStart_802632 := by decide
  rcases family_descends (prefixWord ++ tailWord_802632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802677 : List Nat := [1, 3, 4, 1, 1, 1, 3, 1, 7]
def baseStart_802677 : Nat := 118140960795 + 802677 * 2 ^ 59
def prefixEnd_802677 : Nat := 4983230072969 + 3 ^ 40 * 802677 * 2
def baseEnd_802677 : Nat := 91590913624235834721347

theorem tailTrace_802677 : CollatzResearch.WordTrace tailWord_802677 prefixEnd_802677 91590913624235834721347 := by
  unfold tailWord_802677
  simp only [CollatzResearch.WordTrace]
  refine ⟨29276035313045790162710285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19517356875363860108473523 29276035313045790162710285)
  ·
    refine ⟨10978513242392171311016357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29276035313045790162710285 10978513242392171311016357)
    ·
      refine ⟨2058471232948532120815567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10978513242392171311016357 2058471232948532120815567)
      ·
        refine ⟨3087706849422798181223351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2058471232948532120815567 3087706849422798181223351)
        ·
          refine ⟨4631560274134197271835027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3087706849422798181223351 4631560274134197271835027)
          ·
            refine ⟨6947340411201295907752541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4631560274134197271835027 6947340411201295907752541)
            ·
              refine ⟨2605252654200485965407203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6947340411201295907752541 2605252654200485965407203)
              ·
                refine ⟨3907878981300728948110805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2605252654200485965407203 3907878981300728948110805)
                ·
                  refine ⟨91590913624235834721347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3907878981300728948110805 91590913624235834721347)
                  ·
                    rfl

theorem cell22_802677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 1, 7].length) (baseStart_802677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_802677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_802677 prefixEnd_802677 := by exact prefixLift 802677
  have htrace : WordTrace (prefixWord ++ tailWord_802677) baseStart_802677 baseEnd_802677 := by
    simpa [prefixWord, tailWord_802677, baseEnd_802677] using wordTrace_append hprefix tailTrace_802677
  have hstable : (prefixWord ++ tailWord_802677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802677).length < 2 ^ (prefixWord ++ tailWord_802677).sum := by decide
  have hdescent : baseEnd_802677 < baseStart_802677 := by decide
  rcases family_descends (prefixWord ++ tailWord_802677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802692 : List Nat := [2, 3, 2, 1, 1, 1, 4, 1, 2, 5]
def baseStart_802692 : Nat := 118140960795 + 802692 * 2 ^ 59
def prefixEnd_802692 : Nat := 4983230072969 + 3 ^ 40 * 802692 * 2
def baseEnd_802692 : Nat := 274777875679252465038995

theorem tailTrace_802692 : CollatzResearch.WordTrace tailWord_802692 prefixEnd_802692 274777875679252465038995 := by
  unfold tailWord_802692
  simp only [CollatzResearch.WordTrace]
  refine ⟨14638291203995723862253165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19517721605327631816337553 14638291203995723862253165)
  ·
    refine ⟨5489359201498396448344937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14638291203995723862253165 5489359201498396448344937)
    ·
      refine ⟨4117019401123797336258703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5489359201498396448344937 4117019401123797336258703)
      ·
        refine ⟨6175529101685696004388055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4117019401123797336258703 6175529101685696004388055)
        ·
          refine ⟨9263293652528544006582083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6175529101685696004388055 9263293652528544006582083)
          ·
            refine ⟨13894940478792816009873125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9263293652528544006582083 13894940478792816009873125)
            ·
              refine ⟨2605301339773653001851211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13894940478792816009873125 2605301339773653001851211)
              ·
                refine ⟨3907952009660479502776817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2605301339773653001851211 3907952009660479502776817)
                ·
                  refine ⟨2930964007245359627082613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3907952009660479502776817 2930964007245359627082613)
                  ·
                    refine ⟨274777875679252465038995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2930964007245359627082613 274777875679252465038995)
                    ·
                      rfl

theorem cell22_802692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_802692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_802692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_802692 prefixEnd_802692 := by exact prefixLift 802692
  have htrace : WordTrace (prefixWord ++ tailWord_802692) baseStart_802692 baseEnd_802692 := by
    simpa [prefixWord, tailWord_802692, baseEnd_802692] using wordTrace_append hprefix tailTrace_802692
  have hstable : (prefixWord ++ tailWord_802692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802692).length < 2 ^ (prefixWord ++ tailWord_802692).sum := by decide
  have hdescent : baseEnd_802692 < baseStart_802692 := by decide
  rcases family_descends (prefixWord ++ tailWord_802692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802724 : List Nat := [2, 3, 1, 2, 1, 3, 2, 3, 1, 4]
def baseStart_802724 : Nat := 118140960795 + 802724 * 2 ^ 59
def prefixEnd_802724 : Nat := 4983230072969 + 3 ^ 40 * 802724 * 2
def baseEnd_802724 : Nat := 274788829933215048238897

theorem tailTrace_802724 : CollatzResearch.WordTrace tailWord_802724 prefixEnd_802724 274788829933215048238897 := by
  unfold tailWord_802724
  simp only [CollatzResearch.WordTrace]
  refine ⟨14638874771937758594835613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19518499695917011459780817 14638874771937758594835613)
  ·
    refine ⟨5489578039476659473063355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14638874771937758594835613 5489578039476659473063355)
    ·
      refine ⟨8234367059214989209595033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5489578039476659473063355 8234367059214989209595033)
      ·
        refine ⟨6175775294411241907196275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8234367059214989209595033 6175775294411241907196275)
        ·
          refine ⟨9263662941616862860794413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6175775294411241907196275 9263662941616862860794413)
          ·
            refine ⟨3473873603106323572797905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9263662941616862860794413 3473873603106323572797905)
            ·
              refine ⟨2605405202329742679598429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3473873603106323572797905 2605405202329742679598429)
              ·
                refine ⟨977026950873653504849411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2605405202329742679598429 977026950873653504849411)
                ·
                  refine ⟨1465540426310480257274117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 977026950873653504849411 1465540426310480257274117)
                  ·
                    refine ⟨274788829933215048238897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1465540426310480257274117 274788829933215048238897)
                    ·
                      rfl

theorem cell22_802724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 3, 1, 4].length) (baseStart_802724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_802724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_802724 prefixEnd_802724 := by exact prefixLift 802724
  have htrace : WordTrace (prefixWord ++ tailWord_802724) baseStart_802724 baseEnd_802724 := by
    simpa [prefixWord, tailWord_802724, baseEnd_802724] using wordTrace_append hprefix tailTrace_802724
  have hstable : (prefixWord ++ tailWord_802724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802724).length < 2 ^ (prefixWord ++ tailWord_802724).sum := by decide
  have hdescent : baseEnd_802724 < baseStart_802724 := by decide
  rcases family_descends (prefixWord ++ tailWord_802724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802752 : List Nat := [2, 1, 1, 2, 3, 2, 1, 2, 4, 4]
def baseStart_802752 : Nat := 118140960795 + 802752 * 2 ^ 59
def prefixEnd_802752 : Nat := 4983230072969 + 3 ^ 40 * 802752 * 2
def baseEnd_802752 : Nat := 274798414905432308538811

theorem tailTrace_802752 : CollatzResearch.WordTrace tailWord_802752 prefixEnd_802752 274798414905432308538811 := by
  unfold tailWord_802752
  simp only [CollatzResearch.WordTrace]
  refine ⟨14639385393887038985845255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19519180525182718647793673 14639385393887038985845255)
  ·
    refine ⟨21959078090830558478767883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14639385393887038985845255 21959078090830558478767883)
    ·
      refine ⟨32938617136245837718151825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21959078090830558478767883 32938617136245837718151825)
      ·
        refine ⟨24703962852184378288613869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32938617136245837718151825 24703962852184378288613869)
        ·
          refine ⟨9263986069569141858230201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24703962852184378288613869 9263986069569141858230201)
          ·
            refine ⟨6947989552176856393672651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9263986069569141858230201 6947989552176856393672651)
            ·
              refine ⟨10421984328265284590508977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6947989552176856393672651 10421984328265284590508977)
              ·
                refine ⟨7816488246198963442881733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10421984328265284590508977 7816488246198963442881733)
                ·
                  refine ⟨1465591546162305645540325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7816488246198963442881733 1465591546162305645540325)
                  ·
                    refine ⟨274798414905432308538811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1465591546162305645540325 274798414905432308538811)
                    ·
                      rfl

theorem cell22_802752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 4, 4].length) (baseStart_802752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_802752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_802752 prefixEnd_802752 := by exact prefixLift 802752
  have htrace : WordTrace (prefixWord ++ tailWord_802752) baseStart_802752 baseEnd_802752 := by
    simpa [prefixWord, tailWord_802752, baseEnd_802752] using wordTrace_append hprefix tailTrace_802752
  have hstable : (prefixWord ++ tailWord_802752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802752).length < 2 ^ (prefixWord ++ tailWord_802752).sum := by decide
  have hdescent : baseEnd_802752 < baseStart_802752 := by decide
  rcases family_descends (prefixWord ++ tailWord_802752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802799 : List Nat := [1, 1, 2, 1, 4, 2, 2, 3, 3, 3]
def baseStart_802799 : Nat := 118140960795 + 802799 * 2 ^ 59
def prefixEnd_802799 : Nat := 4983230072969 + 3 ^ 40 * 802799 * 2
def baseEnd_802799 : Nat := 274814503965939852613667

theorem tailTrace_802799 : CollatzResearch.WordTrace tailWord_802799 prefixEnd_802799 274814503965939852613667 := by
  unfold tailWord_802799
  simp only [CollatzResearch.WordTrace]
  refine ⟨29280485018603804998651451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19520323345735869999100967 29280485018603804998651451)
  ·
    refine ⟨43920727527905707497977177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29280485018603804998651451 43920727527905707497977177)
    ·
      refine ⟨32940545645929280623482883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43920727527905707497977177 32940545645929280623482883)
      ·
        refine ⟨49410818468893920935224325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32940545645929280623482883 49410818468893920935224325)
        ·
          refine ⟨9264528462917610175354561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49410818468893920935224325 9264528462917610175354561)
          ·
            refine ⟨6948396347188207631515921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9264528462917610175354561 6948396347188207631515921)
            ·
              refine ⟨5211297260391155723636941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6948396347188207631515921 5211297260391155723636941)
              ·
                refine ⟨1954236472646683396363853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5211297260391155723636941 1954236472646683396363853)
                ·
                  refine ⟨732838677242506273636445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1954236472646683396363853 732838677242506273636445)
                  ·
                    refine ⟨274814503965939852613667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 732838677242506273636445 274814503965939852613667)
                    ·
                      rfl

theorem cell22_802799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 3, 3, 3].length) (baseStart_802799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_802799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_802799 prefixEnd_802799 := by exact prefixLift 802799
  have htrace : WordTrace (prefixWord ++ tailWord_802799) baseStart_802799 baseEnd_802799 := by
    simpa [prefixWord, tailWord_802799, baseEnd_802799] using wordTrace_append hprefix tailTrace_802799
  have hstable : (prefixWord ++ tailWord_802799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802799).length < 2 ^ (prefixWord ++ tailWord_802799).sum := by decide
  have hdescent : baseEnd_802799 < baseStart_802799 := by decide
  rcases family_descends (prefixWord ++ tailWord_802799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802801 : List Nat := [1, 2, 2, 2, 6, 1, 1, 7]
def baseStart_802801 : Nat := 118140960795 + 802801 * 2 ^ 59
def prefixEnd_802801 : Nat := 4983230072969 + 3 ^ 40 * 802801 * 2
def baseEnd_802801 : Nat := 30535020956312501562629

theorem tailTrace_802801 : CollatzResearch.WordTrace tailWord_802801 prefixEnd_802801 30535020956312501562629 := by
  unfold tailWord_802801
  simp only [CollatzResearch.WordTrace]
  refine ⟨29280557964596559340224257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19520371976397706226816171 29280557964596559340224257)
  ·
    refine ⟨21960418473447419505168193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29280557964596559340224257 21960418473447419505168193)
    ·
      refine ⟨16470313855085564628876145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21960418473447419505168193 16470313855085564628876145)
      ·
        refine ⟨12352735391314173471657109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16470313855085564628876145 12352735391314173471657109)
        ·
          refine ⟨579034471467851881483927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12352735391314173471657109 579034471467851881483927)
          ·
            refine ⟨868551707201777822225891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 579034471467851881483927 868551707201777822225891)
            ·
              refine ⟨1302827560802666733338837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 868551707201777822225891 1302827560802666733338837)
              ·
                refine ⟨30535020956312501562629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1302827560802666733338837 30535020956312501562629)
                ·
                  rfl

theorem cell22_802801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 7].length) (baseStart_802801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_802801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_802801 prefixEnd_802801 := by exact prefixLift 802801
  have htrace : WordTrace (prefixWord ++ tailWord_802801) baseStart_802801 baseEnd_802801 := by
    simpa [prefixWord, tailWord_802801, baseEnd_802801] using wordTrace_append hprefix tailTrace_802801
  have hstable : (prefixWord ++ tailWord_802801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802801).length < 2 ^ (prefixWord ++ tailWord_802801).sum := by decide
  have hdescent : baseEnd_802801 < baseStart_802801 := by decide
  rcases family_descends (prefixWord ++ tailWord_802801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802820 : List Nat := [2, 3, 2, 4, 2, 1, 1, 1, 2, 4]
def baseStart_802820 : Nat := 118140960795 + 802820 * 2 ^ 59
def prefixEnd_802820 : Nat := 4983230072969 + 3 ^ 40 * 802820 * 2
def baseEnd_802820 : Nat := 274821692695102797838603

theorem tailTrace_802820 : CollatzResearch.WordTrace tailWord_802820 prefixEnd_802820 274821692695102797838603 := by
  unfold tailWord_802820
  simp only [CollatzResearch.WordTrace]
  refine ⟨14640625475763862792582957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19520833967685150390110609 14640625475763862792582957)
  ·
    refine ⟨5490234553411448547218609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14640625475763862792582957 5490234553411448547218609)
    ·
      refine ⟨4117675915058586410413957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5490234553411448547218609 4117675915058586410413957)
      ·
        refine ⟨772064234073484951952617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4117675915058586410413957 772064234073484951952617)
        ·
          refine ⟨579048175555113713964463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 772064234073484951952617 579048175555113713964463)
          ·
            refine ⟨868572263332670570946695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 579048175555113713964463 868572263332670570946695)
            ·
              refine ⟨1302858394999005856420043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 868572263332670570946695 1302858394999005856420043)
              ·
                refine ⟨1954287592498508784630065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1302858394999005856420043 1954287592498508784630065)
                ·
                  refine ⟨1465715694373881588472549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1954287592498508784630065 1465715694373881588472549)
                  ·
                    refine ⟨274821692695102797838603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1465715694373881588472549 274821692695102797838603)
                    ·
                      rfl

theorem cell22_802820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 1, 2, 4].length) (baseStart_802820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_802820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_802820 prefixEnd_802820 := by exact prefixLift 802820
  have htrace : WordTrace (prefixWord ++ tailWord_802820) baseStart_802820 baseEnd_802820 := by
    simpa [prefixWord, tailWord_802820, baseEnd_802820] using wordTrace_append hprefix tailTrace_802820
  have hstable : (prefixWord ++ tailWord_802820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802820).length < 2 ^ (prefixWord ++ tailWord_802820).sum := by decide
  have hdescent : baseEnd_802820 < baseStart_802820 := by decide
  rcases family_descends (prefixWord ++ tailWord_802820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802827 : List Nat := [1, 1, 1, 1, 6, 1, 1, 2, 1, 7]
def baseStart_802827 : Nat := 118140960795 + 802827 * 2 ^ 59
def prefixEnd_802827 : Nat := 4983230072969 + 3 ^ 40 * 802827 * 2
def baseEnd_802827 : Nat := 274824088938157112913581

theorem tailTrace_802827 : CollatzResearch.WordTrace tailWord_802827 prefixEnd_802827 274824088938157112913581 := by
  unfold tailWord_802827
  simp only [CollatzResearch.WordTrace]
  refine ⟨29281506262502365780670735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19521004175001577187113823 29281506262502365780670735)
  ·
    refine ⟨43922259393753548671006103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29281506262502365780670735 43922259393753548671006103)
    ·
      refine ⟨65883389090630323006509155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43922259393753548671006103 65883389090630323006509155)
      ·
        refine ⟨98825083635945484509763733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65883389090630323006509155 98825083635945484509763733)
        ·
          refine ⟨4632425795434944586395175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 98825083635945484509763733 4632425795434944586395175)
          ·
            refine ⟨6948638693152416879592763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4632425795434944586395175 6948638693152416879592763)
            ·
              refine ⟨10422958039728625319389145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6948638693152416879592763 10422958039728625319389145)
              ·
                refine ⟨7817218529796468989541859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10422958039728625319389145 7817218529796468989541859)
                ·
                  refine ⟨11725827794694703484312789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7817218529796468989541859 11725827794694703484312789)
                  ·
                    refine ⟨274824088938157112913581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11725827794694703484312789 274824088938157112913581)
                    ·
                      rfl

theorem cell22_802827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 7].length) (baseStart_802827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_802827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_802827 prefixEnd_802827 := by exact prefixLift 802827
  have htrace : WordTrace (prefixWord ++ tailWord_802827) baseStart_802827 baseEnd_802827 := by
    simpa [prefixWord, tailWord_802827, baseEnd_802827] using wordTrace_append hprefix tailTrace_802827
  have hstable : (prefixWord ++ tailWord_802827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802827).length < 2 ^ (prefixWord ++ tailWord_802827).sum := by decide
  have hdescent : baseEnd_802827 < baseStart_802827 := by decide
  rcases family_descends (prefixWord ++ tailWord_802827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802844 : List Nat := [2, 2, 3, 1, 3, 1, 1, 2, 2, 5]
def baseStart_802844 : Nat := 118140960795 + 802844 * 2 ^ 59
def prefixEnd_802844 : Nat := 4983230072969 + 3 ^ 40 * 802844 * 2
def baseEnd_802844 : Nat := 274829908385574735238529

theorem tailTrace_802844 : CollatzResearch.WordTrace tailWord_802844 prefixEnd_802844 274829908385574735238529 := by
  unfold tailWord_802844
  simp only [CollatzResearch.WordTrace]
  refine ⟨14641063151720388842019793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19521417535627185122693057 14641063151720388842019793)
  ·
    refine ⟨10980797363790291631514845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14641063151720388842019793 10980797363790291631514845)
    ·
      refine ⟨4117799011421359361818067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10980797363790291631514845 4117799011421359361818067)
      ·
        refine ⟨6176698517132039042727101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4117799011421359361818067 6176698517132039042727101)
        ·
          refine ⟨2316261943924514641022663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6176698517132039042727101 2316261943924514641022663)
          ·
            refine ⟨3474392915886771961533995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2316261943924514641022663 3474392915886771961533995)
            ·
              refine ⟨5211589373830157942300993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3474392915886771961533995 5211589373830157942300993)
              ·
                refine ⟨3908692030372618456725745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5211589373830157942300993 3908692030372618456725745)
                ·
                  refine ⟨2931519022779463842544309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3908692030372618456725745 2931519022779463842544309)
                  ·
                    refine ⟨274829908385574735238529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2931519022779463842544309 274829908385574735238529)
                    ·
                      rfl

theorem cell22_802844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_802844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_802844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_802844 prefixEnd_802844 := by exact prefixLift 802844
  have htrace : WordTrace (prefixWord ++ tailWord_802844) baseStart_802844 baseEnd_802844 := by
    simpa [prefixWord, tailWord_802844, baseEnd_802844] using wordTrace_append hprefix tailTrace_802844
  have hstable : (prefixWord ++ tailWord_802844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802844).length < 2 ^ (prefixWord ++ tailWord_802844).sum := by decide
  have hdescent : baseEnd_802844 < baseStart_802844 := by decide
  rcases family_descends (prefixWord ++ tailWord_802844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802876 : List Nat := [2, 2, 2, 2, 2, 1, 4, 2, 1, 4]
def baseStart_802876 : Nat := 118140960795 + 802876 * 2 ^ 59
def prefixEnd_802876 : Nat := 4983230072969 + 3 ^ 40 * 802876 * 2
def baseEnd_802876 : Nat := 274840862639537318438431

theorem tailTrace_802876 : CollatzResearch.WordTrace tailWord_802876 prefixEnd_802876 274840862639537318438431 := by
  unfold tailWord_802876
  simp only [CollatzResearch.WordTrace]
  refine ⟨14641646719662423574602241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19522195626216564766136321 14641646719662423574602241)
  ·
    refine ⟨10981235039746817680951681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14641646719662423574602241 10981235039746817680951681)
    ·
      refine ⟨8235926279810113260713761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10981235039746817680951681 8235926279810113260713761)
      ·
        refine ⟨6176944709857584945535321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8235926279810113260713761 6176944709857584945535321)
        ·
          refine ⟨4632708532393188709151491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6176944709857584945535321 4632708532393188709151491)
          ·
            refine ⟨6949062798589783063727237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4632708532393188709151491 6949062798589783063727237)
            ·
              refine ⟨1302949274735584324448857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6949062798589783063727237 1302949274735584324448857)
              ·
                refine ⟨977211956051688243336643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1302949274735584324448857 977211956051688243336643)
                ·
                  refine ⟨1465817934077532365004965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 977211956051688243336643 1465817934077532365004965)
                  ·
                    refine ⟨274840862639537318438431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1465817934077532365004965 274840862639537318438431)
                    ·
                      rfl

theorem cell22_802876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 2, 1, 4].length) (baseStart_802876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_802876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_802876 prefixEnd_802876 := by exact prefixLift 802876
  have htrace : WordTrace (prefixWord ++ tailWord_802876) baseStart_802876 baseEnd_802876 := by
    simpa [prefixWord, tailWord_802876, baseEnd_802876] using wordTrace_append hprefix tailTrace_802876
  have hstable : (prefixWord ++ tailWord_802876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802876).length < 2 ^ (prefixWord ++ tailWord_802876).sum := by decide
  have hdescent : baseEnd_802876 < baseStart_802876 := by decide
  rcases family_descends (prefixWord ++ tailWord_802876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802889 : List Nat := [1, 2, 1, 1, 2, 2, 3, 1, 6, 3]
def baseStart_802889 : Nat := 118140960795 + 802889 * 2 ^ 59
def prefixEnd_802889 : Nat := 4983230072969 + 3 ^ 40 * 802889 * 2
def baseEnd_802889 : Nat := 274845312805209617863391

theorem tailTrace_802889 : CollatzResearch.WordTrace tailWord_802889 prefixEnd_802889 274845312805209617863391 := by
  unfold tailWord_802889
  simp only [CollatzResearch.WordTrace]
  refine ⟨29283767588277750369427721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19522511725518500246285147 29283767588277750369427721)
  ·
    refine ⟨21962825691208312777070791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29283767588277750369427721 21962825691208312777070791)
    ·
      refine ⟨32944238536812469165606187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21962825691208312777070791 32944238536812469165606187)
      ·
        refine ⟨49416357805218703748409281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32944238536812469165606187 49416357805218703748409281)
        ·
          refine ⟨37062268353914027811306961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49416357805218703748409281 37062268353914027811306961)
          ·
            refine ⟨27796701265435520858480221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37062268353914027811306961 27796701265435520858480221)
            ·
              refine ⟨10423762974538320321930083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27796701265435520858480221 10423762974538320321930083)
              ·
                refine ⟨15635644461807480482895125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10423762974538320321930083 15635644461807480482895125)
                ·
                  refine ⟨732920834147225647635709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 15635644461807480482895125 732920834147225647635709)
                  ·
                    refine ⟨274845312805209617863391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 732920834147225647635709 274845312805209617863391)
                    ·
                      rfl

theorem cell22_802889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 6, 3].length) (baseStart_802889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_802889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_802889 prefixEnd_802889 := by exact prefixLift 802889
  have htrace : WordTrace (prefixWord ++ tailWord_802889) baseStart_802889 baseEnd_802889 := by
    simpa [prefixWord, tailWord_802889, baseEnd_802889] using wordTrace_append hprefix tailTrace_802889
  have hstable : (prefixWord ++ tailWord_802889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802889).length < 2 ^ (prefixWord ++ tailWord_802889).sum := by decide
  have hdescent : baseEnd_802889 < baseStart_802889 := by decide
  rcases family_descends (prefixWord ++ tailWord_802889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802904 : List Nat := [2, 1, 2, 2, 1, 4, 1, 1, 4, 4]
def baseStart_802904 : Nat := 118140960795 + 802904 * 2 ^ 59
def prefixEnd_802904 : Nat := 4983230072969 + 3 ^ 40 * 802904 * 2
def baseEnd_802904 : Nat := 274850447611754578738345

theorem tailTrace_802904 : CollatzResearch.WordTrace tailWord_802904 prefixEnd_802904 274850447611754578738345 := by
  unfold tailWord_802904
  simp only [CollatzResearch.WordTrace]
  refine ⟨14642157341611703965611883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19522876455482271954149177 14642157341611703965611883)
  ·
    refine ⟨21963236012417555948417825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14642157341611703965611883 21963236012417555948417825)
    ·
      refine ⟨16472427009313166961313369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21963236012417555948417825 16472427009313166961313369)
      ·
        refine ⟨12354320256984875220985027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16472427009313166961313369 12354320256984875220985027)
        ·
          refine ⟨18531480385477312831477541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12354320256984875220985027 18531480385477312831477541)
          ·
            refine ⟨3474652572276996155902039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18531480385477312831477541 3474652572276996155902039)
            ·
              refine ⟨5211978858415494233853059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3474652572276996155902039 5211978858415494233853059)
              ·
                refine ⟨7817968287623241350779589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5211978858415494233853059 7817968287623241350779589)
                ·
                  refine ⟨1465869053929357753271173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7817968287623241350779589 1465869053929357753271173)
                  ·
                    refine ⟨274850447611754578738345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1465869053929357753271173 274850447611754578738345)
                    ·
                      rfl

theorem cell22_802904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 4, 4].length) (baseStart_802904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_802904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_802904 prefixEnd_802904 := by exact prefixLift 802904
  have htrace : WordTrace (prefixWord ++ tailWord_802904) baseStart_802904 baseEnd_802904 := by
    simpa [prefixWord, tailWord_802904, baseEnd_802904] using wordTrace_append hprefix tailTrace_802904
  have hstable : (prefixWord ++ tailWord_802904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802904).length < 2 ^ (prefixWord ++ tailWord_802904).sum := by decide
  have hdescent : baseEnd_802904 < baseStart_802904 := by decide
  rcases family_descends (prefixWord ++ tailWord_802904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802906 : List Nat := [3, 1, 1, 2, 1, 1, 4, 4, 2, 3]
def baseStart_802906 : Nat := 118140960795 + 802906 * 2 ^ 59
def prefixEnd_802906 : Nat := 4983230072969 + 3 ^ 40 * 802906 * 2
def baseEnd_802906 : Nat := 274851132252627240188339

theorem tailTrace_802906 : CollatzResearch.WordTrace tailWord_802906 prefixEnd_802906 274851132252627240188339 := by
  unfold tailWord_802906
  simp only [CollatzResearch.WordTrace]
  refine ⟨7321096907304040568199143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19522925086144108181864381 7321096907304040568199143)
  ·
    refine ⟨10981645360956060852298715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7321096907304040568199143 10981645360956060852298715)
    ·
      refine ⟨16472468041434091278448073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10981645360956060852298715 16472468041434091278448073)
      ·
        refine ⟨12354351031075568458836055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16472468041434091278448073 12354351031075568458836055)
        ·
          refine ⟨18531526546613352688254083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12354351031075568458836055 18531526546613352688254083)
          ·
            refine ⟨27797289819920029032381125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18531526546613352688254083 27797289819920029032381125)
            ·
              refine ⟨5211991841235005443571461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27797289819920029032381125 5211991841235005443571461)
              ·
                refine ⟨977248470231563520669649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5211991841235005443571461 977248470231563520669649)
                ·
                  refine ⟨732936352673672640502237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 977248470231563520669649 732936352673672640502237)
                  ·
                    refine ⟨274851132252627240188339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 732936352673672640502237 274851132252627240188339)
                    ·
                      rfl

theorem cell22_802906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 4, 2, 3].length) (baseStart_802906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_802906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_802906 prefixEnd_802906 := by exact prefixLift 802906
  have htrace : WordTrace (prefixWord ++ tailWord_802906) baseStart_802906 baseEnd_802906 := by
    simpa [prefixWord, tailWord_802906, baseEnd_802906] using wordTrace_append hprefix tailTrace_802906
  have hstable : (prefixWord ++ tailWord_802906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802906).length < 2 ^ (prefixWord ++ tailWord_802906).sum := by decide
  have hdescent : baseEnd_802906 < baseStart_802906 := by decide
  rcases family_descends (prefixWord ++ tailWord_802906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802919 : List Nat := [1, 1, 5, 1, 1, 2, 4, 7]
def baseStart_802919 : Nat := 118140960795 + 802919 * 2 ^ 59
def prefixEnd_802919 : Nat := 4983230072969 + 3 ^ 40 * 802919 * 2
def baseEnd_802919 : Nat := 30539509157588837734811

theorem tailTrace_802919 : CollatzResearch.WordTrace tailWord_802919 prefixEnd_802919 30539509157588837734811 := by
  unfold tailWord_802919
  simp only [CollatzResearch.WordTrace]
  refine ⟨29284861778169065493019811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19523241185446043662013207 29284861778169065493019811)
  ·
    refine ⟨43927292667253598239529717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29284861778169065493019811 43927292667253598239529717)
    ·
      refine ⟨4118183687555024834955911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43927292667253598239529717 4118183687555024834955911)
      ·
        refine ⟨6177275531332537252433867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4118183687555024834955911 6177275531332537252433867)
        ·
          refine ⟨9265913296998805878650801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6177275531332537252433867 9265913296998805878650801)
          ·
            refine ⟨6949434972749104408988101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9265913296998805878650801 6949434972749104408988101)
            ·
              refine ⟨1303019057390457076685269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6949434972749104408988101 1303019057390457076685269)
              ·
                refine ⟨30539509157588837734811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1303019057390457076685269 30539509157588837734811)
                ·
                  rfl

theorem cell22_802919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 7].length) (baseStart_802919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_802919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_802919 prefixEnd_802919 := by exact prefixLift 802919
  have htrace : WordTrace (prefixWord ++ tailWord_802919) baseStart_802919 baseEnd_802919 := by
    simpa [prefixWord, tailWord_802919, baseEnd_802919] using wordTrace_append hprefix tailTrace_802919
  have hstable : (prefixWord ++ tailWord_802919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802919).length < 2 ^ (prefixWord ++ tailWord_802919).sum := by decide
  have hdescent : baseEnd_802919 < baseStart_802919 := by decide
  rcases family_descends (prefixWord ++ tailWord_802919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803026 : List Nat := [3, 2, 2, 2, 1, 2, 1, 3, 6]
def baseStart_803026 : Nat := 118140960795 + 803026 * 2 ^ 59
def prefixEnd_803026 : Nat := 4983230072969 + 3 ^ 40 * 803026 * 2
def baseEnd_803026 : Nat := 91630736901662309062657

theorem tailTrace_803026 : CollatzResearch.WordTrace tailWord_803026 prefixEnd_803026 91630736901662309062657 := by
  unfold tailWord_803026
  simp only [CollatzResearch.WordTrace]
  refine ⟨7322191097195355691791233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19525842925854281844776621 7322191097195355691791233)
  ·
    refine ⟨5491643322896516768843425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7322191097195355691791233 5491643322896516768843425)
    ·
      refine ⟨4118732492172387576632569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5491643322896516768843425 4118732492172387576632569)
      ·
        refine ⟨3089049369129290682474427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4118732492172387576632569 3089049369129290682474427)
        ·
          refine ⟨4633574053693936023711641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3089049369129290682474427 4633574053693936023711641)
          ·
            refine ⟨3475180540270452017783731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4633574053693936023711641 3475180540270452017783731)
            ·
              refine ⟨5212770810405678026675597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3475180540270452017783731 5212770810405678026675597)
              ·
                refine ⟨1954789053902129260003349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5212770810405678026675597 1954789053902129260003349)
                ·
                  refine ⟨91630736901662309062657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1954789053902129260003349 91630736901662309062657)
                  ·
                    rfl

theorem cell22_803026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 3, 6].length) (baseStart_803026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_803026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_803026 prefixEnd_803026 := by exact prefixLift 803026
  have htrace : WordTrace (prefixWord ++ tailWord_803026) baseStart_803026 baseEnd_803026 := by
    simpa [prefixWord, tailWord_803026, baseEnd_803026] using wordTrace_append hprefix tailTrace_803026
  have hstable : (prefixWord ++ tailWord_803026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803026).length < 2 ^ (prefixWord ++ tailWord_803026).sum := by decide
  have hdescent : baseEnd_803026 < baseStart_803026 := by decide
  rcases family_descends (prefixWord ++ tailWord_803026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803058 : List Nat := [3, 2, 1, 3, 2, 1, 1, 2, 4, 3]
def baseStart_803058 : Nat := 118140960795 + 803058 * 2 ^ 59
def prefixEnd_803058 : Nat := 4983230072969 + 3 ^ 40 * 803058 * 2
def baseEnd_803058 : Nat := 274903164958949510387873

theorem tailTrace_803058 : CollatzResearch.WordTrace tailWord_803058 prefixEnd_803058 274903164958949510387873 := by
  unfold tailWord_803058
  simp only [CollatzResearch.WordTrace]
  refine ⟨7322482881166373058082457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19526621016443661488219885 7322482881166373058082457)
  ·
    refine ⟨5491862160874779793561843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7322482881166373058082457 5491862160874779793561843)
    ·
      refine ⟨8237793241312169690342765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5491862160874779793561843 8237793241312169690342765)
      ·
        refine ⟨3089172465492063633878537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8237793241312169690342765 3089172465492063633878537)
        ·
          refine ⟨2316879349119047725408903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3089172465492063633878537 2316879349119047725408903)
          ·
            refine ⟨3475319023678571588113355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2316879349119047725408903 3475319023678571588113355)
            ·
              refine ⟨5212978535517857382170033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3475319023678571588113355 5212978535517857382170033)
              ·
                refine ⟨3909733901638393036627525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5212978535517857382170033 3909733901638393036627525)
                ·
                  refine ⟨733075106557198694367661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3909733901638393036627525 733075106557198694367661)
                  ·
                    refine ⟨274903164958949510387873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 733075106557198694367661 274903164958949510387873)
                    ·
                      rfl

theorem cell22_803058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 2, 4, 3].length) (baseStart_803058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_803058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_803058 prefixEnd_803058 := by exact prefixLift 803058
  have htrace : WordTrace (prefixWord ++ tailWord_803058) baseStart_803058 baseEnd_803058 := by
    simpa [prefixWord, tailWord_803058, baseEnd_803058] using wordTrace_append hprefix tailTrace_803058
  have hstable : (prefixWord ++ tailWord_803058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803058).length < 2 ^ (prefixWord ++ tailWord_803058).sum := by decide
  have hdescent : baseEnd_803058 < baseStart_803058 := by decide
  rcases family_descends (prefixWord ++ tailWord_803058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803180 : List Nat := [2, 2, 1, 1, 6, 1, 1, 3, 1, 4]
def baseStart_803180 : Nat := 118140960795 + 803180 * 2 ^ 59
def prefixEnd_803180 : Nat := 4983230072969 + 3 ^ 40 * 803180 * 2
def baseEnd_803180 : Nat := 274944928052181858837499

theorem tailTrace_803180 : CollatzResearch.WordTrace tailWord_803180 prefixEnd_803180 274944928052181858837499 := by
  unfold tailWord_803180
  simp only [CollatzResearch.WordTrace]
  refine ⟨14647190615111753534135497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19529587486815671378847329 14647190615111753534135497)
  ·
    refine ⟨10985392961333815150601623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14647190615111753534135497 10985392961333815150601623)
    ·
      refine ⟨16478089442000722725902435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10985392961333815150601623 16478089442000722725902435)
      ·
        refine ⟨24717134163001084088853653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16478089442000722725902435 24717134163001084088853653)
        ·
          refine ⟨1158615663890675816665015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 24717134163001084088853653 1158615663890675816665015)
          ·
            refine ⟨1737923495836013724997523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1158615663890675816665015 1737923495836013724997523)
            ·
              refine ⟨2606885243754020587496285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1737923495836013724997523 2606885243754020587496285)
              ·
                refine ⟨977581966407757720311107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2606885243754020587496285 977581966407757720311107)
                ·
                  refine ⟨1466372949611636580466661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 977581966407757720311107 1466372949611636580466661)
                  ·
                    refine ⟨274944928052181858837499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1466372949611636580466661 274944928052181858837499)
                    ·
                      rfl

theorem cell22_803180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 4].length) (baseStart_803180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_803180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_803180 prefixEnd_803180 := by exact prefixLift 803180
  have htrace : WordTrace (prefixWord ++ tailWord_803180) baseStart_803180 baseEnd_803180 := by
    simpa [prefixWord, tailWord_803180, baseEnd_803180] using wordTrace_append hprefix tailTrace_803180
  have hstable : (prefixWord ++ tailWord_803180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803180).length < 2 ^ (prefixWord ++ tailWord_803180).sum := by decide
  have hdescent : baseEnd_803180 < baseStart_803180 := by decide
  rcases family_descends (prefixWord ++ tailWord_803180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803221 : List Nat := [1, 3, 2, 1, 1, 2, 1, 1, 1, 9]
def baseStart_803221 : Nat := 118140960795 + 803221 * 2 ^ 59
def prefixEnd_803221 : Nat := 4983230072969 + 3 ^ 40 * 803221 * 2
def baseEnd_803221 : Nat := 274958963190071418562373

theorem tailTrace_803221 : CollatzResearch.WordTrace tailWord_803221 prefixEnd_803221 274958963190071418562373 := by
  unfold tailWord_803221
  simp only [CollatzResearch.WordTrace]
  refine ⟨29295876623074971070513517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19530584415383314047009011 29295876623074971070513517)
  ·
    refine ⟨10985953733653114151442569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29295876623074971070513517 10985953733653114151442569)
    ·
      refine ⟨8239465300239835613581927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10985953733653114151442569 8239465300239835613581927)
      ·
        refine ⟨12359197950359753420372891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8239465300239835613581927 12359197950359753420372891)
        ·
          refine ⟨18538796925539630130559337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12359197950359753420372891 18538796925539630130559337)
          ·
            refine ⟨13904097694154722597919503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18538796925539630130559337 13904097694154722597919503)
            ·
              refine ⟨20856146541232083896879255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13904097694154722597919503 20856146541232083896879255)
              ·
                refine ⟨31284219811848125845318883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20856146541232083896879255 31284219811848125845318883)
                ·
                  refine ⟨46926329717772188767978325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31284219811848125845318883 46926329717772188767978325)
                  ·
                    refine ⟨274958963190071418562373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 46926329717772188767978325 274958963190071418562373)
                    ·
                      rfl

theorem cell22_803221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 9].length) (baseStart_803221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_803221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_803221 prefixEnd_803221 := by exact prefixLift 803221
  have htrace : WordTrace (prefixWord ++ tailWord_803221) baseStart_803221 baseEnd_803221 := by
    simpa [prefixWord, tailWord_803221, baseEnd_803221] using wordTrace_append hprefix tailTrace_803221
  have hstable : (prefixWord ++ tailWord_803221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803221).length < 2 ^ (prefixWord ++ tailWord_803221).sum := by decide
  have hdescent : baseEnd_803221 < baseStart_803221 := by decide
  rcases family_descends (prefixWord ++ tailWord_803221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803223 : List Nat := [1, 1, 3, 3, 1, 1, 6, 6]
def baseStart_803223 : Nat := 118140960795 + 803223 * 2 ^ 59
def prefixEnd_803223 : Nat := 4983230072969 + 3 ^ 40 * 803223 * 2
def baseEnd_803223 : Nat := 30551071981216008890263

theorem tailTrace_803223 : CollatzResearch.WordTrace tailWord_803223 prefixEnd_803223 30551071981216008890263 := by
  unfold tailWord_803223
  simp only [CollatzResearch.WordTrace]
  refine ⟨29295949569067725412086323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19530633046045150274724215 29295949569067725412086323)
  ·
    refine ⟨43943924353601588118129485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29295949569067725412086323 43943924353601588118129485)
    ·
      refine ⟨16478971632600595544298557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43943924353601588118129485 16478971632600595544298557)
      ·
        refine ⟨6179614362225223329111959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16478971632600595544298557 6179614362225223329111959)
        ·
          refine ⟨9269421543337834993667939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6179614362225223329111959 9269421543337834993667939)
          ·
            refine ⟨13904132315006752490501909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9269421543337834993667939 13904132315006752490501909)
            ·
              refine ⟨651756202265941522992277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13904132315006752490501909 651756202265941522992277)
              ·
                refine ⟨30551071981216008890263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 651756202265941522992277 30551071981216008890263)
                ·
                  rfl

theorem cell22_803223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 6, 6].length) (baseStart_803223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_803223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_803223 prefixEnd_803223 := by exact prefixLift 803223
  have htrace : WordTrace (prefixWord ++ tailWord_803223) baseStart_803223 baseEnd_803223 := by
    simpa [prefixWord, tailWord_803223, baseEnd_803223] using wordTrace_append hprefix tailTrace_803223
  have hstable : (prefixWord ++ tailWord_803223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803223).length < 2 ^ (prefixWord ++ tailWord_803223).sum := by decide
  have hdescent : baseEnd_803223 < baseStart_803223 := by decide
  rcases family_descends (prefixWord ++ tailWord_803223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803229 : List Nat := [1, 4, 2, 1, 5, 1, 1, 3, 4]
def baseStart_803229 : Nat := 118140960795 + 803229 * 2 ^ 59
def prefixEnd_803229 : Nat := 4983230072969 + 3 ^ 40 * 803229 * 2
def baseEnd_803229 : Nat := 91653900584520688120783

theorem tailTrace_803229 : CollatzResearch.WordTrace tailWord_803229 prefixEnd_803229 91653900584520688120783 := by
  unfold tailWord_803229
  simp only [CollatzResearch.WordTrace]
  refine ⟨29296168407045988436804741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19530778938030658957869827 29296168407045988436804741)
  ·
    refine ⟨5493031576321122831900889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29296168407045988436804741 5493031576321122831900889)
    ·
      refine ⟨4119773682240842123925667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5493031576321122831900889 4119773682240842123925667)
      ·
        refine ⟨6179660523361263185888501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4119773682240842123925667 6179660523361263185888501)
        ·
          refine ⟨579343174065118423677047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6179660523361263185888501 579343174065118423677047)
          ·
            refine ⟨869014761097677635515571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 579343174065118423677047 869014761097677635515571)
            ·
              refine ⟨1303522141646516453273357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 869014761097677635515571 1303522141646516453273357)
              ·
                refine ⟨488820803117443669977509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1303522141646516453273357 488820803117443669977509)
                ·
                  refine ⟨91653900584520688120783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 488820803117443669977509 91653900584520688120783)
                  ·
                    rfl

theorem cell22_803229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 3, 4].length) (baseStart_803229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_803229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_803229 prefixEnd_803229 := by exact prefixLift 803229
  have htrace : WordTrace (prefixWord ++ tailWord_803229) baseStart_803229 baseEnd_803229 := by
    simpa [prefixWord, tailWord_803229, baseEnd_803229] using wordTrace_append hprefix tailTrace_803229
  have hstable : (prefixWord ++ tailWord_803229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803229).length < 2 ^ (prefixWord ++ tailWord_803229).sum := by decide
  have hdescent : baseEnd_803229 < baseStart_803229 := by decide
  rcases family_descends (prefixWord ++ tailWord_803229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803240 : List Nat := [2, 1, 6, 1, 1, 3, 8]
def baseStart_803240 : Nat := 118140960795 + 803240 * 2 ^ 59
def prefixEnd_803240 : Nat := 4983230072969 + 3 ^ 40 * 803240 * 2
def baseEnd_803240 : Nat := 10183906195494877864345

theorem tailTrace_803240 : CollatzResearch.WordTrace tailWord_803240 prefixEnd_803240 10183906195494877864345 := by
  unfold tailWord_803240
  simp only [CollatzResearch.WordTrace]
  refine ⟨14648284805003068657727587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19531046406670758210303449 14648284805003068657727587)
  ·
    refine ⟨21972427207504602986591381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14648284805003068657727587 21972427207504602986591381)
    ·
      refine ⟨1029957525351778264996471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 21972427207504602986591381 1029957525351778264996471)
      ·
        refine ⟨1544936288027667397494707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1029957525351778264996471 1544936288027667397494707)
        ·
          refine ⟨2317404432041501096242061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1544936288027667397494707 2317404432041501096242061)
          ·
            refine ⟨869026662015562911090773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2317404432041501096242061 869026662015562911090773)
            ·
              refine ⟨10183906195494877864345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 869026662015562911090773 10183906195494877864345)
              ·
                rfl

theorem cell22_803240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 8].length) (baseStart_803240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_803240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_803240 prefixEnd_803240 := by exact prefixLift 803240
  have htrace : WordTrace (prefixWord ++ tailWord_803240) baseStart_803240 baseEnd_803240 := by
    simpa [prefixWord, tailWord_803240, baseEnd_803240] using wordTrace_append hprefix tailTrace_803240
  have hstable : (prefixWord ++ tailWord_803240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803240).length < 2 ^ (prefixWord ++ tailWord_803240).sum := by decide
  have hdescent : baseEnd_803240 < baseStart_803240 := by decide
  rcases family_descends (prefixWord ++ tailWord_803240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803255 : List Nat := [1, 1, 3, 1, 3, 3, 3, 1, 3, 3]
def baseStart_803255 : Nat := 118140960795 + 803255 * 2 ^ 59
def prefixEnd_803255 : Nat := 4983230072969 + 3 ^ 40 * 803255 * 2
def baseEnd_803255 : Nat := 274970602084906663212269

theorem tailTrace_803255 : CollatzResearch.WordTrace tailWord_803255 prefixEnd_803255 274970602084906663212269 := by
  unfold tailWord_803255
  simp only [CollatzResearch.WordTrace]
  refine ⟨29297116704951794877251219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19531411136634529918167479 29297116704951794877251219)
  ·
    refine ⟨43945675057427692315876829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29297116704951794877251219 43945675057427692315876829)
    ·
      refine ⟨16479628146535384618453811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43945675057427692315876829 16479628146535384618453811)
      ·
        refine ⟨24719442219803076927680717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16479628146535384618453811 24719442219803076927680717)
        ·
          refine ⟨9269790832426153847880269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24719442219803076927680717 9269790832426153847880269)
          ·
            refine ⟨3476171562159807692955101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9269790832426153847880269 3476171562159807692955101)
            ·
              refine ⟨1303564335809927884858163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3476171562159807692955101 1303564335809927884858163)
              ·
                refine ⟨1955346503714891827287245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1303564335809927884858163 1955346503714891827287245)
                ·
                  refine ⟨733254938893084435232717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1955346503714891827287245 733254938893084435232717)
                  ·
                    refine ⟨274970602084906663212269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 733254938893084435232717 274970602084906663212269)
                    ·
                      rfl

theorem cell22_803255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 1, 3, 3].length) (baseStart_803255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_803255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_803255 prefixEnd_803255 := by exact prefixLift 803255
  have htrace : WordTrace (prefixWord ++ tailWord_803255) baseStart_803255 baseEnd_803255 := by
    simpa [prefixWord, tailWord_803255, baseEnd_803255] using wordTrace_append hprefix tailTrace_803255
  have hstable : (prefixWord ++ tailWord_803255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803255).length < 2 ^ (prefixWord ++ tailWord_803255).sum := by decide
  have hdescent : baseEnd_803255 < baseStart_803255 := by decide
  rcases family_descends (prefixWord ++ tailWord_803255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803306 : List Nat := [3, 1, 3, 1, 3, 3, 2, 2, 1, 3]
def baseStart_803306 : Nat := 118140960795 + 803306 * 2 ^ 59
def prefixEnd_803306 : Nat := 4983230072969 + 3 ^ 40 * 803306 * 2
def baseEnd_803306 : Nat := 274988060427159530187113

theorem tailTrace_803306 : CollatzResearch.WordTrace tailWord_803306 prefixEnd_803306 274988060427159530187113 := by
  unfold tailWord_803306
  simp only [CollatzResearch.WordTrace]
  refine ⟨7324744206941757646839443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19532651218511353724905181 7324744206941757646839443)
  ·
    refine ⟨10987116310412636470259165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7324744206941757646839443 10987116310412636470259165)
    ·
      refine ⟨4120168616404738676347187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10987116310412636470259165 4120168616404738676347187)
      ·
        refine ⟨6180252924607108014520781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4120168616404738676347187 6180252924607108014520781)
        ·
          refine ⟨2317594846727665505445293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6180252924607108014520781 2317594846727665505445293)
          ·
            refine ⟨869098067522874564541985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2317594846727665505445293 869098067522874564541985)
            ·
              refine ⟨651823550642155923406489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 869098067522874564541985 651823550642155923406489)
              ·
                refine ⟨488867662981616942554867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 651823550642155923406489 488867662981616942554867)
                ·
                  refine ⟨733301494472425413832301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 488867662981616942554867 733301494472425413832301)
                  ·
                    refine ⟨274988060427159530187113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 733301494472425413832301 274988060427159530187113)
                    ·
                      rfl

theorem cell22_803306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 2, 2, 1, 3].length) (baseStart_803306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_803306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_803306 prefixEnd_803306 := by exact prefixLift 803306
  have htrace : WordTrace (prefixWord ++ tailWord_803306) baseStart_803306 baseEnd_803306 := by
    simpa [prefixWord, tailWord_803306, baseEnd_803306] using wordTrace_append hprefix tailTrace_803306
  have hstable : (prefixWord ++ tailWord_803306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803306).length < 2 ^ (prefixWord ++ tailWord_803306).sum := by decide
  have hdescent : baseEnd_803306 < baseStart_803306 := by decide
  rcases family_descends (prefixWord ++ tailWord_803306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803313 : List Nat := [1, 2, 2, 2, 3, 1, 2, 3, 6]
def baseStart_803313 : Nat := 118140960795 + 803313 * 2 ^ 59
def prefixEnd_803313 : Nat := 4983230072969 + 3 ^ 40 * 803313 * 2
def baseEnd_803313 : Nat := 91663485556737948420697

theorem tailTrace_803313 : CollatzResearch.WordTrace tailWord_803313 prefixEnd_803313 91663485556737948420697 := by
  unfold tailWord_803313
  simp only [CollatzResearch.WordTrace]
  refine ⟨29299232138741670782862593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19532821425827780521908395 29299232138741670782862593)
  ·
    refine ⟨21974424104056253087146945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29299232138741670782862593 21974424104056253087146945)
    ·
      refine ⟨16480818078042189815360209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21974424104056253087146945 16480818078042189815360209)
      ·
        refine ⟨12360613558531642361520157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16480818078042189815360209 12360613558531642361520157)
        ·
          refine ⟨4635230084449365885570059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12360613558531642361520157 4635230084449365885570059)
          ·
            refine ⟨6952845126674048828355089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4635230084449365885570059 6952845126674048828355089)
            ·
              refine ⟨5214633845005536621266317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6952845126674048828355089 5214633845005536621266317)
              ·
                refine ⟨1955487691877076232974869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5214633845005536621266317 1955487691877076232974869)
                ·
                  refine ⟨91663485556737948420697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1955487691877076232974869 91663485556737948420697)
                  ·
                    rfl

theorem cell22_803313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 3, 6].length) (baseStart_803313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_803313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_803313 prefixEnd_803313 := by exact prefixLift 803313
  have htrace : WordTrace (prefixWord ++ tailWord_803313) baseStart_803313 baseEnd_803313 := by
    simpa [prefixWord, tailWord_803313, baseEnd_803313] using wordTrace_append hprefix tailTrace_803313
  have hstable : (prefixWord ++ tailWord_803313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803313).length < 2 ^ (prefixWord ++ tailWord_803313).sum := by decide
  have hdescent : baseEnd_803313 < baseStart_803313 := by decide
  rcases family_descends (prefixWord ++ tailWord_803313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803317 : List Nat := [1, 3, 5, 1, 2, 1, 1, 1, 2, 5]
def baseStart_803317 : Nat := 118140960795 + 803317 * 2 ^ 59
def prefixEnd_803317 : Nat := 4983230072969 + 3 ^ 40 * 803317 * 2
def baseEnd_803317 : Nat := 274991825951959168162079

theorem tailTrace_803317 : CollatzResearch.WordTrace tailWord_803317 prefixEnd_803317 274991825951959168162079 := by
  unfold tailWord_803317
  simp only [CollatzResearch.WordTrace]
  refine ⟨29299378030727179466008205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19532918687151452977338803 29299378030727179466008205)
  ·
    refine ⟨10987266761522692299753077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29299378030727179466008205 10987266761522692299753077)
    ·
      refine ⟨1030056258892752403101851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10987266761522692299753077 1030056258892752403101851)
      ·
        refine ⟨1545084388339128604652777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1030056258892752403101851 1545084388339128604652777)
        ·
          refine ⟨1158813291254346453489583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1545084388339128604652777 1158813291254346453489583)
          ·
            refine ⟨1738219936881519680234375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1158813291254346453489583 1738219936881519680234375)
            ·
              refine ⟨2607329905322279520351563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1738219936881519680234375 2607329905322279520351563)
              ·
                refine ⟨3910994857983419280527345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2607329905322279520351563 3910994857983419280527345)
                ·
                  refine ⟨2933246143487564460395509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3910994857983419280527345 2933246143487564460395509)
                  ·
                    refine ⟨274991825951959168162079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2933246143487564460395509 274991825951959168162079)
                    ·
                      rfl

theorem cell22_803317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_803317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_803317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_803317 prefixEnd_803317 := by exact prefixLift 803317
  have htrace : WordTrace (prefixWord ++ tailWord_803317) baseStart_803317 baseEnd_803317 := by
    simpa [prefixWord, tailWord_803317, baseEnd_803317] using wordTrace_append hprefix tailTrace_803317
  have hstable : (prefixWord ++ tailWord_803317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803317).length < 2 ^ (prefixWord ++ tailWord_803317).sum := by decide
  have hdescent : baseEnd_803317 < baseStart_803317 := by decide
  rcases family_descends (prefixWord ++ tailWord_803317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803403 : List Nat := [1, 1, 1, 1, 3, 1, 5, 2, 7]
def baseStart_803403 : Nat := 118140960795 + 803403 * 2 ^ 59
def prefixEnd_803403 : Nat := 4983230072969 + 3 ^ 40 * 803403 * 2
def baseEnd_803403 : Nat := 91673755169827870170605

theorem tailTrace_803403 : CollatzResearch.WordTrace tailWord_803403 prefixEnd_803403 91673755169827870170605 := by
  unfold tailWord_803403
  simp only [CollatzResearch.WordTrace]
  refine ⟨29302514708415616153638863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19535009805610410769092575 29302514708415616153638863)
  ·
    refine ⟨43953772062623424230458295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29302514708415616153638863 43953772062623424230458295)
    ·
      refine ⟨65930658093935136345687443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43953772062623424230458295 65930658093935136345687443)
      ·
        refine ⟨98895987140902704518531165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65930658093935136345687443 98895987140902704518531165)
        ·
          refine ⟨37085995177838514194449187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98895987140902704518531165 37085995177838514194449187)
          ·
            refine ⟨55628992766757771291673781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37085995177838514194449187 55628992766757771291673781)
            ·
              refine ⟨5215218071883541058594417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55628992766757771291673781 5215218071883541058594417)
              ·
                refine ⟨3911413553912655793945813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5215218071883541058594417 3911413553912655793945813)
                ·
                  refine ⟨91673755169827870170605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3911413553912655793945813 91673755169827870170605)
                  ·
                    rfl

theorem cell22_803403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 7].length) (baseStart_803403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_803403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_803403 prefixEnd_803403 := by exact prefixLift 803403
  have htrace : WordTrace (prefixWord ++ tailWord_803403) baseStart_803403 baseEnd_803403 := by
    simpa [prefixWord, tailWord_803403, baseEnd_803403] using wordTrace_append hprefix tailTrace_803403
  have hstable : (prefixWord ++ tailWord_803403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803403).length < 2 ^ (prefixWord ++ tailWord_803403).sum := by decide
  have hdescent : baseEnd_803403 < baseStart_803403 := by decide
  rcases family_descends (prefixWord ++ tailWord_803403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803433 : List Nat := [1, 2, 1, 1, 1, 4, 1, 1, 2, 8]
def baseStart_803433 : Nat := 118140960795 + 803433 * 2 ^ 59
def prefixEnd_803433 : Nat := 4983230072969 + 3 ^ 40 * 803433 * 2
def baseEnd_803433 : Nat := 275031535122573532261723

theorem tailTrace_803433 : CollatzResearch.WordTrace tailWord_803433 prefixEnd_803433 275031535122573532261723 := by
  unfold tailWord_803433
  simp only [CollatzResearch.WordTrace]
  refine ⟨29303608898306931277230953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19535739265537954184820635 29303608898306931277230953)
  ·
    refine ⟨21977706673730198457923215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29303608898306931277230953 21977706673730198457923215)
    ·
      refine ⟨32966560010595297686884823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21977706673730198457923215 32966560010595297686884823)
      ·
        refine ⟨49449840015892946530327235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32966560010595297686884823 49449840015892946530327235)
        ·
          refine ⟨74174760023839419795490853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49449840015892946530327235 74174760023839419795490853)
          ·
            refine ⟨13907767504469891211654535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74174760023839419795490853 13907767504469891211654535)
            ·
              refine ⟨20861651256704836817481803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13907767504469891211654535 20861651256704836817481803)
              ·
                refine ⟨31292476885057255226222705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20861651256704836817481803 31292476885057255226222705)
                ·
                  refine ⟨23469357663792941419667029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31292476885057255226222705 23469357663792941419667029)
                  ·
                    refine ⟨275031535122573532261723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 23469357663792941419667029 275031535122573532261723)
                    ·
                      rfl

theorem cell22_803433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 8].length) (baseStart_803433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_803433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_803433 prefixEnd_803433 := by exact prefixLift 803433
  have htrace : WordTrace (prefixWord ++ tailWord_803433) baseStart_803433 baseEnd_803433 := by
    simpa [prefixWord, tailWord_803433, baseEnd_803433] using wordTrace_append hprefix tailTrace_803433
  have hstable : (prefixWord ++ tailWord_803433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803433).length < 2 ^ (prefixWord ++ tailWord_803433).sum := by decide
  have hdescent : baseEnd_803433 < baseStart_803433 := by decide
  rcases family_descends (prefixWord ++ tailWord_803433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803437 : List Nat := [1, 5, 1, 1, 3, 2, 1, 3, 5]
def baseStart_803437 : Nat := 118140960795 + 803437 * 2 ^ 59
def prefixEnd_803437 : Nat := 4983230072969 + 3 ^ 40 * 803437 * 2
def baseEnd_803437 : Nat := 91677634801439618387237

theorem tailTrace_803437 : CollatzResearch.WordTrace tailWord_803437 prefixEnd_803437 91677634801439618387237 := by
  unfold tailWord_803437
  simp only [CollatzResearch.WordTrace]
  refine ⟨29303754790292439960376565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19535836526861626640251043 29303754790292439960376565)
  ·
    refine ⟨2747227011589916246285303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29303754790292439960376565 2747227011589916246285303)
    ·
      refine ⟨4120840517384874369427955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2747227011589916246285303 4120840517384874369427955)
      ·
        refine ⟨6181260776077311554141933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4120840517384874369427955 6181260776077311554141933)
        ·
          refine ⟨2317972791028991832803225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6181260776077311554141933 2317972791028991832803225)
          ·
            refine ⟨1738479593271743874602419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2317972791028991832803225 1738479593271743874602419)
            ·
              refine ⟨2607719389907615811903629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1738479593271743874602419 2607719389907615811903629)
              ·
                refine ⟨977894771215355929463861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2607719389907615811903629 977894771215355929463861)
                ·
                  refine ⟨91677634801439618387237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 977894771215355929463861 91677634801439618387237)
                  ·
                    rfl

theorem cell22_803437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 3, 5].length) (baseStart_803437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_803437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_803437 prefixEnd_803437 := by exact prefixLift 803437
  have htrace : WordTrace (prefixWord ++ tailWord_803437) baseStart_803437 baseEnd_803437 := by
    simpa [prefixWord, tailWord_803437, baseEnd_803437] using wordTrace_append hprefix tailTrace_803437
  have hstable : (prefixWord ++ tailWord_803437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803437).length < 2 ^ (prefixWord ++ tailWord_803437).sum := by decide
  have hdescent : baseEnd_803437 < baseStart_803437 := by decide
  rcases family_descends (prefixWord ++ tailWord_803437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803480 : List Nat := [2, 1, 2, 4, 1, 1, 1, 2, 3, 5]
def baseStart_803480 : Nat := 118140960795 + 803480 * 2 ^ 59
def prefixEnd_803480 : Nat := 4983230072969 + 3 ^ 40 * 803480 * 2
def baseEnd_803480 : Nat := 275047624183081076336579

theorem tailTrace_803480 : CollatzResearch.WordTrace tailWord_803480 prefixEnd_803480 275047624183081076336579 := by
  unfold tailWord_803480
  simp only [CollatzResearch.WordTrace]
  refine ⟨14652661564568329152095947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19536882086091105536127929 14652661564568329152095947)
  ·
    refine ⟨21978992346852493728143921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14652661564568329152095947 21978992346852493728143921)
    ·
      refine ⟨16484244260139370296107941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21978992346852493728143921 16484244260139370296107941)
      ·
        refine ⟨3090795798776131930520239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16484244260139370296107941 3090795798776131930520239)
        ·
          refine ⟨4636193698164197895780359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3090795798776131930520239 4636193698164197895780359)
          ·
            refine ⟨6954290547246296843670539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4636193698164197895780359 6954290547246296843670539)
            ·
              refine ⟨10431435820869445265505809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6954290547246296843670539 10431435820869445265505809)
              ·
                refine ⟨7823576865652083949129357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10431435820869445265505809 7823576865652083949129357)
                ·
                  refine ⟨2933841324619531480923509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7823576865652083949129357 2933841324619531480923509)
                  ·
                    refine ⟨275047624183081076336579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2933841324619531480923509 275047624183081076336579)
                    ·
                      rfl

theorem cell22_803480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 3, 5].length) (baseStart_803480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_803480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_803480 prefixEnd_803480 := by exact prefixLift 803480
  have htrace : WordTrace (prefixWord ++ tailWord_803480) baseStart_803480 baseEnd_803480 := by
    simpa [prefixWord, tailWord_803480, baseEnd_803480] using wordTrace_append hprefix tailTrace_803480
  have hstable : (prefixWord ++ tailWord_803480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803480).length < 2 ^ (prefixWord ++ tailWord_803480).sum := by decide
  have hdescent : baseEnd_803480 < baseStart_803480 := by decide
  rcases family_descends (prefixWord ++ tailWord_803480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803548 : List Nat := [2, 2, 5, 1, 1, 2, 3, 1, 2, 3]
def baseStart_803548 : Nat := 118140960795 + 803548 * 2 ^ 59
def prefixEnd_803548 : Nat := 4983230072969 + 3 ^ 40 * 803548 * 2
def baseEnd_803548 : Nat := 275070901972751565636371

theorem tailTrace_803548 : CollatzResearch.WordTrace tailWord_803548 prefixEnd_803548 275070901972751565636371 := by
  unfold tailWord_803548
  simp only [CollatzResearch.WordTrace]
  refine ⟨14653901646445152958833649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19538535528593537278444865 14653901646445152958833649)
  ·
    refine ⟨10990426234833864719125237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14653901646445152958833649 10990426234833864719125237)
    ·
      refine ⟨1030352459515674817417991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10990426234833864719125237 1030352459515674817417991)
      ·
        refine ⟨1545528689273512226126987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1030352459515674817417991 1545528689273512226126987)
        ·
          refine ⟨2318293033910268339190481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1545528689273512226126987 2318293033910268339190481)
          ·
            refine ⟨1738719775432701254392861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2318293033910268339190481 1738719775432701254392861)
            ·
              refine ⟨652019915787262970397323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1738719775432701254392861 652019915787262970397323)
              ·
                refine ⟨978029873680894455595985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 652019915787262970397323 978029873680894455595985)
                ·
                  refine ⟨733522405260670841696989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 978029873680894455595985 733522405260670841696989)
                  ·
                    refine ⟨275070901972751565636371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 733522405260670841696989 275070901972751565636371)
                    ·
                      rfl

theorem cell22_803548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_803548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_803548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_803548 prefixEnd_803548 := by exact prefixLift 803548
  have htrace : WordTrace (prefixWord ++ tailWord_803548) baseStart_803548 baseEnd_803548 := by
    simpa [prefixWord, tailWord_803548, baseEnd_803548] using wordTrace_append hprefix tailTrace_803548
  have hstable : (prefixWord ++ tailWord_803548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803548).length < 2 ^ (prefixWord ++ tailWord_803548).sum := by decide
  have hdescent : baseEnd_803548 < baseStart_803548 := by decide
  rcases family_descends (prefixWord ++ tailWord_803548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803632 : List Nat := [2, 1, 1, 1, 2, 2, 1, 3, 6, 3]
def baseStart_803632 : Nat := 118140960795 + 803632 * 2 ^ 59
def prefixEnd_803632 : Nat := 4983230072969 + 3 ^ 40 * 803632 * 2
def baseEnd_803632 : Nat := 275099656889403346536113

theorem tailTrace_803632 : CollatzResearch.WordTrace tailWord_803632 prefixEnd_803632 275099656889403346536113 := by
  unfold tailWord_803632
  simp only [CollatzResearch.WordTrace]
  refine ⟨14655433512292994131862575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19540578016390658842483433 14655433512292994131862575)
  ·
    refine ⟨21983150268439491197793863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14655433512292994131862575 21983150268439491197793863)
    ·
      refine ⟨32974725402659236796690795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21983150268439491197793863 32974725402659236796690795)
      ·
        refine ⟨49462088103988855195036193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32974725402659236796690795 49462088103988855195036193)
        ·
          refine ⟨37096566077991641396277145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49462088103988855195036193 37096566077991641396277145)
          ·
            refine ⟨27822424558493731047207859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37096566077991641396277145 27822424558493731047207859)
            ·
              refine ⟨41733636837740596570811789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27822424558493731047207859 41733636837740596570811789)
              ·
                refine ⟨15650113814152723714054421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41733636837740596570811789 15650113814152723714054421)
                ·
                  refine ⟨733599085038408924096301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 15650113814152723714054421 733599085038408924096301)
                  ·
                    refine ⟨275099656889403346536113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 733599085038408924096301 275099656889403346536113)
                    ·
                      rfl

theorem cell22_803632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 6, 3].length) (baseStart_803632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_803632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_803632 prefixEnd_803632 := by exact prefixLift 803632
  have htrace : WordTrace (prefixWord ++ tailWord_803632) baseStart_803632 baseEnd_803632 := by
    simpa [prefixWord, tailWord_803632, baseEnd_803632] using wordTrace_append hprefix tailTrace_803632
  have hstable : (prefixWord ++ tailWord_803632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803632).length < 2 ^ (prefixWord ++ tailWord_803632).sum := by decide
  have hdescent : baseEnd_803632 < baseStart_803632 := by decide
  rcases family_descends (prefixWord ++ tailWord_803632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803634 : List Nat := [3, 2, 1, 1, 3, 1, 2, 5, 4]
def baseStart_803634 : Nat := 118140960795 + 803634 * 2 ^ 59
def prefixEnd_803634 : Nat := 4983230072969 + 3 ^ 40 * 803634 * 2
def baseEnd_803634 : Nat := 91700113843425335995369

theorem tailTrace_803634 : CollatzResearch.WordTrace tailWord_803634 prefixEnd_803634 91700113843425335995369 := by
  unfold tailWord_803634
  simp only [CollatzResearch.WordTrace]
  refine ⟨7327734992644685651324489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19540626647052495070198637 7327734992644685651324489)
  ·
    refine ⟨5495801244483514238493367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7327734992644685651324489 5495801244483514238493367)
    ·
      refine ⟨8243701866725271357740051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5495801244483514238493367 8243701866725271357740051)
      ·
        refine ⟨12365552800087907036610077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8243701866725271357740051 12365552800087907036610077)
        ·
          refine ⟨4637082300032965138728779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12365552800087907036610077 4637082300032965138728779)
          ·
            refine ⟨6955623450049447708093169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4637082300032965138728779 6955623450049447708093169)
            ·
              refine ⟨5216717587537085781069877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6955623450049447708093169 5216717587537085781069877)
              ·
                refine ⟨489067273831601791975301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5216717587537085781069877 489067273831601791975301)
                ·
                  refine ⟨91700113843425335995369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 489067273831601791975301 91700113843425335995369)
                  ·
                    rfl

theorem cell22_803634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 5, 4].length) (baseStart_803634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_803634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_803634 prefixEnd_803634 := by exact prefixLift 803634
  have htrace : WordTrace (prefixWord ++ tailWord_803634) baseStart_803634 baseEnd_803634 := by
    simpa [prefixWord, tailWord_803634, baseEnd_803634] using wordTrace_append hprefix tailTrace_803634
  have hstable : (prefixWord ++ tailWord_803634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803634).length < 2 ^ (prefixWord ++ tailWord_803634).sum := by decide
  have hdescent : baseEnd_803634 < baseStart_803634 := by decide
  rcases family_descends (prefixWord ++ tailWord_803634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803711 : List Nat := [1, 1, 2, 2, 1, 1, 6, 4, 1, 3]
def baseStart_803711 : Nat := 118140960795 + 803711 * 2 ^ 59
def prefixEnd_803711 : Nat := 4983230072969 + 3 ^ 40 * 803711 * 2
def baseEnd_803711 : Nat := 275126700203873473810871

theorem tailTrace_803711 : CollatzResearch.WordTrace tailWord_803711 prefixEnd_803711 275126700203873473810871 := by
  unfold tailWord_803711
  simp only [CollatzResearch.WordTrace]
  refine ⟨29313748391299784755850987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19542498927533189837233991 29313748391299784755850987)
  ·
    refine ⟨43970622586949677133776481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29313748391299784755850987 43970622586949677133776481)
    ·
      refine ⟨32977966940212257850332361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43970622586949677133776481 32977966940212257850332361)
      ·
        refine ⟨24733475205159193387749271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32977966940212257850332361 24733475205159193387749271)
        ·
          refine ⟨37100212807738790081623907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24733475205159193387749271 37100212807738790081623907)
          ·
            refine ⟨55650319211608185122435861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37100212807738790081623907 55650319211608185122435861)
            ·
              refine ⟨2608608713044133677614181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 55650319211608185122435861 2608608713044133677614181)
              ·
                refine ⟨489114133695775064552659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2608608713044133677614181 489114133695775064552659)
                ·
                  refine ⟨733671200543662596828989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 489114133695775064552659 733671200543662596828989)
                  ·
                    refine ⟨275126700203873473810871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 733671200543662596828989 275126700203873473810871)
                    ·
                      rfl

theorem cell22_803711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 4, 1, 3].length) (baseStart_803711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_803711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_803711 prefixEnd_803711 := by exact prefixLift 803711
  have htrace : WordTrace (prefixWord ++ tailWord_803711) baseStart_803711 baseEnd_803711 := by
    simpa [prefixWord, tailWord_803711, baseEnd_803711] using wordTrace_append hprefix tailTrace_803711
  have hstable : (prefixWord ++ tailWord_803711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803711).length < 2 ^ (prefixWord ++ tailWord_803711).sum := by decide
  have hdescent : baseEnd_803711 < baseStart_803711 := by decide
  rcases family_descends (prefixWord ++ tailWord_803711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803745 : List Nat := [1, 2, 3, 4, 1, 3, 1, 3, 1, 3]
def baseStart_803745 : Nat := 118140960795 + 803745 * 2 ^ 59
def prefixEnd_803745 : Nat := 4983230072969 + 3 ^ 40 * 803745 * 2
def baseEnd_803745 : Nat := 275138339098708718460767

theorem tailTrace_803745 : CollatzResearch.WordTrace tailWord_803745 prefixEnd_803745 275138339098708718460767 := by
  unfold tailWord_803745
  simp only [CollatzResearch.WordTrace]
  refine ⟨29314988473176608562588689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19543325648784405708392459 29314988473176608562588689)
  ·
    refine ⟨21986241354882456421941517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29314988473176608562588689 21986241354882456421941517)
    ·
      refine ⟨8244840508080921158228069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21986241354882456421941517 8244840508080921158228069)
      ·
        refine ⟨1545907595265172717167763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8244840508080921158228069 1545907595265172717167763)
        ·
          refine ⟨2318861392897759075751645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1545907595265172717167763 2318861392897759075751645)
          ·
            refine ⟨869573022336659653406867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2318861392897759075751645 869573022336659653406867)
            ·
              refine ⟨1304359533504989480110301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 869573022336659653406867 1304359533504989480110301)
              ·
                refine ⟨489134825064371055041363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1304359533504989480110301 489134825064371055041363)
                ·
                  refine ⟨733702237596556582562045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 489134825064371055041363 733702237596556582562045)
                  ·
                    refine ⟨275138339098708718460767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 733702237596556582562045 275138339098708718460767)
                    ·
                      rfl

theorem cell22_803745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 3, 1, 3].length) (baseStart_803745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_803745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_803745 prefixEnd_803745 := by exact prefixLift 803745
  have htrace : WordTrace (prefixWord ++ tailWord_803745) baseStart_803745 baseEnd_803745 := by
    simpa [prefixWord, tailWord_803745, baseEnd_803745] using wordTrace_append hprefix tailTrace_803745
  have hstable : (prefixWord ++ tailWord_803745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803745).length < 2 ^ (prefixWord ++ tailWord_803745).sum := by decide
  have hdescent : baseEnd_803745 < baseStart_803745 := by decide
  rcases family_descends (prefixWord ++ tailWord_803745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803769 : List Nat := [1, 2, 1, 4, 2, 2, 3, 1, 6]
def baseStart_803769 : Nat := 118140960795 + 803769 * 2 ^ 59
def prefixEnd_803769 : Nat := 4983230072969 + 3 ^ 40 * 803769 * 2
def baseEnd_803769 : Nat := 91715518263060218620231

theorem tailTrace_803769 : CollatzResearch.WordTrace tailWord_803769 prefixEnd_803769 91715518263060218620231 := by
  unfold tailWord_803769
  simp only [CollatzResearch.WordTrace]
  refine ⟨29315863825089660661462361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19543909216726440440974907 29315863825089660661462361)
  ·
    refine ⟨21986897868817245496096771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29315863825089660661462361 21986897868817245496096771)
    ·
      refine ⟨32980346803225868244145157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21986897868817245496096771 32980346803225868244145157)
      ·
        refine ⟨6183815025604850295777217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32980346803225868244145157 6183815025604850295777217)
        ·
          refine ⟨4637861269203637721832913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6183815025604850295777217 4637861269203637721832913)
          ·
            refine ⟨3478395951902728291374685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4637861269203637721832913 3478395951902728291374685)
            ·
              refine ⟨1304398481963523109265507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3478395951902728291374685 1304398481963523109265507)
              ·
                refine ⟨1956597722945284663898261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1304398481963523109265507 1956597722945284663898261)
                ·
                  refine ⟨91715518263060218620231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1956597722945284663898261 91715518263060218620231)
                  ·
                    rfl

theorem cell22_803769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 1, 6].length) (baseStart_803769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_803769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_803769 prefixEnd_803769 := by exact prefixLift 803769
  have htrace : WordTrace (prefixWord ++ tailWord_803769) baseStart_803769 baseEnd_803769 := by
    simpa [prefixWord, tailWord_803769, baseEnd_803769] using wordTrace_append hprefix tailTrace_803769
  have hstable : (prefixWord ++ tailWord_803769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803769).length < 2 ^ (prefixWord ++ tailWord_803769).sum := by decide
  have hdescent : baseEnd_803769 < baseStart_803769 := by decide
  rcases family_descends (prefixWord ++ tailWord_803769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803818 : List Nat := [3, 1, 3, 1, 2, 3, 2, 2, 2, 3]
def baseStart_803818 : Nat := 118140960795 + 803818 * 2 ^ 59
def prefixEnd_803818 : Nat := 4983230072969 + 3 ^ 40 * 803818 * 2
def baseEnd_803818 : Nat := 275163328490560861385543

theorem tailTrace_803818 : CollatzResearch.WordTrace tailWord_803818 prefixEnd_803818 275163328490560861385543 := by
  unfold tailWord_803818
  simp only [CollatzResearch.WordTrace]
  refine ⟨7329412750478035507499027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19545100667941428019997405 7329412750478035507499027)
  ·
    refine ⟨10994119125717053261248541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7329412750478035507499027 10994119125717053261248541)
    ·
      refine ⟨4122794672143894972968203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10994119125717053261248541 4122794672143894972968203)
      ·
        refine ⟨6184192008215842459452305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4122794672143894972968203 6184192008215842459452305)
        ·
          refine ⟨4638144006161881844589229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6184192008215842459452305 4638144006161881844589229)
          ·
            refine ⟨1739304002310705691720961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4638144006161881844589229 1739304002310705691720961)
            ·
              refine ⟨1304478001733029268790721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1739304002310705691720961 1304478001733029268790721)
              ·
                refine ⟨978358501299771951593041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1304478001733029268790721 978358501299771951593041)
                ·
                  refine ⟨733768875974828963694781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 978358501299771951593041 733768875974828963694781)
                  ·
                    refine ⟨275163328490560861385543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 733768875974828963694781 275163328490560861385543)
                    ·
                      rfl

theorem cell22_803818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 2, 2, 3].length) (baseStart_803818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_803818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_803818 prefixEnd_803818 := by exact prefixLift 803818
  have htrace : WordTrace (prefixWord ++ tailWord_803818) baseStart_803818 baseEnd_803818 := by
    simpa [prefixWord, tailWord_803818, baseEnd_803818] using wordTrace_append hprefix tailTrace_803818
  have hstable : (prefixWord ++ tailWord_803818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803818).length < 2 ^ (prefixWord ++ tailWord_803818).sum := by decide
  have hdescent : baseEnd_803818 < baseStart_803818 := by decide
  rcases family_descends (prefixWord ++ tailWord_803818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803876 : List Nat := [2, 3, 1, 4, 1, 2, 1, 1, 7]
def baseStart_803876 : Nat := 118140960795 + 803876 * 2 ^ 59
def prefixEnd_803876 : Nat := 4983230072969 + 3 ^ 40 * 803876 * 2
def baseEnd_803876 : Nat := 91727727691956014478455

theorem tailTrace_803876 : CollatzResearch.WordTrace tailWord_803876 prefixEnd_803876 91727727691956014478455 := by
  unfold tailWord_803876
  simp only [CollatzResearch.WordTrace]
  refine ⟨14659883217851008967803741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19546510957134678623738321 14659883217851008967803741)
  ·
    refine ⟨5497456206694128362926403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14659883217851008967803741 5497456206694128362926403)
    ·
      refine ⟨8246184310041192544389605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5497456206694128362926403 8246184310041192544389605)
      ·
        refine ⟨1546159558132723602073051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8246184310041192544389605 1546159558132723602073051)
        ·
          refine ⟨2319239337199085403109577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1546159558132723602073051 2319239337199085403109577)
          ·
            refine ⟨1739429502899314052332183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2319239337199085403109577 1739429502899314052332183)
            ·
              refine ⟨2609144254348971078498275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1739429502899314052332183 2609144254348971078498275)
              ·
                refine ⟨3913716381523456617747413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2609144254348971078498275 3913716381523456617747413)
                ·
                  refine ⟨91727727691956014478455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3913716381523456617747413 91727727691956014478455)
                  ·
                    rfl

theorem cell22_803876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 1, 7].length) (baseStart_803876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_803876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_803876 prefixEnd_803876 := by exact prefixLift 803876
  have htrace : WordTrace (prefixWord ++ tailWord_803876) baseStart_803876 baseEnd_803876 := by
    simpa [prefixWord, tailWord_803876, baseEnd_803876] using wordTrace_append hprefix tailTrace_803876
  have hstable : (prefixWord ++ tailWord_803876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803876).length < 2 ^ (prefixWord ++ tailWord_803876).sum := by decide
  have hdescent : baseEnd_803876 < baseStart_803876 := by decide
  rcases family_descends (prefixWord ++ tailWord_803876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803904 : List Nat := [2, 1, 1, 2, 2, 3, 1, 4, 6]
def baseStart_803904 : Nat := 118140960795 + 803904 * 2 ^ 59
def prefixEnd_803904 : Nat := 4983230072969 + 3 ^ 40 * 803904 * 2
def baseEnd_803904 : Nat := 91730922682695101245093

theorem tailTrace_803904 : CollatzResearch.WordTrace tailWord_803904 prefixEnd_803904 91730922682695101245093 := by
  unfold tailWord_803904
  simp only [CollatzResearch.WordTrace]
  refine ⟨14660393839800289358813383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19547191786400385811751177 14660393839800289358813383)
  ·
    refine ⟨21990590759700434038220075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14660393839800289358813383 21990590759700434038220075)
    ·
      refine ⟨32985886139550651057330113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21990590759700434038220075 32985886139550651057330113)
      ·
        refine ⟨24739414604662988292997585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32985886139550651057330113 24739414604662988292997585)
        ·
          refine ⟨18554560953497241219748189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24739414604662988292997585 18554560953497241219748189)
          ·
            refine ⟨6957960357561465457405571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18554560953497241219748189 6957960357561465457405571)
            ·
              refine ⟨10436940536342198186108357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6957960357561465457405571 10436940536342198186108357)
              ·
                refine ⟨1956926350564162159895317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10436940536342198186108357 1956926350564162159895317)
                ·
                  refine ⟨91730922682695101245093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1956926350564162159895317 91730922682695101245093)
                  ·
                    rfl

theorem cell22_803904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 4, 6].length) (baseStart_803904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_803904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_803904 prefixEnd_803904 := by exact prefixLift 803904
  have htrace : WordTrace (prefixWord ++ tailWord_803904) baseStart_803904 baseEnd_803904 := by
    simpa [prefixWord, tailWord_803904, baseEnd_803904] using wordTrace_append hprefix tailTrace_803904
  have hstable : (prefixWord ++ tailWord_803904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803904).length < 2 ^ (prefixWord ++ tailWord_803904).sum := by decide
  have hdescent : baseEnd_803904 < baseStart_803904 := by decide
  rcases family_descends (prefixWord ++ tailWord_803904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803936 : List Nat := [2, 1, 1, 3, 2, 2, 1, 3, 4, 3]
def baseStart_803936 : Nat := 118140960795 + 803936 * 2 ^ 59
def prefixEnd_803936 : Nat := 4983230072969 + 3 ^ 40 * 803936 * 2
def baseEnd_803936 : Nat := 275203722302047886935181

theorem tailTrace_803936 : CollatzResearch.WordTrace tailWord_803936 prefixEnd_803936 275203722302047886935181 := by
  unfold tailWord_803936
  simp only [CollatzResearch.WordTrace]
  refine ⟨14660977407742324091395831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19547969876989765455194441 14660977407742324091395831)
  ·
    refine ⟨21991466111613486137093747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14660977407742324091395831 21991466111613486137093747)
    ·
      refine ⟨32987199167420229205640621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21991466111613486137093747 32987199167420229205640621)
      ·
        refine ⟨12370199687782585952115233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32987199167420229205640621 12370199687782585952115233)
        ·
          refine ⟨9277649765836939464086425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12370199687782585952115233 9277649765836939464086425)
          ·
            refine ⟨6958237324377704598064819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9277649765836939464086425 6958237324377704598064819)
            ·
              refine ⟨10437355986566556897097229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6958237324377704598064819 10437355986566556897097229)
              ·
                refine ⟨3914008494962458836411461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10437355986566556897097229 3914008494962458836411461)
                ·
                  refine ⟨733876592805461031827149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3914008494962458836411461 733876592805461031827149)
                  ·
                    refine ⟨275203722302047886935181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 733876592805461031827149 275203722302047886935181)
                    ·
                      rfl

theorem cell22_803936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3, 4, 3].length) (baseStart_803936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_803936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_803936 prefixEnd_803936 := by exact prefixLift 803936
  have htrace : WordTrace (prefixWord ++ tailWord_803936) baseStart_803936 baseEnd_803936 := by
    simpa [prefixWord, tailWord_803936, baseEnd_803936] using wordTrace_append hprefix tailTrace_803936
  have hstable : (prefixWord ++ tailWord_803936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803936).length < 2 ^ (prefixWord ++ tailWord_803936).sum := by decide
  have hdescent : baseEnd_803936 < baseStart_803936 := by decide
  rcases family_descends (prefixWord ++ tailWord_803936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803938 : List Nat := [3, 3, 2, 2, 1, 1, 3, 1, 6]
def baseStart_803938 : Nat := 118140960795 + 803938 * 2 ^ 59
def prefixEnd_803938 : Nat := 4983230072969 + 3 ^ 40 * 803938 * 2
def baseEnd_803938 : Nat := 91734802314306849461725

theorem tailTrace_803938 : CollatzResearch.WordTrace tailWord_803938 prefixEnd_803938 91734802314306849461725 := by
  unfold tailWord_803938
  simp only [CollatzResearch.WordTrace]
  refine ⟨7330506940369350631091117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19548018507651601682909645 7330506940369350631091117)
  ·
    refine ⟨2748940102638506486659169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7330506940369350631091117 2748940102638506486659169)
    ·
      refine ⟨2061705076978879864994377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2748940102638506486659169 2061705076978879864994377)
      ·
        refine ⟨1546278807734159898745783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2061705076978879864994377 1546278807734159898745783)
        ·
          refine ⟨2319418211601239848118675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1546278807734159898745783 2319418211601239848118675)
          ·
            refine ⟨3479127317401859772178013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2319418211601239848118675 3479127317401859772178013)
            ·
              refine ⟨1304672744025697414566755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3479127317401859772178013 1304672744025697414566755)
              ·
                refine ⟨1957009116038546121850133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1304672744025697414566755 1957009116038546121850133)
                ·
                  refine ⟨91734802314306849461725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1957009116038546121850133 91734802314306849461725)
                  ·
                    rfl

theorem cell22_803938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 1, 6].length) (baseStart_803938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_803938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_803938 prefixEnd_803938 := by exact prefixLift 803938
  have htrace : WordTrace (prefixWord ++ tailWord_803938) baseStart_803938 baseEnd_803938 := by
    simpa [prefixWord, tailWord_803938, baseEnd_803938] using wordTrace_append hprefix tailTrace_803938
  have hstable : (prefixWord ++ tailWord_803938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803938).length < 2 ^ (prefixWord ++ tailWord_803938).sum := by decide
  have hdescent : baseEnd_803938 < baseStart_803938 := by decide
  rcases family_descends (prefixWord ++ tailWord_803938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803957 : List Nat := [1, 3, 4, 3, 1, 2, 1, 2, 1, 4]
def baseStart_803957 : Nat := 118140960795 + 803957 * 2 ^ 59
def prefixEnd_803957 : Nat := 4983230072969 + 3 ^ 40 * 803957 * 2
def baseEnd_803957 : Nat := 275210911031210832160117

theorem tailTrace_803957 : CollatzResearch.WordTrace tailWord_803957 prefixEnd_803957 275210911031210832160117 := by
  unfold tailWord_803957
  simp only [CollatzResearch.WordTrace]
  refine ⟨29322720748408568769306125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19548480498939045846204083 29322720748408568769306125)
  ·
    refine ⟨10996020280653213288489797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29322720748408568769306125 10996020280653213288489797)
    ·
      refine ⟨2061753802622477491591837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10996020280653213288489797 2061753802622477491591837)
      ·
        refine ⟨773157675983429059346939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2061753802622477491591837 773157675983429059346939)
        ·
          refine ⟨1159736513975143589020409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 773157675983429059346939 1159736513975143589020409)
          ·
            refine ⟨869802385481357691765307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1159736513975143589020409 869802385481357691765307)
            ·
              refine ⟨1304703578222036537647961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 869802385481357691765307 1304703578222036537647961)
              ·
                refine ⟨978527683666527403235971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1304703578222036537647961 978527683666527403235971)
                ·
                  refine ⟨1467791525499791104853957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 978527683666527403235971 1467791525499791104853957)
                  ·
                    refine ⟨275210911031210832160117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1467791525499791104853957 275210911031210832160117)
                    ·
                      rfl

theorem cell22_803957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_803957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_803957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_803957 prefixEnd_803957 := by exact prefixLift 803957
  have htrace : WordTrace (prefixWord ++ tailWord_803957) baseStart_803957 baseEnd_803957 := by
    simpa [prefixWord, tailWord_803957, baseEnd_803957] using wordTrace_append hprefix tailTrace_803957
  have hstable : (prefixWord ++ tailWord_803957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803957).length < 2 ^ (prefixWord ++ tailWord_803957).sum := by decide
  have hdescent : baseEnd_803957 < baseStart_803957 := by decide
  rcases family_descends (prefixWord ++ tailWord_803957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803979 : List Nat := [1, 1, 1, 1, 4, 1, 1, 2, 4, 6]
def baseStart_803979 : Nat := 118140960795 + 803979 * 2 ^ 59
def prefixEnd_803979 : Nat := 4983230072969 + 3 ^ 40 * 803979 * 2
def baseEnd_803979 : Nat := 275218442080810108110049

theorem tailTrace_803979 : CollatzResearch.WordTrace tailWord_803979 prefixEnd_803979 275218442080810108110049 := by
  unfold tailWord_803979
  simp only [CollatzResearch.WordTrace]
  refine ⟨29323523154328866526606991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19549015436219244351071327 29323523154328866526606991)
  ·
    refine ⟨43985284731493299789910487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29323523154328866526606991 43985284731493299789910487)
    ·
      refine ⟨65977927097239949684865731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43985284731493299789910487 65977927097239949684865731)
      ·
        refine ⟨98966890645859924527298597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65977927097239949684865731 98966890645859924527298597)
        ·
          refine ⟨18556291996098735848868487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98966890645859924527298597 18556291996098735848868487)
          ·
            refine ⟨27834437994148103773302731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18556291996098735848868487 27834437994148103773302731)
            ·
              refine ⟨41751656991222155659954097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27834437994148103773302731 41751656991222155659954097)
              ·
                refine ⟨31313742743416616744965573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41751656991222155659954097 31313742743416616744965573)
                ·
                  refine ⟨5871326764390615639681045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31313742743416616744965573 5871326764390615639681045)
                  ·
                    refine ⟨275218442080810108110049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5871326764390615639681045 275218442080810108110049)
                    ·
                      rfl

theorem cell22_803979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4, 6].length) (baseStart_803979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_803979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_803979 prefixEnd_803979 := by exact prefixLift 803979
  have htrace : WordTrace (prefixWord ++ tailWord_803979) baseStart_803979 baseEnd_803979 := by
    simpa [prefixWord, tailWord_803979, baseEnd_803979] using wordTrace_append hprefix tailTrace_803979
  have hstable : (prefixWord ++ tailWord_803979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803979).length < 2 ^ (prefixWord ++ tailWord_803979).sum := by decide
  have hdescent : baseEnd_803979 < baseStart_803979 := by decide
  rcases family_descends (prefixWord ++ tailWord_803979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803996 : List Nat := [2, 2, 3, 2, 1, 2, 1, 1, 2, 6]
def baseStart_803996 : Nat := 118140960795 + 803996 * 2 ^ 59
def prefixEnd_803996 : Nat := 4983230072969 + 3 ^ 40 * 803996 * 2
def baseEnd_803996 : Nat := 275224261528227730434997

theorem tailTrace_803996 : CollatzResearch.WordTrace tailWord_803996 prefixEnd_803996 275224261528227730434997 := by
  unfold tailWord_803996
  simp only [CollatzResearch.WordTrace]
  refine ⟨14662071597633639214987921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19549428796844852286650561 14662071597633639214987921)
  ·
    refine ⟨10996553698225229411240941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14662071597633639214987921 10996553698225229411240941)
    ·
      refine ⟨4123707636834461029215353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10996553698225229411240941 4123707636834461029215353)
      ·
        refine ⟨3092780727625845771911515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4123707636834461029215353 3092780727625845771911515)
        ·
          refine ⟨4639171091438768657867273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3092780727625845771911515 4639171091438768657867273)
          ·
            refine ⟨3479378318579076493400455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4639171091438768657867273 3479378318579076493400455)
            ·
              refine ⟨5219067477868614740100683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3479378318579076493400455 5219067477868614740100683)
              ·
                refine ⟨7828601216802922110151025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5219067477868614740100683 7828601216802922110151025)
                ·
                  refine ⟨5871450912602191582613269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7828601216802922110151025 5871450912602191582613269)
                  ·
                    refine ⟨275224261528227730434997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5871450912602191582613269 275224261528227730434997)
                    ·
                      rfl

theorem cell22_803996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_803996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_803996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_803996 prefixEnd_803996 := by exact prefixLift 803996
  have htrace : WordTrace (prefixWord ++ tailWord_803996) baseStart_803996 baseEnd_803996 := by
    simpa [prefixWord, tailWord_803996, baseEnd_803996] using wordTrace_append hprefix tailTrace_803996
  have hstable : (prefixWord ++ tailWord_803996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803996).length < 2 ^ (prefixWord ++ tailWord_803996).sum := by decide
  have hdescent : baseEnd_803996 < baseStart_803996 := by decide
  rcases family_descends (prefixWord ++ tailWord_803996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804032 : List Nat := [2, 1, 1, 2, 6, 1, 2, 3, 1, 3]
def baseStart_804032 : Nat := 118140960795 + 804032 * 2 ^ 59
def prefixEnd_804032 : Nat := 4983230072969 + 3 ^ 40 * 804032 * 2
def baseEnd_804032 : Nat := 275236585063935636534887

theorem tailTrace_804032 : CollatzResearch.WordTrace tailWord_804032 prefixEnd_804032 275236585063935636534887 := by
  unfold tailWord_804032
  simp only [CollatzResearch.WordTrace]
  refine ⟨14662728111568428289143175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19550304148757904385524233 14662728111568428289143175)
  ·
    refine ⟨21994092167352642433714763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14662728111568428289143175 21994092167352642433714763)
    ·
      refine ⟨32991138251028963650572145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21994092167352642433714763 32991138251028963650572145)
      ·
        refine ⟨24743353688271722737929109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32991138251028963650572145 24743353688271722737929109)
        ·
          refine ⟨1159844704137737003340427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 24743353688271722737929109 1159844704137737003340427)
          ·
            refine ⟨1739767056206605505010641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1159844704137737003340427 1739767056206605505010641)
            ·
              refine ⟨1304825292154954128757981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1739767056206605505010641 1304825292154954128757981)
              ·
                refine ⟨489309484558107798284243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1304825292154954128757981 489309484558107798284243)
                ·
                  refine ⟨733964226837161697426365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 489309484558107798284243 733964226837161697426365)
                  ·
                    refine ⟨275236585063935636534887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 733964226837161697426365 275236585063935636534887)
                    ·
                      rfl

theorem cell22_804032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 3, 1, 3].length) (baseStart_804032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_804032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_804032 prefixEnd_804032 := by exact prefixLift 804032
  have htrace : WordTrace (prefixWord ++ tailWord_804032) baseStart_804032 baseEnd_804032 := by
    simpa [prefixWord, tailWord_804032, baseEnd_804032] using wordTrace_append hprefix tailTrace_804032
  have hstable : (prefixWord ++ tailWord_804032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804032).length < 2 ^ (prefixWord ++ tailWord_804032).sum := by decide
  have hdescent : baseEnd_804032 < baseStart_804032 := by decide
  rcases family_descends (prefixWord ++ tailWord_804032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804038 : List Nat := [6, 1, 2, 2, 2, 1, 1, 2, 2, 3]
def baseStart_804038 : Nat := 118140960795 + 804038 * 2 ^ 59
def prefixEnd_804038 : Nat := 4983230072969 + 3 ^ 40 * 804038 * 2
def baseEnd_804038 : Nat := 275238638986553620884869

theorem tailTrace_804038 : CollatzResearch.WordTrace tailWord_804038 prefixEnd_804038 275238638986553620884869 := by
  unfold tailWord_804038
  simp only [CollatzResearch.WordTrace]
  refine ⟨916427345659847487593899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 19550450040743413068669845 916427345659847487593899)
  ·
    refine ⟨1374641018489771231390849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 916427345659847487593899 1374641018489771231390849)
    ·
      refine ⟨1030980763867328423543137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1374641018489771231390849 1030980763867328423543137)
      ·
        refine ⟨773235572900496317657353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1030980763867328423543137 773235572900496317657353)
        ·
          refine ⟨579926679675372238243015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 773235572900496317657353 579926679675372238243015)
          ·
            refine ⟨869890019513058357364523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 579926679675372238243015 869890019513058357364523)
            ·
              refine ⟨1304835029269587536046785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 869890019513058357364523 1304835029269587536046785)
              ·
                refine ⟨978626271952190652035089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1304835029269587536046785 978626271952190652035089)
                ·
                  refine ⟨733969703964142989026317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 978626271952190652035089 733969703964142989026317)
                  ·
                    refine ⟨275238638986553620884869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 733969703964142989026317 275238638986553620884869)
                    ·
                      rfl

theorem cell22_804038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_804038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_804038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_804038 prefixEnd_804038 := by exact prefixLift 804038
  have htrace : WordTrace (prefixWord ++ tailWord_804038) baseStart_804038 baseEnd_804038 := by
    simpa [prefixWord, tailWord_804038, baseEnd_804038] using wordTrace_append hprefix tailTrace_804038
  have hstable : (prefixWord ++ tailWord_804038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804038).length < 2 ^ (prefixWord ++ tailWord_804038).sum := by decide
  have hdescent : baseEnd_804038 < baseStart_804038 := by decide
  rcases family_descends (prefixWord ++ tailWord_804038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804122 : List Nat := [3, 1, 1, 3, 3, 1, 4, 1, 2, 3]
def baseStart_804122 : Nat := 118140960795 + 804122 * 2 ^ 59
def prefixEnd_804122 : Nat := 4983230072969 + 3 ^ 40 * 804122 * 2
def baseEnd_804122 : Nat := 275267393903205401784611

theorem tailTrace_804122 : CollatzResearch.WordTrace tailWord_804122 prefixEnd_804122 275267393903205401784611 := by
  unfold tailWord_804122
  simp only [CollatzResearch.WordTrace]
  refine ⟨7332184698202700487265655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19552492528540534632708413 7332184698202700487265655)
  ·
    refine ⟨10998277047304050730898483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7332184698202700487265655 10998277047304050730898483)
    ·
      refine ⟨16497415570956076096347725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10998277047304050730898483 16497415570956076096347725)
      ·
        refine ⟨6186530839108528536130397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16497415570956076096347725 6186530839108528536130397)
        ·
          refine ⟨2319949064665698201048899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6186530839108528536130397 2319949064665698201048899)
          ·
            refine ⟨3479923596998547301573349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2319949064665698201048899 3479923596998547301573349)
            ·
              refine ⟨652485674437227619045003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3479923596998547301573349 652485674437227619045003)
              ·
                refine ⟨978728511655841428567505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 652485674437227619045003 978728511655841428567505)
                ·
                  refine ⟨734046383741881071425629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 978728511655841428567505 734046383741881071425629)
                  ·
                    refine ⟨275267393903205401784611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 734046383741881071425629 275267393903205401784611)
                    ·
                      rfl

theorem cell22_804122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 4, 1, 2, 3].length) (baseStart_804122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_804122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_804122 prefixEnd_804122 := by exact prefixLift 804122
  have htrace : WordTrace (prefixWord ++ tailWord_804122) baseStart_804122 baseEnd_804122 := by
    simpa [prefixWord, tailWord_804122, baseEnd_804122] using wordTrace_append hprefix tailTrace_804122
  have hstable : (prefixWord ++ tailWord_804122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804122).length < 2 ^ (prefixWord ++ tailWord_804122).sum := by decide
  have hdescent : baseEnd_804122 < baseStart_804122 := by decide
  rcases family_descends (prefixWord ++ tailWord_804122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804126 : List Nat := [4, 3, 2, 1, 3, 1, 1, 2, 1, 4]
def baseStart_804126 : Nat := 118140960795 + 804126 * 2 ^ 59
def prefixEnd_804126 : Nat := 4983230072969 + 3 ^ 40 * 804126 * 2
def baseEnd_804126 : Nat := 275268763184950724684599

theorem tailTrace_804126 : CollatzResearch.WordTrace tailWord_804126 prefixEnd_804126 275268763184950724684599 := by
  unfold tailWord_804126
  simp only [CollatzResearch.WordTrace]
  refine ⟨3666110585599538829026029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19552589789864207088138821 3666110585599538829026029)
  ·
    refine ⟨1374791469599827060884761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3666110585599538829026029 1374791469599827060884761)
    ·
      refine ⟨1031093602199870295663571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1374791469599827060884761 1031093602199870295663571)
      ·
        refine ⟨1546640403299805443495357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1031093602199870295663571 1546640403299805443495357)
        ·
          refine ⟨579990151237427041310759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1546640403299805443495357 579990151237427041310759)
          ·
            refine ⟨869985226856140561966139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 579990151237427041310759 869985226856140561966139)
            ·
              refine ⟨1304977840284210842949209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 869985226856140561966139 1304977840284210842949209)
              ·
                refine ⟨978733380213158132211907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1304977840284210842949209 978733380213158132211907)
                ·
                  refine ⟨1468100070319737198317861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 978733380213158132211907 1468100070319737198317861)
                  ·
                    refine ⟨275268763184950724684599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1468100070319737198317861 275268763184950724684599)
                    ·
                      rfl

theorem cell22_804126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_804126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_804126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_804126 prefixEnd_804126 := by exact prefixLift 804126
  have htrace : WordTrace (prefixWord ++ tailWord_804126) baseStart_804126 baseEnd_804126 := by
    simpa [prefixWord, tailWord_804126, baseEnd_804126] using wordTrace_append hprefix tailTrace_804126
  have hstable : (prefixWord ++ tailWord_804126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804126).length < 2 ^ (prefixWord ++ tailWord_804126).sum := by decide
  have hdescent : baseEnd_804126 < baseStart_804126 := by decide
  rcases family_descends (prefixWord ++ tailWord_804126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804167 : List Nat := [1, 1, 4, 1, 2, 4, 1, 4, 1, 3]
def baseStart_804167 : Nat := 118140960795 + 804167 * 2 ^ 59
def prefixEnd_804167 : Nat := 4983230072969 + 3 ^ 40 * 804167 * 2
def baseEnd_804167 : Nat := 275282798322840284409473

theorem tailTrace_804167 : CollatzResearch.WordTrace tailWord_804167 prefixEnd_804167 275282798322840284409473 := by
  unfold tailWord_804167
  simp only [CollatzResearch.WordTrace]
  refine ⟨29330380077647774634450755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19553586718431849756300503 29330380077647774634450755)
  ·
    refine ⟨43995570116471661951676133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29330380077647774634450755 43995570116471661951676133)
    ·
      refine ⟨8249169396838436615939275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43995570116471661951676133 8249169396838436615939275)
      ·
        refine ⟨12373754095257654923908913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8249169396838436615939275 12373754095257654923908913)
        ·
          refine ⟨9280315571443241192931685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12373754095257654923908913 9280315571443241192931685)
          ·
            refine ⟨1740059169645607723674691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9280315571443241192931685 1740059169645607723674691)
            ·
              refine ⟨2610088754468411585512037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1740059169645607723674691 2610088754468411585512037)
              ·
                refine ⟨489391641462827172283507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2610088754468411585512037 489391641462827172283507)
                ·
                  refine ⟨734087462194240758425261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 489391641462827172283507 734087462194240758425261)
                  ·
                    refine ⟨275282798322840284409473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 734087462194240758425261 275282798322840284409473)
                    ·
                      rfl

theorem cell22_804167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 4, 1, 3].length) (baseStart_804167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_804167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_804167 prefixEnd_804167 := by exact prefixLift 804167
  have htrace : WordTrace (prefixWord ++ tailWord_804167) baseStart_804167 baseEnd_804167 := by
    simpa [prefixWord, tailWord_804167, baseEnd_804167] using wordTrace_append hprefix tailTrace_804167
  have hstable : (prefixWord ++ tailWord_804167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804167).length < 2 ^ (prefixWord ++ tailWord_804167).sum := by decide
  have hdescent : baseEnd_804167 < baseStart_804167 := by decide
  rcases family_descends (prefixWord ++ tailWord_804167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804210 : List Nat := [3, 2, 1, 2, 1, 2, 3, 3, 1, 4]
def baseStart_804210 : Nat := 118140960795 + 804210 * 2 ^ 59
def prefixEnd_804210 : Nat := 4983230072969 + 3 ^ 40 * 804210 * 2
def baseEnd_804210 : Nat := 275297518101602505584341

theorem tailTrace_804210 : CollatzResearch.WordTrace tailWord_804210 prefixEnd_804210 275297518101602505584341 := by
  unfold tailWord_804210
  simp only [CollatzResearch.WordTrace]
  refine ⟨7332987104122998244566521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19554632277661328652177389 7332987104122998244566521)
  ·
    refine ⟨5499740328092248683424891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7332987104122998244566521 5499740328092248683424891)
    ·
      refine ⟨8249610492138373025137337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5499740328092248683424891 8249610492138373025137337)
      ·
        refine ⟨6187207869103779768853003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8249610492138373025137337 6187207869103779768853003)
        ·
          refine ⟨9280811803655669653279505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6187207869103779768853003 9280811803655669653279505)
          ·
            refine ⟨6960608852741752239959629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9280811803655669653279505 6960608852741752239959629)
            ·
              refine ⟨2610228319778157089984861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6960608852741752239959629 2610228319778157089984861)
              ·
                refine ⟨978835619916808908744323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2610228319778157089984861 978835619916808908744323)
                ·
                  refine ⟨1468253429875213363116485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 978835619916808908744323 1468253429875213363116485)
                  ·
                    refine ⟨275297518101602505584341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1468253429875213363116485 275297518101602505584341)
                    ·
                      rfl

theorem cell22_804210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 3, 1, 4].length) (baseStart_804210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_804210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_804210 prefixEnd_804210 := by exact prefixLift 804210
  have htrace : WordTrace (prefixWord ++ tailWord_804210) baseStart_804210 baseEnd_804210 := by
    simpa [prefixWord, tailWord_804210, baseEnd_804210] using wordTrace_append hprefix tailTrace_804210
  have hstable : (prefixWord ++ tailWord_804210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804210).length < 2 ^ (prefixWord ++ tailWord_804210).sum := by decide
  have hdescent : baseEnd_804210 < baseStart_804210 := by decide
  rcases family_descends (prefixWord ++ tailWord_804210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804336 : List Nat := [2, 1, 1, 1, 3, 6, 2, 2, 1, 3]
def baseStart_804336 : Nat := 118140960795 + 804336 * 2 ^ 59
def prefixEnd_804336 : Nat := 4983230072969 + 3 ^ 40 * 804336 * 2
def baseEnd_804336 : Nat := 275340650476580176933955

theorem tailTrace_804336 : CollatzResearch.WordTrace tailWord_804336 prefixEnd_804336 275340650476580176933955 := by
  unfold tailWord_804336
  simp only [CollatzResearch.WordTrace]
  refine ⟨14668272007017758248676431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19557696009357010998235241 14668272007017758248676431)
  ·
    refine ⟨22002408010526637373014647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14668272007017758248676431 22002408010526637373014647)
    ·
      refine ⟨33003612015789956059521971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22002408010526637373014647 33003612015789956059521971)
      ·
        refine ⟨49505418023684934089282957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33003612015789956059521971 49505418023684934089282957)
        ·
          refine ⟨18564531758881850283481109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49505418023684934089282957 18564531758881850283481109)
          ·
            refine ⟨870212426197586732038177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 18564531758881850283481109 870212426197586732038177)
            ·
              refine ⟨652659319648190049028633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 870212426197586732038177 652659319648190049028633)
              ·
                refine ⟨489494489736142536771475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 652659319648190049028633 489494489736142536771475)
                ·
                  refine ⟨734241734604213805157213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 489494489736142536771475 734241734604213805157213)
                  ·
                    refine ⟨275340650476580176933955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 734241734604213805157213 275340650476580176933955)
                    ·
                      rfl

theorem cell22_804336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 2, 2, 1, 3].length) (baseStart_804336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_804336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_804336 prefixEnd_804336 := by exact prefixLift 804336
  have htrace : WordTrace (prefixWord ++ tailWord_804336) baseStart_804336 baseEnd_804336 := by
    simpa [prefixWord, tailWord_804336, baseEnd_804336] using wordTrace_append hprefix tailTrace_804336
  have hstable : (prefixWord ++ tailWord_804336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804336).length < 2 ^ (prefixWord ++ tailWord_804336).sum := by decide
  have hdescent : baseEnd_804336 < baseStart_804336 := by decide
  rcases family_descends (prefixWord ++ tailWord_804336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804465 : List Nat := [1, 2, 2, 2, 1, 1, 1, 5, 2, 5]
def baseStart_804465 : Nat := 118140960795 + 804465 * 2 ^ 59
def prefixEnd_804465 : Nat := 4983230072969 + 3 ^ 40 * 804465 * 2
def baseEnd_804465 : Nat := 275384809812866840458559

theorem tailTrace_804465 : CollatzResearch.WordTrace tailWord_804465 prefixEnd_804465 275384809812866840458559 := by
  unfold tailWord_804465
  simp only [CollatzResearch.WordTrace]
  refine ⟨29341249030568171528798849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19560832687045447685865899 29341249030568171528798849)
  ·
    refine ⟨22005936772926128646599137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29341249030568171528798849 22005936772926128646599137)
    ·
      refine ⟨16504452579694596484949353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22005936772926128646599137 16504452579694596484949353)
      ·
        refine ⟨12378339434770947363712015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16504452579694596484949353 12378339434770947363712015)
        ·
          refine ⟨18567509152156421045568023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12378339434770947363712015 18567509152156421045568023)
          ·
            refine ⟨27851263728234631568352035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18567509152156421045568023 27851263728234631568352035)
            ·
              refine ⟨41776895592351947352528053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27851263728234631568352035 41776895592351947352528053)
              ·
                refine ⟨3916583961782995064299505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41776895592351947352528053 3916583961782995064299505)
                ·
                  refine ⟨2937437971337246298224629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3916583961782995064299505 2937437971337246298224629)
                  ·
                    refine ⟨275384809812866840458559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2937437971337246298224629 275384809812866840458559)
                    ·
                      rfl

theorem cell22_804465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5, 2, 5].length) (baseStart_804465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_804465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_804465 prefixEnd_804465 := by exact prefixLift 804465
  have htrace : WordTrace (prefixWord ++ tailWord_804465) baseStart_804465 baseEnd_804465 := by
    simpa [prefixWord, tailWord_804465, baseEnd_804465] using wordTrace_append hprefix tailTrace_804465
  have hstable : (prefixWord ++ tailWord_804465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804465).length < 2 ^ (prefixWord ++ tailWord_804465).sum := by decide
  have hdescent : baseEnd_804465 < baseStart_804465 := by decide
  rcases family_descends (prefixWord ++ tailWord_804465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804527 : List Nat := [1, 1, 2, 1, 2, 4, 4, 1, 1, 5]
def baseStart_804527 : Nat := 118140960795 + 804527 * 2 ^ 59
def prefixEnd_804527 : Nat := 4983230072969 + 3 ^ 40 * 804527 * 2
def baseEnd_804527 : Nat := 275406033679919345408369

theorem tailTrace_804527 : CollatzResearch.WordTrace tailWord_804527 prefixEnd_804527 275406033679919345408369 := by
  unfold tailWord_804527
  simp only [CollatzResearch.WordTrace]
  refine ⟨29343510356343556117555835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19562340237562370745037223 29343510356343556117555835)
  ·
    refine ⟨44015265534515334176333753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29343510356343556117555835 44015265534515334176333753)
    ·
      refine ⟨33011449150886500632250315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44015265534515334176333753 33011449150886500632250315)
      ·
        refine ⟨49517173726329750948375473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33011449150886500632250315 49517173726329750948375473)
        ·
          refine ⟨37137880294747313211281605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49517173726329750948375473 37137880294747313211281605)
          ·
            refine ⟨6963352555265121227115301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37137880294747313211281605 6963352555265121227115301)
            ·
              refine ⟨1305628604112210230084119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6963352555265121227115301 1305628604112210230084119)
              ·
                refine ⟨1958442906168315345126179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1305628604112210230084119 1958442906168315345126179)
                ·
                  refine ⟨2937664359252473017689269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1958442906168315345126179 2937664359252473017689269)
                  ·
                    refine ⟨275406033679919345408369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2937664359252473017689269 275406033679919345408369)
                    ·
                      rfl

theorem cell22_804527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 1, 1, 5].length) (baseStart_804527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_804527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_804527 prefixEnd_804527 := by exact prefixLift 804527
  have htrace : WordTrace (prefixWord ++ tailWord_804527) baseStart_804527 baseEnd_804527 := by
    simpa [prefixWord, tailWord_804527, baseEnd_804527] using wordTrace_append hprefix tailTrace_804527
  have hstable : (prefixWord ++ tailWord_804527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804527).length < 2 ^ (prefixWord ++ tailWord_804527).sum := by decide
  have hdescent : baseEnd_804527 < baseStart_804527 := by decide
  rcases family_descends (prefixWord ++ tailWord_804527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804555 : List Nat := [1, 1, 1, 1, 3, 2, 1, 2, 1, 9]
def baseStart_804555 : Nat := 118140960795 + 804555 * 2 ^ 59
def prefixEnd_804555 : Nat := 4983230072969 + 3 ^ 40 * 804555 * 2
def baseEnd_804555 : Nat := 275415618652136605708283

theorem tailTrace_804555 : CollatzResearch.WordTrace tailWord_804555 prefixEnd_804555 275415618652136605708283 := by
  unfold tailWord_804555
  simp only [CollatzResearch.WordTrace]
  refine ⟨29344531600242116899575119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19563021066828077933050079 29344531600242116899575119)
  ·
    refine ⟨44016797400363175349362679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29344531600242116899575119 44016797400363175349362679)
    ·
      refine ⟨66025196100544763024044019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44016797400363175349362679 66025196100544763024044019)
      ·
        refine ⟨99037794150817144536066029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66025196100544763024044019 99037794150817144536066029)
        ·
          refine ⟨37139172806556429201024761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99037794150817144536066029 37139172806556429201024761)
          ·
            refine ⟨27854379604917321900768571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37139172806556429201024761 27854379604917321900768571)
            ·
              refine ⟨41781569407375982851152857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27854379604917321900768571 41781569407375982851152857)
              ·
                refine ⟨31336177055531987138364643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41781569407375982851152857 31336177055531987138364643)
                ·
                  refine ⟨47004265583297980707546965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31336177055531987138364643 47004265583297980707546965)
                  ·
                    refine ⟨275415618652136605708283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 47004265583297980707546965 275415618652136605708283)
                    ·
                      rfl

theorem cell22_804555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 9].length) (baseStart_804555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_804555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_804555 prefixEnd_804555 := by exact prefixLift 804555
  have htrace : WordTrace (prefixWord ++ tailWord_804555) baseStart_804555 baseEnd_804555 := by
    simpa [prefixWord, tailWord_804555, baseEnd_804555] using wordTrace_append hprefix tailTrace_804555
  have hstable : (prefixWord ++ tailWord_804555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804555).length < 2 ^ (prefixWord ++ tailWord_804555).sum := by decide
  have hdescent : baseEnd_804555 < baseStart_804555 := by decide
  rcases family_descends (prefixWord ++ tailWord_804555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804561 : List Nat := [1, 2, 2, 1, 2, 6, 1, 2, 2, 3]
def baseStart_804561 : Nat := 118140960795 + 804561 * 2 ^ 59
def prefixEnd_804561 : Nat := 4983230072969 + 3 ^ 40 * 804561 * 2
def baseEnd_804561 : Nat := 275417672574754590058265

theorem tailTrace_804561 : CollatzResearch.WordTrace tailWord_804561 prefixEnd_804561 275417672574754590058265 := by
  unfold tailWord_804561
  simp only [CollatzResearch.WordTrace]
  refine ⟨29344750438220379924293537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19563166958813586616195691 29344750438220379924293537)
  ·
    refine ⟨22008562828665284943220153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29344750438220379924293537 22008562828665284943220153)
    ·
      refine ⟨16506422121498963707415115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22008562828665284943220153 16506422121498963707415115)
      ·
        refine ⟨24759633182248445561122673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16506422121498963707415115 24759633182248445561122673)
        ·
          refine ⟨18569724886686334170842005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24759633182248445561122673 18569724886686334170842005)
          ·
            refine ⟨870455854063421914258219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 18569724886686334170842005 870455854063421914258219)
            ·
              refine ⟨1305683781095132871387329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 870455854063421914258219 1305683781095132871387329)
              ·
                refine ⟨979262835821349653540497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1305683781095132871387329 979262835821349653540497)
                ·
                  refine ⟨734447126866012240155373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 979262835821349653540497 734447126866012240155373)
                  ·
                    refine ⟨275417672574754590058265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 734447126866012240155373 275417672574754590058265)
                    ·
                      rfl

theorem cell22_804561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 2, 2, 3].length) (baseStart_804561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_804561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_804561 prefixEnd_804561 := by exact prefixLift 804561
  have htrace : WordTrace (prefixWord ++ tailWord_804561) baseStart_804561 baseEnd_804561 := by
    simpa [prefixWord, tailWord_804561, baseEnd_804561] using wordTrace_append hprefix tailTrace_804561
  have hstable : (prefixWord ++ tailWord_804561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804561).length < 2 ^ (prefixWord ++ tailWord_804561).sum := by decide
  have hdescent : baseEnd_804561 < baseStart_804561 := by decide
  rcases family_descends (prefixWord ++ tailWord_804561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804614 : List Nat := [6, 2, 2, 1, 2, 1, 1, 1, 6]
def baseStart_804614 : Nat := 118140960795 + 804614 * 2 ^ 59
def prefixEnd_804614 : Nat := 4983230072969 + 3 ^ 40 * 804614 * 2
def baseEnd_804614 : Nat := 91811938519293372827701

theorem tailTrace_804614 : CollatzResearch.WordTrace tailWord_804614 prefixEnd_804614 91811938519293372827701 := by
  unfold tailWord_804614
  simp only [CollatzResearch.WordTrace]
  refine ⟨917083859594636561749153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 19564455671352246650648597 917083859594636561749153)
  ·
    refine ⟨687812894695977421311865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 917083859594636561749153 687812894695977421311865)
    ·
      refine ⟨515859671021983065983899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 687812894695977421311865 515859671021983065983899)
      ·
        refine ⟨773789506532974598975849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 515859671021983065983899 773789506532974598975849)
        ·
          refine ⟨580342129899730949231887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 773789506532974598975849 580342129899730949231887)
          ·
            refine ⟨870513194849596423847831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 580342129899730949231887 870513194849596423847831)
            ·
              refine ⟨1305769792274394635771747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 870513194849596423847831 1305769792274394635771747)
              ·
                refine ⟨1958654688411591953657621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1305769792274394635771747 1958654688411591953657621)
                ·
                  refine ⟨91811938519293372827701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1958654688411591953657621 91811938519293372827701)
                  ·
                    rfl

theorem cell22_804614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_804614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_804614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_804614 prefixEnd_804614 := by exact prefixLift 804614
  have htrace : WordTrace (prefixWord ++ tailWord_804614) baseStart_804614 baseEnd_804614 := by
    simpa [prefixWord, tailWord_804614, baseEnd_804614] using wordTrace_append hprefix tailTrace_804614
  have hstable : (prefixWord ++ tailWord_804614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804614).length < 2 ^ (prefixWord ++ tailWord_804614).sum := by decide
  have hdescent : baseEnd_804614 < baseStart_804614 := by decide
  rcases family_descends (prefixWord ++ tailWord_804614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804679 : List Nat := [1, 1, 4, 1, 2, 1, 2, 3, 4, 3]
def baseStart_804679 : Nat := 118140960795 + 804679 * 2 ^ 59
def prefixEnd_804679 : Nat := 4983230072969 + 3 ^ 40 * 804679 * 2
def baseEnd_804679 : Nat := 275458066386241615607903

theorem tailTrace_804679 : CollatzResearch.WordTrace tailWord_804679 prefixEnd_804679 275458066386241615607903 := by
  unfold tailWord_804679
  simp only [CollatzResearch.WordTrace]
  refine ⟨29349054251792886077089091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19566036167861924051392727 29349054251792886077089091)
  ·
    refine ⟨44023581377689329115633637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29349054251792886077089091 44023581377689329115633637)
    ·
      refine ⟨8254421508316749209181307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44023581377689329115633637 8254421508316749209181307)
      ·
        refine ⟨12381632262475123813771961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8254421508316749209181307 12381632262475123813771961)
        ·
          refine ⟨9286224196856342860328971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12381632262475123813771961 9286224196856342860328971)
          ·
            refine ⟨13929336295284514290493457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9286224196856342860328971 13929336295284514290493457)
            ·
              refine ⟨10447002221463385717870093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13929336295284514290493457 10447002221463385717870093)
              ·
                refine ⟨3917625833048769644201285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10447002221463385717870093 3917625833048769644201285)
                ·
                  refine ⟨734554843696644308287741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3917625833048769644201285 734554843696644308287741)
                  ·
                    refine ⟨275458066386241615607903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 734554843696644308287741 275458066386241615607903)
                    ·
                      rfl

theorem cell22_804679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3, 4, 3].length) (baseStart_804679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_804679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_804679 prefixEnd_804679 := by exact prefixLift 804679
  have htrace : WordTrace (prefixWord ++ tailWord_804679) baseStart_804679 baseEnd_804679 := by
    simpa [prefixWord, tailWord_804679, baseEnd_804679] using wordTrace_append hprefix tailTrace_804679
  have hstable : (prefixWord ++ tailWord_804679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804679).length < 2 ^ (prefixWord ++ tailWord_804679).sum := by decide
  have hdescent : baseEnd_804679 < baseStart_804679 := by decide
  rcases family_descends (prefixWord ++ tailWord_804679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804726 : List Nat := [5, 1, 1, 3, 2, 1, 9]
def baseStart_804726 : Nat := 118140960795 + 804726 * 2 ^ 59
def prefixEnd_804726 : Nat := 4983230072969 + 3 ^ 40 * 804726 * 2
def baseEnd_804726 : Nat := 10202746498027746654917

theorem tailTrace_804726 : CollatzResearch.WordTrace tailWord_804726 prefixEnd_804726 10202746498027746654917 := by
  unfold tailWord_804726
  simp only [CollatzResearch.WordTrace]
  refine ⟨1834423030163913319003127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19567178988415075402700021 1834423030163913319003127)
  ·
    refine ⟨2751634545245869978504691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1834423030163913319003127 2751634545245869978504691)
    ·
      refine ⟨4127451817868804967757037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2751634545245869978504691 4127451817868804967757037)
      ·
        refine ⟨1547794431700801862908889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4127451817868804967757037 1547794431700801862908889)
        ·
          refine ⟨1160845823775601397181667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1547794431700801862908889 1160845823775601397181667)
          ·
            refine ⟨1741268735663402095772501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1160845823775601397181667 1741268735663402095772501)
            ·
              refine ⟨10202746498027746654917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1741268735663402095772501 10202746498027746654917)
              ·
                rfl

theorem cell22_804726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 9].length) (baseStart_804726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_804726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_804726 prefixEnd_804726 := by exact prefixLift 804726
  have htrace : WordTrace (prefixWord ++ tailWord_804726) baseStart_804726 baseEnd_804726 := by
    simpa [prefixWord, tailWord_804726, baseEnd_804726] using wordTrace_append hprefix tailTrace_804726
  have hstable : (prefixWord ++ tailWord_804726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804726).length < 2 ^ (prefixWord ++ tailWord_804726).sum := by decide
  have hdescent : baseEnd_804726 < baseStart_804726 := by decide
  rcases family_descends (prefixWord ++ tailWord_804726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804741 : List Nat := [1, 3, 1, 1, 3, 2, 4, 1, 3, 3]
def baseStart_804741 : Nat := 118140960795 + 804741 * 2 ^ 59
def prefixEnd_804741 : Nat := 4983230072969 + 3 ^ 40 * 804741 * 2
def baseEnd_804741 : Nat := 275479290253294120557713

theorem tailTrace_804741 : CollatzResearch.WordTrace tailWord_804741 prefixEnd_804741 275479290253294120557713 := by
  unfold tailWord_804741
  simp only [CollatzResearch.WordTrace]
  refine ⟨29351315577568270665846077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19567543718378847110564051 29351315577568270665846077)
  ·
    refine ⟨11006743341588101499692279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29351315577568270665846077 11006743341588101499692279)
    ·
      refine ⟨16510115012382152249538419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11006743341588101499692279 16510115012382152249538419)
      ·
        refine ⟨24765172518573228374307629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16510115012382152249538419 24765172518573228374307629)
        ·
          refine ⟨9286939694464960640365361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24765172518573228374307629 9286939694464960640365361)
          ·
            refine ⟨6965204770848720480274021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9286939694464960640365361 6965204770848720480274021)
            ·
              refine ⟨1305975894534135090051379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6965204770848720480274021 1305975894534135090051379)
              ·
                refine ⟨1958963841801202635077069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1305975894534135090051379 1958963841801202635077069)
                ·
                  refine ⟨734611440675450988153901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1958963841801202635077069 734611440675450988153901)
                  ·
                    refine ⟨275479290253294120557713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 734611440675450988153901 275479290253294120557713)
                    ·
                      rfl

theorem cell22_804741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 1, 3, 3].length) (baseStart_804741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_804741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_804741 prefixEnd_804741 := by exact prefixLift 804741
  have htrace : WordTrace (prefixWord ++ tailWord_804741) baseStart_804741 baseEnd_804741 := by
    simpa [prefixWord, tailWord_804741, baseEnd_804741] using wordTrace_append hprefix tailTrace_804741
  have hstable : (prefixWord ++ tailWord_804741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804741).length < 2 ^ (prefixWord ++ tailWord_804741).sum := by decide
  have hdescent : baseEnd_804741 < baseStart_804741 := by decide
  rcases family_descends (prefixWord ++ tailWord_804741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804760 : List Nat := [2, 1, 2, 6, 2, 1, 2, 6]
def baseStart_804760 : Nat := 118140960795 + 804760 * 2 ^ 59
def prefixEnd_804760 : Nat := 4983230072969 + 3 ^ 40 * 804760 * 2
def baseEnd_804760 : Nat := 30609532704620489370295

theorem tailTrace_804760 : CollatzResearch.WordTrace tailWord_804760 prefixEnd_804760 30609532704620489370295 := by
  unfold tailWord_804760
  simp only [CollatzResearch.WordTrace]
  refine ⟨14676004282249718455393867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19568005709666291273858489 14676004282249718455393867)
  ·
    refine ⟨22014006423374577683090801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14676004282249718455393867 22014006423374577683090801)
    ·
      refine ⟨16510504817530933262318101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22014006423374577683090801 16510504817530933262318101)
      ·
        refine ⟨773929913321762496671161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 16510504817530933262318101 773929913321762496671161)
        ·
          refine ⟨580447434991321872503371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 773929913321762496671161 580447434991321872503371)
          ·
            refine ⟨870671152486982808755057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 580447434991321872503371 870671152486982808755057)
            ·
              refine ⟨653003364365237106566293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 870671152486982808755057 653003364365237106566293)
              ·
                refine ⟨30609532704620489370295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 653003364365237106566293 30609532704620489370295)
                ·
                  rfl

theorem cell22_804760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 2, 6].length) (baseStart_804760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_804760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_804760 prefixEnd_804760 := by exact prefixLift 804760
  have htrace : WordTrace (prefixWord ++ tailWord_804760) baseStart_804760 baseEnd_804760 := by
    simpa [prefixWord, tailWord_804760, baseEnd_804760] using wordTrace_append hprefix tailTrace_804760
  have hstable : (prefixWord ++ tailWord_804760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804760).length < 2 ^ (prefixWord ++ tailWord_804760).sum := by decide
  have hdescent : baseEnd_804760 < baseStart_804760 := by decide
  rcases family_descends (prefixWord ++ tailWord_804760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804775 : List Nat := [1, 1, 6, 1, 2, 1, 3, 3, 1, 3]
def baseStart_804775 : Nat := 118140960795 + 804775 * 2 ^ 59
def prefixEnd_804775 : Nat := 4983230072969 + 3 ^ 40 * 804775 * 2
def baseEnd_804775 : Nat := 275490929148129365207609

theorem tailTrace_804775 : CollatzResearch.WordTrace tailWord_804775 prefixEnd_804775 275490929148129365207609 := by
  unfold tailWord_804775
  simp only [CollatzResearch.WordTrace]
  refine ⟨29352555659445094472583779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19568370439630062981722519 29352555659445094472583779)
  ·
    refine ⟨44028833489167641708875669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29352555659445094472583779 44028833489167641708875669)
    ·
      refine ⟨2063851569804733205103547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 44028833489167641708875669 2063851569804733205103547)
      ·
        refine ⟨3095777354707099807655321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2063851569804733205103547 3095777354707099807655321)
        ·
          refine ⟨2321833016030324855741491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3095777354707099807655321 2321833016030324855741491)
          ·
            refine ⟨3482749524045487283612237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2321833016030324855741491 3482749524045487283612237)
            ·
              refine ⟨1306031071517057731354589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3482749524045487283612237 1306031071517057731354589)
              ·
                refine ⟨489761651818896649257971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1306031071517057731354589 489761651818896649257971)
                ·
                  refine ⟨734642477728344973886957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 489761651818896649257971 734642477728344973886957)
                  ·
                    refine ⟨275490929148129365207609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 734642477728344973886957 275490929148129365207609)
                    ·
                      rfl

theorem cell22_804775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_804775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_804775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_804775 prefixEnd_804775 := by exact prefixLift 804775
  have htrace : WordTrace (prefixWord ++ tailWord_804775) baseStart_804775 baseEnd_804775 := by
    simpa [prefixWord, tailWord_804775, baseEnd_804775] using wordTrace_append hprefix tailTrace_804775
  have hstable : (prefixWord ++ tailWord_804775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804775).length < 2 ^ (prefixWord ++ tailWord_804775).sum := by decide
  have hdescent : baseEnd_804775 < baseStart_804775 := by decide
  rcases family_descends (prefixWord ++ tailWord_804775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804818 : List Nat := [3, 2, 2, 3, 2, 1, 1, 1, 3, 4]
def baseStart_804818 : Nat := 118140960795 + 804818 * 2 ^ 59
def prefixEnd_804818 : Nat := 4983230072969 + 3 ^ 40 * 804818 * 2
def baseEnd_804818 : Nat := 275505648926891586382477

theorem tailTrace_804818 : CollatzResearch.WordTrace tailWord_804818 prefixEnd_804818 275505648926891586382477 := by
  unfold tailWord_804818
  simp only [CollatzResearch.WordTrace]
  refine ⟨7338530999572328204099777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19569415998859541877599405 7338530999572328204099777)
  ·
    refine ⟨5503898249679246153074833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7338530999572328204099777 5503898249679246153074833)
    ·
      refine ⟨4127923687259434614806125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5503898249679246153074833 4127923687259434614806125)
      ·
        refine ⟨1547971382722287980552297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4127923687259434614806125 1547971382722287980552297)
        ·
          refine ⟨1160978537041715985414223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1547971382722287980552297 1160978537041715985414223)
          ·
            refine ⟨1741467805562573978121335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1160978537041715985414223 1741467805562573978121335)
            ·
              refine ⟨2612201708343860967182003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1741467805562573978121335 2612201708343860967182003)
              ·
                refine ⟨3918302562515791450773005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2612201708343860967182003 3918302562515791450773005)
                ·
                  refine ⟨1469363460943421794039877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3918302562515791450773005 1469363460943421794039877)
                  ·
                    refine ⟨275505648926891586382477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1469363460943421794039877 275505648926891586382477)
                    ·
                      rfl

theorem cell22_804818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_804818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_804818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_804818 prefixEnd_804818 := by exact prefixLift 804818
  have htrace : WordTrace (prefixWord ++ tailWord_804818) baseStart_804818 baseEnd_804818 := by
    simpa [prefixWord, tailWord_804818, baseEnd_804818] using wordTrace_append hprefix tailTrace_804818
  have hstable : (prefixWord ++ tailWord_804818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804818).length < 2 ^ (prefixWord ++ tailWord_804818).sum := by decide
  have hdescent : baseEnd_804818 < baseStart_804818 := by decide
  rcases family_descends (prefixWord ++ tailWord_804818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804831 : List Nat := [1, 1, 2, 3, 4, 2, 1, 2, 1, 5]
def baseStart_804831 : Nat := 118140960795 + 804831 * 2 ^ 59
def prefixEnd_804831 : Nat := 4983230072969 + 3 ^ 40 * 804831 * 2
def baseEnd_804831 : Nat := 275510099092563885807437

theorem tailTrace_804831 : CollatzResearch.WordTrace tailWord_804831 prefixEnd_804831 275510099092563885807437 := by
  unfold tailWord_804831
  simp only [CollatzResearch.WordTrace]
  refine ⟨29354598147242216036622347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19569732098161477357748231 29354598147242216036622347)
  ·
    refine ⟨44031897220863324054933521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29354598147242216036622347 44031897220863324054933521)
    ·
      refine ⟨33023922915647493041200141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44031897220863324054933521 33023922915647493041200141)
      ·
        refine ⟨12383971093367809890450053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33023922915647493041200141 12383971093367809890450053)
        ·
          refine ⟨2321994580006464354459385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12383971093367809890450053 2321994580006464354459385)
          ·
            refine ⟨1741495935004848265844539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2321994580006464354459385 1741495935004848265844539)
            ·
              refine ⟨2612243902507272398766809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1741495935004848265844539 2612243902507272398766809)
              ·
                refine ⟨1959182926880454299075107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2612243902507272398766809 1959182926880454299075107)
                ·
                  refine ⟨2938774390320681448612661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1959182926880454299075107 2938774390320681448612661)
                  ·
                    refine ⟨275510099092563885807437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2938774390320681448612661 275510099092563885807437)
                    ·
                      rfl

theorem cell22_804831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 2, 1, 5].length) (baseStart_804831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_804831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_804831 prefixEnd_804831 := by exact prefixLift 804831
  have htrace : WordTrace (prefixWord ++ tailWord_804831) baseStart_804831 baseEnd_804831 := by
    simpa [prefixWord, tailWord_804831, baseEnd_804831] using wordTrace_append hprefix tailTrace_804831
  have hstable : (prefixWord ++ tailWord_804831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804831).length < 2 ^ (prefixWord ++ tailWord_804831).sum := by decide
  have hdescent : baseEnd_804831 < baseStart_804831 := by decide
  rcases family_descends (prefixWord ++ tailWord_804831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804889 : List Nat := [1, 2, 1, 2, 1, 1, 3, 4, 7]
def baseStart_804889 : Nat := 118140960795 + 804889 * 2 ^ 59
def prefixEnd_804889 : Nat := 4983230072969 + 3 ^ 40 * 804889 * 2
def baseEnd_804889 : Nat := 91843317892623689285753

theorem tailTrace_804889 : CollatzResearch.WordTrace tailWord_804889 prefixEnd_804889 91843317892623689285753 := by
  unfold tailWord_804889
  simp only [CollatzResearch.WordTrace]
  refine ⟨29356713581032091942233721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19571142387354727961489147 29356713581032091942233721)
  ·
    refine ⟨22017535185774068956675291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29356713581032091942233721 22017535185774068956675291)
    ·
      refine ⟨33026302778661103435012937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22017535185774068956675291 33026302778661103435012937)
      ·
        refine ⟨24769727083995827576259703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33026302778661103435012937 24769727083995827576259703)
        ·
          refine ⟨37154590625993741364389555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24769727083995827576259703 37154590625993741364389555)
          ·
            refine ⟨55731885938990612046584333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37154590625993741364389555 55731885938990612046584333)
            ·
              refine ⟨20899457227121479517469125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55731885938990612046584333 20899457227121479517469125)
              ·
                refine ⟨3918648230085277409525461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20899457227121479517469125 3918648230085277409525461)
                ·
                  refine ⟨91843317892623689285753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3918648230085277409525461 91843317892623689285753)
                  ·
                    rfl

theorem cell22_804889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4, 7].length) (baseStart_804889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_804889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_804889 prefixEnd_804889 := by exact prefixLift 804889
  have htrace : WordTrace (prefixWord ++ tailWord_804889) baseStart_804889 baseEnd_804889 := by
    simpa [prefixWord, tailWord_804889, baseEnd_804889] using wordTrace_append hprefix tailTrace_804889
  have hstable : (prefixWord ++ tailWord_804889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804889).length < 2 ^ (prefixWord ++ tailWord_804889).sum := by decide
  have hdescent : baseEnd_804889 < baseStart_804889 := by decide
  rcases family_descends (prefixWord ++ tailWord_804889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804910 : List Nat := [4, 1, 3, 1, 1, 3, 2, 1, 3, 3]
def baseStart_804910 : Nat := 118140960795 + 804910 * 2 ^ 59
def prefixEnd_804910 : Nat := 4983230072969 + 3 ^ 40 * 804910 * 2
def baseEnd_804910 : Nat := 275537142407034013082195

theorem tailTrace_804910 : CollatzResearch.WordTrace tailWord_804910 prefixEnd_804910 275537142407034013082195 := by
  unfold tailWord_804910
  simp only [CollatzResearch.WordTrace]
  refine ⟨3669684939244501566093523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19571653009304008352498789 3669684939244501566093523)
  ·
    refine ⟨5504527408866752349140285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3669684939244501566093523 5504527408866752349140285)
    ·
      refine ⟨2064197778325032130927607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5504527408866752349140285 2064197778325032130927607)
      ·
        refine ⟨3096296667487548196391411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2064197778325032130927607 3096296667487548196391411)
        ·
          refine ⟨4644445001231322294587117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3096296667487548196391411 4644445001231322294587117)
          ·
            refine ⟨1741666875461745860470169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4644445001231322294587117 1741666875461745860470169)
            ·
              refine ⟨1306250156596309395352627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1741666875461745860470169 1306250156596309395352627)
              ·
                refine ⟨1959375234894464093028941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1306250156596309395352627 1959375234894464093028941)
                ·
                  refine ⟨734765713085424034885853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1959375234894464093028941 734765713085424034885853)
                  ·
                    refine ⟨275537142407034013082195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 734765713085424034885853 275537142407034013082195)
                    ·
                      rfl

theorem cell22_804910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_804910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_804910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_804910 prefixEnd_804910 := by exact prefixLift 804910
  have htrace : WordTrace (prefixWord ++ tailWord_804910) baseStart_804910 baseEnd_804910 := by
    simpa [prefixWord, tailWord_804910, baseEnd_804910] using wordTrace_append hprefix tailTrace_804910
  have hstable : (prefixWord ++ tailWord_804910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804910).length < 2 ^ (prefixWord ++ tailWord_804910).sum := by decide
  have hdescent : baseEnd_804910 < baseStart_804910 := by decide
  rcases family_descends (prefixWord ++ tailWord_804910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804996 : List Nat := [2, 3, 2, 1, 2, 1, 1, 10]
def baseStart_804996 : Nat := 118140960795 + 804996 * 2 ^ 59
def prefixEnd_804996 : Nat := 4983230072969 + 3 ^ 40 * 804996 * 2
def baseEnd_804996 : Nat := 30618509107173161714659

theorem tailTrace_804996 : CollatzResearch.WordTrace tailWord_804996 prefixEnd_804996 30618509107173161714659 := by
  unfold tailWord_804996
  simp only [CollatzResearch.WordTrace]
  refine ⟨14680308095822224608189421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19573744127762966144252561 14680308095822224608189421)
  ·
    refine ⟨5505115535933334228071033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14680308095822224608189421 5505115535933334228071033)
    ·
      refine ⟨4128836651950000671053275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5505115535933334228071033 4128836651950000671053275)
      ·
        refine ⟨6193254977925001006579913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4128836651950000671053275 6193254977925001006579913)
        ·
          refine ⟨4644941233443750754934935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6193254977925001006579913 4644941233443750754934935)
          ·
            refine ⟨6967411850165626132402403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4644941233443750754934935 6967411850165626132402403)
            ·
              refine ⟨10451117775248439198603605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6967411850165626132402403 10451117775248439198603605)
              ·
                refine ⟨30618509107173161714659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 10451117775248439198603605 30618509107173161714659)
                ·
                  rfl

theorem cell22_804996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 10].length) (baseStart_804996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_804996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_804996 prefixEnd_804996 := by exact prefixLift 804996
  have htrace : WordTrace (prefixWord ++ tailWord_804996) baseStart_804996 baseEnd_804996 := by
    simpa [prefixWord, tailWord_804996, baseEnd_804996] using wordTrace_append hprefix tailTrace_804996
  have hstable : (prefixWord ++ tailWord_804996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804996).length < 2 ^ (prefixWord ++ tailWord_804996).sum := by decide
  have hdescent : baseEnd_804996 < baseStart_804996 := by decide
  rcases family_descends (prefixWord ++ tailWord_804996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805103 : List Nat := [1, 1, 2, 1, 6, 1, 2, 2, 6]
def baseStart_805103 : Nat := 118140960795 + 805103 * 2 ^ 59
def prefixEnd_805103 : Nat := 4983230072969 + 3 ^ 40 * 805103 * 2
def baseEnd_805103 : Nat := 91867736750415281002201

theorem tailTrace_805103 : CollatzResearch.WordTrace tailWord_805103 prefixEnd_805103 91867736750415281002201 := by
  unfold tailWord_805103
  simp only [CollatzResearch.WordTrace]
  refine ⟨29364518802256806490523963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19576345868171204327015975 29364518802256806490523963)
  ·
    refine ⟨44046778203385209735785945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29364518802256806490523963 44046778203385209735785945)
    ·
      refine ⟨33035083652538907301839459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44046778203385209735785945 33035083652538907301839459)
      ·
        refine ⟨49552625478808360952759189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33035083652538907301839459 49552625478808360952759189)
        ·
          refine ⟨2322779319319141919660587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 49552625478808360952759189 2322779319319141919660587)
          ·
            refine ⟨3484168978978712879490881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2322779319319141919660587 3484168978978712879490881)
            ·
              refine ⟨2613126734234034659618161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3484168978978712879490881 2613126734234034659618161)
              ·
                refine ⟨1959845050675525994713621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2613126734234034659618161 1959845050675525994713621)
                ·
                  refine ⟨91867736750415281002201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1959845050675525994713621 91867736750415281002201)
                  ·
                    rfl

theorem cell22_805103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 2, 6].length) (baseStart_805103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_805103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_805103 prefixEnd_805103 := by exact prefixLift 805103
  have htrace : WordTrace (prefixWord ++ tailWord_805103) baseStart_805103 baseEnd_805103 := by
    simpa [prefixWord, tailWord_805103, baseEnd_805103] using wordTrace_append hprefix tailTrace_805103
  have hstable : (prefixWord ++ tailWord_805103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805103).length < 2 ^ (prefixWord ++ tailWord_805103).sum := by decide
  have hdescent : baseEnd_805103 < baseStart_805103 := by decide
  rcases family_descends (prefixWord ++ tailWord_805103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805120 : List Nat := [2, 1, 1, 2, 1, 1, 7, 3, 4]
def baseStart_805120 : Nat := 118140960795 + 805120 * 2 ^ 59
def prefixEnd_805120 : Nat := 4983230072969 + 3 ^ 40 * 805120 * 2
def baseEnd_805120 : Nat := 91869676566221155110517

theorem tailTrace_805120 : CollatzResearch.WordTrace tailWord_805120 prefixEnd_805120 91869676566221155110517 := by
  unfold tailWord_805120
  simp only [CollatzResearch.WordTrace]
  refine ⟨14682569421597609196946407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19576759228796812262595209 14682569421597609196946407)
  ·
    refine ⟨22023854132396413795419611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14682569421597609196946407 22023854132396413795419611)
    ·
      refine ⟨33035781198594620693129417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22023854132396413795419611 33035781198594620693129417)
      ·
        refine ⟨24776835898945965519847063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33035781198594620693129417 24776835898945965519847063)
        ·
          refine ⟨37165253848418948279770595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24776835898945965519847063 37165253848418948279770595)
          ·
            refine ⟨55747880772628422419655893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37165253848418948279770595 55747880772628422419655893)
            ·
              refine ⟨1306590955608478650460685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 55747880772628422419655893 1306590955608478650460685)
              ·
                refine ⟨489971608353179493922757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1306590955608478650460685 489971608353179493922757)
                ·
                  refine ⟨91869676566221155110517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 489971608353179493922757 91869676566221155110517)
                  ·
                    rfl

theorem cell22_805120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 3, 4].length) (baseStart_805120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_805120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_805120 prefixEnd_805120 := by exact prefixLift 805120
  have htrace : WordTrace (prefixWord ++ tailWord_805120) baseStart_805120 baseEnd_805120 := by
    simpa [prefixWord, tailWord_805120, baseEnd_805120] using wordTrace_append hprefix tailTrace_805120
  have hstable : (prefixWord ++ tailWord_805120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805120).length < 2 ^ (prefixWord ++ tailWord_805120).sum := by decide
  have hdescent : baseEnd_805120 < baseStart_805120 := by decide
  rcases family_descends (prefixWord ++ tailWord_805120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805122 : List Nat := [3, 4, 1, 1, 2, 1, 2, 3, 1, 4]
def baseStart_805122 : Nat := 118140960795 + 805122 * 2 ^ 59
def prefixEnd_805122 : Nat := 4983230072969 + 3 ^ 40 * 805122 * 2
def baseEnd_805122 : Nat := 275609714339536126781545

theorem tailTrace_805122 : CollatzResearch.WordTrace tailWord_805122 prefixEnd_805122 275609714339536126781545 := by
  unfold tailWord_805122
  simp only [CollatzResearch.WordTrace]
  refine ⟨7341302947296993183866405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19576807859458648490310413 7341302947296993183866405)
  ·
    refine ⟨1376494302618186221974951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7341302947296993183866405 1376494302618186221974951)
    ·
      refine ⟨2064741453927279332962427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1376494302618186221974951 2064741453927279332962427)
      ·
        refine ⟨3097112180890918999443641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2064741453927279332962427 3097112180890918999443641)
        ·
          refine ⟨2322834135668189249582731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3097112180890918999443641 2322834135668189249582731)
          ·
            refine ⟨3484251203502283874374097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2322834135668189249582731 3484251203502283874374097)
            ·
              refine ⟨2613188402626712905780573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3484251203502283874374097 2613188402626712905780573)
              ·
                refine ⟨979945650985017339667715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2613188402626712905780573 979945650985017339667715)
                ·
                  refine ⟨1469918476477526009501573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 979945650985017339667715 1469918476477526009501573)
                  ·
                    refine ⟨275609714339536126781545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1469918476477526009501573 275609714339536126781545)
                    ·
                      rfl

theorem cell22_805122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_805122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_805122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_805122 prefixEnd_805122 := by exact prefixLift 805122
  have htrace : WordTrace (prefixWord ++ tailWord_805122) baseStart_805122 baseEnd_805122 := by
    simpa [prefixWord, tailWord_805122, baseEnd_805122] using wordTrace_append hprefix tailTrace_805122
  have hstable : (prefixWord ++ tailWord_805122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805122).length < 2 ^ (prefixWord ++ tailWord_805122).sum := by decide
  have hdescent : baseEnd_805122 < baseStart_805122 := by decide
  rcases family_descends (prefixWord ++ tailWord_805122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805137 : List Nat := [1, 2, 2, 1, 1, 6, 3, 2, 4]
def baseStart_805137 : Nat := 118140960795 + 805137 * 2 ^ 59
def prefixEnd_805137 : Nat := 4983230072969 + 3 ^ 40 * 805137 * 2
def baseEnd_805137 : Nat := 91871616382027029218833

theorem tailTrace_805137 : CollatzResearch.WordTrace tailWord_805137 prefixEnd_805137 91871616382027029218833 := by
  unfold tailWord_805137
  simp only [CollatzResearch.WordTrace]
  refine ⟨29365758884133630297261665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19577172589422420198174443 29365758884133630297261665)
  ·
    refine ⟨22024319163100222722946249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29365758884133630297261665 22024319163100222722946249)
    ·
      refine ⟨16518239372325167042209687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22024319163100222722946249 16518239372325167042209687)
      ·
        refine ⟨24777359058487750563314531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16518239372325167042209687 24777359058487750563314531)
        ·
          refine ⟨37166038587731625844971797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24777359058487750563314531 37166038587731625844971797)
          ·
            refine ⟨1742158058799919961483053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 37166038587731625844971797 1742158058799919961483053)
            ·
              refine ⟨653309272049969985556145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1742158058799919961483053 653309272049969985556145)
              ·
                refine ⟨489981954037477489167109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 653309272049969985556145 489981954037477489167109)
                ·
                  refine ⟨91871616382027029218833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 489981954037477489167109 91871616382027029218833)
                  ·
                    rfl

theorem cell22_805137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 3, 2, 4].length) (baseStart_805137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_805137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_805137 prefixEnd_805137 := by exact prefixLift 805137
  have htrace : WordTrace (prefixWord ++ tailWord_805137) baseStart_805137 baseEnd_805137 := by
    simpa [prefixWord, tailWord_805137, baseEnd_805137] using wordTrace_append hprefix tailTrace_805137
  have hstable : (prefixWord ++ tailWord_805137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805137).length < 2 ^ (prefixWord ++ tailWord_805137).sum := by decide
  have hdescent : baseEnd_805137 < baseStart_805137 := by decide
  rcases family_descends (prefixWord ++ tailWord_805137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805152 : List Nat := [2, 1, 1, 5, 2, 2, 1, 3, 2, 3]
def baseStart_805152 : Nat := 118140960795 + 805152 * 2 ^ 59
def prefixEnd_805152 : Nat := 4983230072969 + 3 ^ 40 * 805152 * 2
def baseEnd_805152 : Nat := 275619983952626048531453

theorem tailTrace_805152 : CollatzResearch.WordTrace tailWord_805152 prefixEnd_805152 275619983952626048531453 := by
  unfold tailWord_805152
  simp only [CollatzResearch.WordTrace]
  refine ⟨14683152989539643929528855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19577537319386191906038473 14683152989539643929528855)
  ·
    refine ⟨22024729484309465894293283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14683152989539643929528855 22024729484309465894293283)
    ·
      refine ⟨33037094226464198841439925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22024729484309465894293283 33037094226464198841439925)
      ·
        refine ⟨3097227583731018641384993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33037094226464198841439925 3097227583731018641384993)
        ·
          refine ⟨2322920687798263981038745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3097227583731018641384993 2322920687798263981038745)
          ·
            refine ⟨1742190515848697985779059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2322920687798263981038745 1742190515848697985779059)
            ·
              refine ⟨2613285773773046978668589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1742190515848697985779059 2613285773773046978668589)
              ·
                refine ⟨979982165164892617000721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2613285773773046978668589 979982165164892617000721)
                ·
                  refine ⟨734986623873669462750541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 979982165164892617000721 734986623873669462750541)
                  ·
                    refine ⟨275619983952626048531453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 734986623873669462750541 275619983952626048531453)
                    ·
                      rfl

theorem cell22_805152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 3, 2, 3].length) (baseStart_805152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_805152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_805152 prefixEnd_805152 := by exact prefixLift 805152
  have htrace : WordTrace (prefixWord ++ tailWord_805152) baseStart_805152 baseEnd_805152 := by
    simpa [prefixWord, tailWord_805152, baseEnd_805152] using wordTrace_append hprefix tailTrace_805152
  have hstable : (prefixWord ++ tailWord_805152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805152).length < 2 ^ (prefixWord ++ tailWord_805152).sum := by decide
  have hdescent : baseEnd_805152 < baseStart_805152 := by decide
  rcases family_descends (prefixWord ++ tailWord_805152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805188 : List Nat := [2, 3, 4, 1, 3, 1, 2, 2, 4]
def baseStart_805188 : Nat := 118140960795 + 805188 * 2 ^ 59
def prefixEnd_805188 : Nat := 4983230072969 + 3 ^ 40 * 805188 * 2
def baseEnd_805188 : Nat := 91877435829444651543781

theorem tailTrace_805188 : CollatzResearch.WordTrace tailWord_805188 prefixEnd_805188 91877435829444651543781 := by
  unfold tailWord_805188
  simp only [CollatzResearch.WordTrace]
  refine ⟨14683809503474433003684109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19578412671299244004912145 14683809503474433003684109)
  ·
    refine ⟨5506428563802912376381541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14683809503474433003684109 5506428563802912376381541)
    ·
      refine ⟨1032455355713046070571539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5506428563802912376381541 1032455355713046070571539)
      ·
        refine ⟨1548683033569569105857309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1032455355713046070571539 1548683033569569105857309)
        ·
          refine ⟨580756137588588414696491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1548683033569569105857309 580756137588588414696491)
          ·
            refine ⟨871134206382882622044737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 580756137588588414696491 871134206382882622044737)
            ·
              refine ⟨653350654787161966533553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 871134206382882622044737 653350654787161966533553)
              ·
                refine ⟨490012991090371474900165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 653350654787161966533553 490012991090371474900165)
                ·
                  refine ⟨91877435829444651543781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 490012991090371474900165 91877435829444651543781)
                  ·
                    rfl

theorem cell22_805188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 2, 2, 4].length) (baseStart_805188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_805188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_805188 prefixEnd_805188 := by exact prefixLift 805188
  have htrace : WordTrace (prefixWord ++ tailWord_805188) baseStart_805188 baseEnd_805188 := by
    simpa [prefixWord, tailWord_805188, baseEnd_805188] using wordTrace_append hprefix tailTrace_805188
  have hstable : (prefixWord ++ tailWord_805188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805188).length < 2 ^ (prefixWord ++ tailWord_805188).sum := by decide
  have hdescent : baseEnd_805188 < baseStart_805188 := by decide
  rcases family_descends (prefixWord ++ tailWord_805188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805255 : List Nat := [1, 1, 4, 2, 2, 1, 4, 1, 6]
def baseStart_805255 : Nat := 118140960795 + 805255 * 2 ^ 59
def prefixEnd_805255 : Nat := 4983230072969 + 3 ^ 40 * 805255 * 2
def baseEnd_805255 : Nat := 91885080985856037735379

theorem tailTrace_805255 : CollatzResearch.WordTrace tailWord_805255 prefixEnd_805255 91885080985856037735379 := by
  unfold tailWord_805255
  simp only [CollatzResearch.WordTrace]
  refine ⟨29370062697706136450057219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19580041798470757633371479 29370062697706136450057219)
  ·
    refine ⟨44055094046559204675085829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29370062697706136450057219 44055094046559204675085829)
    ·
      refine ⟨8260330133729850876578593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44055094046559204675085829 8260330133729850876578593)
      ·
        refine ⟨6195247600297388157433945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8260330133729850876578593 6195247600297388157433945)
        ·
          refine ⟨4646435700223041118075459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6195247600297388157433945 4646435700223041118075459)
          ·
            refine ⟨6969653550334561677113189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4646435700223041118075459 6969653550334561677113189)
            ·
              refine ⟨1306810040687730314458723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6969653550334561677113189 1306810040687730314458723)
              ·
                refine ⟨1960215061031595471688085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1306810040687730314458723 1960215061031595471688085)
                ·
                  refine ⟨91885080985856037735379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1960215061031595471688085 91885080985856037735379)
                  ·
                    rfl

theorem cell22_805255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 1, 6].length) (baseStart_805255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_805255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_805255 prefixEnd_805255 := by exact prefixLift 805255
  have htrace : WordTrace (prefixWord ++ tailWord_805255) baseStart_805255 baseEnd_805255 := by
    simpa [prefixWord, tailWord_805255, baseEnd_805255] using wordTrace_append hprefix tailTrace_805255
  have hstable : (prefixWord ++ tailWord_805255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805255).length < 2 ^ (prefixWord ++ tailWord_805255).sum := by decide
  have hdescent : baseEnd_805255 < baseStart_805255 := by decide
  rcases family_descends (prefixWord ++ tailWord_805255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805285 : List Nat := [1, 3, 1, 2, 1, 1, 4, 3, 2, 4]
def baseStart_805285 : Nat := 118140960795 + 805285 * 2 ^ 59
def prefixEnd_805285 : Nat := 4983230072969 + 3 ^ 40 * 805285 * 2
def baseEnd_805285 : Nat := 275665512570658034956045

theorem tailTrace_805285 : CollatzResearch.WordTrace tailWord_805285 prefixEnd_805285 275665512570658034956045 := by
  unfold tailWord_805285
  simp only [CollatzResearch.WordTrace]
  refine ⟨29371156887597451573649309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19580771258398301049099539 29371156887597451573649309)
  ·
    refine ⟨11014183832849044340118491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29371156887597451573649309 11014183832849044340118491)
    ·
      refine ⟨16521275749273566510177737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11014183832849044340118491 16521275749273566510177737)
      ·
        refine ⟨12390956811955174882633303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16521275749273566510177737 12390956811955174882633303)
        ·
          refine ⟨18586435217932762323949955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12390956811955174882633303 18586435217932762323949955)
          ·
            refine ⟨27879652826899143485924933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18586435217932762323949955 27879652826899143485924933)
            ·
              refine ⟨5227434905043589403610925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27879652826899143485924933 5227434905043589403610925)
              ·
                refine ⟨1960288089391346026354097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5227434905043589403610925 1960288089391346026354097)
                ·
                  refine ⟨1470216067043509519765573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1960288089391346026354097 1470216067043509519765573)
                  ·
                    refine ⟨275665512570658034956045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1470216067043509519765573 275665512570658034956045)
                    ·
                      rfl

theorem cell22_805285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 3, 2, 4].length) (baseStart_805285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_805285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_805285 prefixEnd_805285 := by exact prefixLift 805285
  have htrace : WordTrace (prefixWord ++ tailWord_805285) baseStart_805285 baseEnd_805285 := by
    simpa [prefixWord, tailWord_805285, baseEnd_805285] using wordTrace_append hprefix tailTrace_805285
  have hstable : (prefixWord ++ tailWord_805285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805285).length < 2 ^ (prefixWord ++ tailWord_805285).sum := by decide
  have hdescent : baseEnd_805285 < baseStart_805285 := by decide
  rcases family_descends (prefixWord ++ tailWord_805285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805287 : List Nat := [1, 1, 6, 1, 1, 2, 1, 2, 4, 3]
def baseStart_805287 : Nat := 118140960795 + 805287 * 2 ^ 59
def prefixEnd_805287 : Nat := 4983230072969 + 3 ^ 40 * 805287 * 2
def baseEnd_805287 : Nat := 275666197211530696406039

theorem tailTrace_805287 : CollatzResearch.WordTrace tailWord_805287 prefixEnd_805287 275666197211530696406039 := by
  unfold tailWord_805287
  simp only [CollatzResearch.WordTrace]
  refine ⟨29371229833590205915222115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19580819889060137276814743 29371229833590205915222115)
  ·
    refine ⟨44056844750385308872833173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29371229833590205915222115 44056844750385308872833173)
    ·
      refine ⟨2065164597674311353414055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 44056844750385308872833173 2065164597674311353414055)
      ·
        refine ⟨3097746896511467030121083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2065164597674311353414055 3097746896511467030121083)
        ·
          refine ⟨4646620344767200545181625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3097746896511467030121083 4646620344767200545181625)
          ·
            refine ⟨3484965258575400408886219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4646620344767200545181625 3484965258575400408886219)
            ·
              refine ⟨5227447887863100613329329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3484965258575400408886219 5227447887863100613329329)
              ·
                refine ⟨3920585915897325459996997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5227447887863100613329329 3920585915897325459996997)
                ·
                  refine ⟨735109859230748523749437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3920585915897325459996997 735109859230748523749437)
                  ·
                    refine ⟨275666197211530696406039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 735109859230748523749437 275666197211530696406039)
                    ·
                      rfl

theorem cell22_805287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_805287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_805287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_805287 prefixEnd_805287 := by exact prefixLift 805287
  have htrace : WordTrace (prefixWord ++ tailWord_805287) baseStart_805287 baseEnd_805287 := by
    simpa [prefixWord, tailWord_805287, baseEnd_805287] using wordTrace_append hprefix tailTrace_805287
  have hstable : (prefixWord ++ tailWord_805287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805287).length < 2 ^ (prefixWord ++ tailWord_805287).sum := by decide
  have hdescent : baseEnd_805287 < baseStart_805287 := by decide
  rcases family_descends (prefixWord ++ tailWord_805287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805360 : List Nat := [2, 1, 1, 1, 3, 3, 2, 2, 2, 5]
def baseStart_805360 : Nat := 118140960795 + 805360 * 2 ^ 59
def prefixEnd_805360 : Nat := 4983230072969 + 3 ^ 40 * 805360 * 2
def baseEnd_805360 : Nat := 275691186603382839330815

theorem tailTrace_805360 : CollatzResearch.WordTrace tailWord_805360 prefixEnd_805360 275691186603382839330815 := by
  unfold tailWord_805360
  simp only [CollatzResearch.WordTrace]
  refine ⟨14686946181162869691314767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19582594908217159588419689 14686946181162869691314767)
  ·
    refine ⟨22030419271744304536972151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14686946181162869691314767 22030419271744304536972151)
    ·
      refine ⟨33045628907616456805458227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22030419271744304536972151 33045628907616456805458227)
      ·
        refine ⟨49568443361424685208187341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33045628907616456805458227 49568443361424685208187341)
        ·
          refine ⟨18588166260534256953070253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49568443361424685208187341 18588166260534256953070253)
          ·
            refine ⟨6970562347700346357401345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18588166260534256953070253 6970562347700346357401345)
            ·
              refine ⟨5227921760775259768051009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6970562347700346357401345 5227921760775259768051009)
              ·
                refine ⟨3920941320581444826038257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5227921760775259768051009 3920941320581444826038257)
                ·
                  refine ⟨2940705990436083619528693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3920941320581444826038257 2940705990436083619528693)
                  ·
                    refine ⟨275691186603382839330815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2940705990436083619528693 275691186603382839330815)
                    ·
                      rfl

theorem cell22_805360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 2, 5].length) (baseStart_805360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_805360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_805360 prefixEnd_805360 := by exact prefixLift 805360
  have htrace : WordTrace (prefixWord ++ tailWord_805360) baseStart_805360 baseEnd_805360 := by
    simpa [prefixWord, tailWord_805360, baseEnd_805360] using wordTrace_append hprefix tailTrace_805360
  have hstable : (prefixWord ++ tailWord_805360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805360).length < 2 ^ (prefixWord ++ tailWord_805360).sum := by decide
  have hdescent : baseEnd_805360 < baseStart_805360 := by decide
  rcases family_descends (prefixWord ++ tailWord_805360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805366 : List Nat := [5, 1, 1, 1, 2, 1, 3, 4, 1, 3]
def baseStart_805366 : Nat := 118140960795 + 805366 * 2 ^ 59
def prefixEnd_805366 : Nat := 4983230072969 + 3 ^ 40 * 805366 * 2
def baseEnd_805366 : Nat := 275693240526000823680797

theorem tailTrace_805366 : CollatzResearch.WordTrace tailWord_805366 prefixEnd_805366 275693240526000823680797 := by
  unfold tailWord_805366
  simp only [CollatzResearch.WordTrace]
  refine ⟨1835881950019000150459247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19582740800202668271565301 1835881950019000150459247)
  ·
    refine ⟨2753822925028500225688871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1835881950019000150459247 2753822925028500225688871)
    ·
      refine ⟨4130734387542750338533307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2753822925028500225688871 4130734387542750338533307)
      ·
        refine ⟨6196101581314125507799961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4130734387542750338533307 6196101581314125507799961)
        ·
          refine ⟨4647076185985594130849971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6196101581314125507799961 4647076185985594130849971)
          ·
            refine ⟨6970614278978391196274957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4647076185985594130849971 6970614278978391196274957)
            ·
              refine ⟨2613980354616896698603109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6970614278978391196274957 2613980354616896698603109)
              ·
                refine ⟨490121316490668130988083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2613980354616896698603109 490121316490668130988083)
                ·
                  refine ⟨735181974736002196482125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 490121316490668130988083 735181974736002196482125)
                  ·
                    refine ⟨275693240526000823680797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 735181974736002196482125 275693240526000823680797)
                    ·
                      rfl

theorem cell22_805366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 4, 1, 3].length) (baseStart_805366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_805366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_805366 prefixEnd_805366 := by exact prefixLift 805366
  have htrace : WordTrace (prefixWord ++ tailWord_805366) baseStart_805366 baseEnd_805366 := by
    simpa [prefixWord, tailWord_805366, baseEnd_805366] using wordTrace_append hprefix tailTrace_805366
  have hstable : (prefixWord ++ tailWord_805366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805366).length < 2 ^ (prefixWord ++ tailWord_805366).sum := by decide
  have hdescent : baseEnd_805366 < baseStart_805366 := by decide
  rcases family_descends (prefixWord ++ tailWord_805366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805375 : List Nat := [1, 1, 2, 2, 1, 2, 3, 1, 5, 4]
def baseStart_805375 : Nat := 118140960795 + 805375 * 2 ^ 59
def prefixEnd_805375 : Nat := 4983230072969 + 3 ^ 40 * 805375 * 2
def baseEnd_805375 : Nat := 275696321409927800205769

theorem tailTrace_805375 : CollatzResearch.WordTrace tailWord_805375 prefixEnd_805375 275696321409927800205769 := by
  unfold tailWord_805375
  simp only [CollatzResearch.WordTrace]
  refine ⟨29374439457271396944425579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19582959638180931296283719 29374439457271396944425579)
  ·
    refine ⟨44061659185907095416638369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29374439457271396944425579 44061659185907095416638369)
    ·
      refine ⟨33046244389430321562478777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44061659185907095416638369 33046244389430321562478777)
      ·
        refine ⟨24784683292072741171859083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33046244389430321562478777 24784683292072741171859083)
        ·
          refine ⟨37177024938109111757788625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24784683292072741171859083 37177024938109111757788625)
          ·
            refine ⟨27882768703581833818341469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37177024938109111757788625 27882768703581833818341469)
            ·
              refine ⟨10456038263843187681878051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27882768703581833818341469 10456038263843187681878051)
              ·
                refine ⟨15684057395764781522817077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10456038263843187681878051 15684057395764781522817077)
                ·
                  refine ⟨1470380380852948267764101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15684057395764781522817077 1470380380852948267764101)
                  ·
                    refine ⟨275696321409927800205769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1470380380852948267764101 275696321409927800205769)
                    ·
                      rfl

theorem cell22_805375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 5, 4].length) (baseStart_805375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_805375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_805375 prefixEnd_805375 := by exact prefixLift 805375
  have htrace : WordTrace (prefixWord ++ tailWord_805375) baseStart_805375 baseEnd_805375 := by
    simpa [prefixWord, tailWord_805375, baseEnd_805375] using wordTrace_append hprefix tailTrace_805375
  have hstable : (prefixWord ++ tailWord_805375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805375).length < 2 ^ (prefixWord ++ tailWord_805375).sum := by decide
  have hdescent : baseEnd_805375 < baseStart_805375 := by decide
  rcases family_descends (prefixWord ++ tailWord_805375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805377 : List Nat := [1, 2, 4, 1, 3, 2, 1, 1, 2, 5]
def baseStart_805377 : Nat := 118140960795 + 805377 * 2 ^ 59
def prefixEnd_805377 : Nat := 4983230072969 + 3 ^ 40 * 805377 * 2
def baseEnd_805377 : Nat := 275697006050800461655763

theorem tailTrace_805377 : CollatzResearch.WordTrace tailWord_805377 prefixEnd_805377 275697006050800461655763 := by
  unfold tailWord_805377
  simp only [CollatzResearch.WordTrace]
  refine ⟨29374512403264151285998385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19583008268842767523998923 29374512403264151285998385)
  ·
    refine ⟨22030884302448113464498789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29374512403264151285998385 22030884302448113464498789)
    ·
      refine ⟨4130790806709021274593523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22030884302448113464498789 4130790806709021274593523)
      ·
        refine ⟨6196186210063531911890285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4130790806709021274593523 6196186210063531911890285)
        ·
          refine ⟨2323569828773824466958857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6196186210063531911890285 2323569828773824466958857)
          ·
            refine ⟨1742677371580368350219143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2323569828773824466958857 1742677371580368350219143)
            ·
              refine ⟨2614016057370552525328715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1742677371580368350219143 2614016057370552525328715)
              ·
                refine ⟨3921024086055828787993073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2614016057370552525328715 3921024086055828787993073)
                ·
                  refine ⟨2940768064541871590994805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3921024086055828787993073 2940768064541871590994805)
                  ·
                    refine ⟨275697006050800461655763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2940768064541871590994805 275697006050800461655763)
                    ·
                      rfl

theorem cell22_805377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_805377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_805377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_805377 prefixEnd_805377 := by exact prefixLift 805377
  have htrace : WordTrace (prefixWord ++ tailWord_805377) baseStart_805377 baseEnd_805377 := by
    simpa [prefixWord, tailWord_805377, baseEnd_805377] using wordTrace_append hprefix tailTrace_805377
  have hstable : (prefixWord ++ tailWord_805377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805377).length < 2 ^ (prefixWord ++ tailWord_805377).sum := by decide
  have hdescent : baseEnd_805377 < baseStart_805377 := by decide
  rcases family_descends (prefixWord ++ tailWord_805377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805437 : List Nat := [1, 4, 1, 3, 2, 1, 1, 2, 1, 6]
def baseStart_805437 : Nat := 118140960795 + 805437 * 2 ^ 59
def prefixEnd_805437 : Nat := 4983230072969 + 3 ^ 40 * 805437 * 2
def baseEnd_805437 : Nat := 275717545276980305155579

theorem tailTrace_805437 : CollatzResearch.WordTrace tailWord_805437 prefixEnd_805437 275717545276980305155579 := by
  unfold tailWord_805437
  simp only [CollatzResearch.WordTrace]
  refine ⟨29376700783046781533182565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19584467188697854355455043 29376700783046781533182565)
  ·
    refine ⟨5508131396821271537471731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29376700783046781533182565 5508131396821271537471731)
    ·
      refine ⟨8262197095231907306207597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5508131396821271537471731 8262197095231907306207597)
      ·
        refine ⟨3098323910711965239827849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8262197095231907306207597 3098323910711965239827849)
        ·
          refine ⟨2323742933033973929870887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3098323910711965239827849 2323742933033973929870887)
          ·
            refine ⟨3485614399550960894806331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2323742933033973929870887 3485614399550960894806331)
            ·
              refine ⟨5228421599326441342209497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3485614399550960894806331 5228421599326441342209497)
              ·
                refine ⟨3921316199494831006657123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5228421599326441342209497 3921316199494831006657123)
                ·
                  refine ⟨5881974299242246509985685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3921316199494831006657123 5881974299242246509985685)
                  ·
                    refine ⟨275717545276980305155579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5881974299242246509985685 275717545276980305155579)
                    ·
                      rfl

theorem cell22_805437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 2, 1, 6].length) (baseStart_805437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_805437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_805437 prefixEnd_805437 := by exact prefixLift 805437
  have htrace : WordTrace (prefixWord ++ tailWord_805437) baseStart_805437 baseEnd_805437 := by
    simpa [prefixWord, tailWord_805437, baseEnd_805437] using wordTrace_append hprefix tailTrace_805437
  have hstable : (prefixWord ++ tailWord_805437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805437).length < 2 ^ (prefixWord ++ tailWord_805437).sum := by decide
  have hdescent : baseEnd_805437 < baseStart_805437 := by decide
  rcases family_descends (prefixWord ++ tailWord_805437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805465 : List Nat := [1, 2, 1, 2, 2, 1, 1, 1, 3, 8]
def baseStart_805465 : Nat := 118140960795 + 805465 * 2 ^ 59
def prefixEnd_805465 : Nat := 4983230072969 + 3 ^ 40 * 805465 * 2
def baseEnd_805465 : Nat := 275727130249197565455493

theorem tailTrace_805465 : CollatzResearch.WordTrace tailWord_805465 prefixEnd_805465 275727130249197565455493 := by
  unfold tailWord_805465
  simp only [CollatzResearch.WordTrace]
  refine ⟨29377722026945342315201849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19585148017963561543467899 29377722026945342315201849)
  ·
    refine ⟨22033291520209006736401387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29377722026945342315201849 22033291520209006736401387)
    ·
      refine ⟨33049937280313510104602081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22033291520209006736401387 33049937280313510104602081)
      ·
        refine ⟨24787452960235132578451561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33049937280313510104602081 24787452960235132578451561)
        ·
          refine ⟨18590589720176349433838671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24787452960235132578451561 18590589720176349433838671)
          ·
            refine ⟨27885884580264524150758007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18590589720176349433838671 27885884580264524150758007)
            ·
              refine ⟨41828826870396786226137011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27885884580264524150758007 41828826870396786226137011)
              ·
                refine ⟨62743240305595179339205517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41828826870396786226137011 62743240305595179339205517)
                ·
                  refine ⟨23528715114598192252202069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62743240305595179339205517 23528715114598192252202069)
                  ·
                    refine ⟨275727130249197565455493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 23528715114598192252202069 275727130249197565455493)
                    ·
                      rfl

theorem cell22_805465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 8].length) (baseStart_805465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_805465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_805465 prefixEnd_805465 := by exact prefixLift 805465
  have htrace : WordTrace (prefixWord ++ tailWord_805465) baseStart_805465 baseEnd_805465 := by
    simpa [prefixWord, tailWord_805465, baseEnd_805465] using wordTrace_append hprefix tailTrace_805465
  have hstable : (prefixWord ++ tailWord_805465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805465).length < 2 ^ (prefixWord ++ tailWord_805465).sum := by decide
  have hdescent : baseEnd_805465 < baseStart_805465 := by decide
  rcases family_descends (prefixWord ++ tailWord_805465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805482 : List Nat := [3, 1, 3, 2, 1, 1, 2, 1, 2, 6]
def baseStart_805482 : Nat := 118140960795 + 805482 * 2 ^ 59
def prefixEnd_805482 : Nat := 4983230072969 + 3 ^ 40 * 805482 * 2
def baseEnd_805482 : Nat := 275732949696615187780441

theorem tailTrace_805482 : CollatzResearch.WordTrace tailWord_805482 prefixEnd_805482 275732949696615187780441 := by
  unfold tailWord_805482
  simp only [CollatzResearch.WordTrace]
  refine ⟨7344585516970938554642675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19585561378589169479047133 7344585516970938554642675)
  ·
    refine ⟨11016878275456407831964013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7344585516970938554642675 11016878275456407831964013)
    ·
      refine ⟨4131329353296152936986505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11016878275456407831964013 4131329353296152936986505)
      ·
        refine ⟨3098497014972114702739879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4131329353296152936986505 3098497014972114702739879)
        ·
          refine ⟨4647745522458172054109819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3098497014972114702739879 4647745522458172054109819)
          ·
            refine ⟨6971618283687258081164729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4647745522458172054109819 6971618283687258081164729)
            ·
              refine ⟨5228713712765443560873547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6971618283687258081164729 5228713712765443560873547)
              ·
                refine ⟨7843070569148165341310321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5228713712765443560873547 7843070569148165341310321)
                ·
                  refine ⟨5882302926861124005982741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7843070569148165341310321 5882302926861124005982741)
                  ·
                    refine ⟨275732949696615187780441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5882302926861124005982741 275732949696615187780441)
                    ·
                      rfl

theorem cell22_805482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_805482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_805482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_805482 prefixEnd_805482 := by exact prefixLift 805482
  have htrace : WordTrace (prefixWord ++ tailWord_805482) baseStart_805482 baseEnd_805482 := by
    simpa [prefixWord, tailWord_805482, baseEnd_805482] using wordTrace_append hprefix tailTrace_805482
  have hstable : (prefixWord ++ tailWord_805482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805482).length < 2 ^ (prefixWord ++ tailWord_805482).sum := by decide
  have hdescent : baseEnd_805482 < baseStart_805482 := by decide
  rcases family_descends (prefixWord ++ tailWord_805482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805484 : List Nat := [2, 2, 1, 1, 3, 1, 5, 1, 3, 3]
def baseStart_805484 : Nat := 118140960795 + 805484 * 2 ^ 59
def prefixEnd_805484 : Nat := 4983230072969 + 3 ^ 40 * 805484 * 2
def baseEnd_805484 : Nat := 275733634337487849230435

theorem tailTrace_805484 : CollatzResearch.WordTrace tailWord_805484 prefixEnd_805484 275733634337487849230435 := by
  unfold tailWord_805484
  simp only [CollatzResearch.WordTrace]
  refine ⟨14689207506938254280071753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19585610009251005706762337 14689207506938254280071753)
  ·
    refine ⟨11016905630203690710053815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14689207506938254280071753 11016905630203690710053815)
    ·
      refine ⟨16525358445305536065080723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11016905630203690710053815 16525358445305536065080723)
      ·
        refine ⟨24788037667958304097621085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16525358445305536065080723 24788037667958304097621085)
        ·
          refine ⟨9295514125484364036607907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24788037667958304097621085 9295514125484364036607907)
          ·
            refine ⟨13943271188226546054911861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9295514125484364036607907 13943271188226546054911861)
            ·
              refine ⟨1307181673896238692647987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13943271188226546054911861 1307181673896238692647987)
              ·
                refine ⟨1960772510844358038971981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1307181673896238692647987 1960772510844358038971981)
                ·
                  refine ⟨735289691566634264614493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1960772510844358038971981 735289691566634264614493)
                  ·
                    refine ⟨275733634337487849230435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 735289691566634264614493 275733634337487849230435)
                    ·
                      rfl

theorem cell22_805484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 3].length) (baseStart_805484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_805484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_805484 prefixEnd_805484 := by exact prefixLift 805484
  have htrace : WordTrace (prefixWord ++ tailWord_805484) baseStart_805484 baseEnd_805484 := by
    simpa [prefixWord, tailWord_805484, baseEnd_805484] using wordTrace_append hprefix tailTrace_805484
  have hstable : (prefixWord ++ tailWord_805484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805484).length < 2 ^ (prefixWord ++ tailWord_805484).sum := by decide
  have hdescent : baseEnd_805484 < baseStart_805484 := by decide
  rcases family_descends (prefixWord ++ tailWord_805484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805490 : List Nat := [3, 2, 1, 2, 5, 1, 2, 1, 2, 3]
def baseStart_805490 : Nat := 118140960795 + 805490 * 2 ^ 59
def prefixEnd_805490 : Nat := 4983230072969 + 3 ^ 40 * 805490 * 2
def baseEnd_805490 : Nat := 275735688260105833580417

theorem tailTrace_805490 : CollatzResearch.WordTrace tailWord_805490 prefixEnd_805490 275735688260105833580417 := by
  unfold tailWord_805490
  simp only [CollatzResearch.WordTrace]
  refine ⟨7344658462963692896215481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19585755901236514389907949 7344658462963692896215481)
  ·
    refine ⟨5508493847222769672161611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7344658462963692896215481 5508493847222769672161611)
    ·
      refine ⟨8262740770834154508242417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5508493847222769672161611 8262740770834154508242417)
      ·
        refine ⟨6197055578125615881181813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8262740770834154508242417 6197055578125615881181813)
        ·
          refine ⟨580973960449276488860795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6197055578125615881181813 580973960449276488860795)
          ·
            refine ⟨871460940673914733291193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 580973960449276488860795 871460940673914733291193)
            ·
              refine ⟨653595705505436049968395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 871460940673914733291193 653595705505436049968395)
              ·
                refine ⟨980393558258154074952593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 653595705505436049968395 980393558258154074952593)
                ·
                  refine ⟨735295168693615556214445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 980393558258154074952593 735295168693615556214445)
                  ·
                    refine ⟨275735688260105833580417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 735295168693615556214445 275735688260105833580417)
                    ·
                      rfl

theorem cell22_805490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 2, 1, 2, 3].length) (baseStart_805490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_805490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_805490 prefixEnd_805490 := by exact prefixLift 805490
  have htrace : WordTrace (prefixWord ++ tailWord_805490) baseStart_805490 baseEnd_805490 := by
    simpa [prefixWord, tailWord_805490, baseEnd_805490] using wordTrace_append hprefix tailTrace_805490
  have hstable : (prefixWord ++ tailWord_805490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805490).length < 2 ^ (prefixWord ++ tailWord_805490).sum := by decide
  have hdescent : baseEnd_805490 < baseStart_805490 := by decide
  rcases family_descends (prefixWord ++ tailWord_805490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805559 : List Nat := [1, 1, 3, 1, 6, 1, 1, 2, 6]
def baseStart_805559 : Nat := 118140960795 + 805559 * 2 ^ 59
def prefixEnd_805559 : Nat := 4983230072969 + 3 ^ 40 * 805559 * 2
def baseEnd_805559 : Nat := 91919769456737551201735

theorem tailTrace_805559 : CollatzResearch.WordTrace tailWord_805559 prefixEnd_805559 91919769456737551201735 := by
  unfold tailWord_805559
  simp only [CollatzResearch.WordTrace]
  refine ⟨29381150488604796369123731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19587433659069864246082487 29381150488604796369123731)
  ·
    refine ⟨44071725732907194553685597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29381150488604796369123731 44071725732907194553685597)
    ·
      refine ⟨16526897149840197957632099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44071725732907194553685597 16526897149840197957632099)
      ·
        refine ⟨24790345724760296936448149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16526897149840197957632099 24790345724760296936448149)
        ·
          refine ⟨1162047455848138918896007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 24790345724760296936448149 1162047455848138918896007)
          ·
            refine ⟨1743071183772208378344011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1162047455848138918896007 1743071183772208378344011)
            ·
              refine ⟨2614606775658312567516017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1743071183772208378344011 2614606775658312567516017)
              ·
                refine ⟨1960955081743734425637013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2614606775658312567516017 1960955081743734425637013)
                ·
                  refine ⟨91919769456737551201735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1960955081743734425637013 91919769456737551201735)
                  ·
                    rfl

theorem cell22_805559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 2, 6].length) (baseStart_805559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_805559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_805559 prefixEnd_805559 := by exact prefixLift 805559
  have htrace : WordTrace (prefixWord ++ tailWord_805559) baseStart_805559 baseEnd_805559 := by
    simpa [prefixWord, tailWord_805559, baseEnd_805559] using wordTrace_append hprefix tailTrace_805559
  have hstable : (prefixWord ++ tailWord_805559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805559).length < 2 ^ (prefixWord ++ tailWord_805559).sum := by decide
  have hdescent : baseEnd_805559 < baseStart_805559 := by decide
  rcases family_descends (prefixWord ++ tailWord_805559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805576 : List Nat := [2, 1, 3, 1, 2, 4, 2, 3, 4]
def baseStart_805576 : Nat := 118140960795 + 805576 * 2 ^ 59
def prefixEnd_805576 : Nat := 4983230072969 + 3 ^ 40 * 805576 * 2
def baseEnd_805576 : Nat := 91921709272543425310051

theorem tailTrace_805576 : CollatzResearch.WordTrace tailWord_805576 prefixEnd_805576 91921709272543425310051 := by
  unfold tailWord_805576
  simp only [CollatzResearch.WordTrace]
  refine ⟨14690885264771604136246291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19587847019695472181661721 14690885264771604136246291)
  ·
    refine ⟨22036327897157406204369437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14690885264771604136246291 22036327897157406204369437)
    ·
      refine ⟨8263622961434027326638539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22036327897157406204369437 8263622961434027326638539)
      ·
        refine ⟨12395434442151040989957809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8263622961434027326638539 12395434442151040989957809)
        ·
          refine ⟨9296575831613280742468357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12395434442151040989957809 9296575831613280742468357)
          ·
            refine ⟨1743107968427490139212817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9296575831613280742468357 1743107968427490139212817)
            ·
              refine ⟨1307330976320617604409613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1743107968427490139212817 1307330976320617604409613)
              ·
                refine ⟨490249116120231601653605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1307330976320617604409613 490249116120231601653605)
                ·
                  refine ⟨91921709272543425310051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 490249116120231601653605 91921709272543425310051)
                  ·
                    rfl

theorem cell22_805576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 3, 4].length) (baseStart_805576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_805576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_805576 prefixEnd_805576 := by exact prefixLift 805576
  have htrace : WordTrace (prefixWord ++ tailWord_805576) baseStart_805576 baseEnd_805576 := by
    simpa [prefixWord, tailWord_805576, baseEnd_805576] using wordTrace_append hprefix tailTrace_805576
  have hstable : (prefixWord ++ tailWord_805576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805576).length < 2 ^ (prefixWord ++ tailWord_805576).sum := by decide
  have hdescent : baseEnd_805576 < baseStart_805576 := by decide
  rcases family_descends (prefixWord ++ tailWord_805576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805578 : List Nat := [3, 1, 2, 1, 4, 3, 2, 1, 1, 4]
def baseStart_805578 : Nat := 118140960795 + 805578 * 2 ^ 59
def prefixEnd_805578 : Nat := 4983230072969 + 3 ^ 40 * 805578 * 2
def baseEnd_805578 : Nat := 275765812458502937380147

theorem tailTrace_805578 : CollatzResearch.WordTrace tailWord_805578 prefixEnd_805578 275765812458502937380147 := by
  unfold tailWord_805578
  simp only [CollatzResearch.WordTrace]
  refine ⟨7345460868883990653516347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19587895650357308409376925 7345460868883990653516347)
  ·
    refine ⟨11018191303325985980274521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7345460868883990653516347 11018191303325985980274521)
    ·
      refine ⟨8263643477494489485205891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11018191303325985980274521 8263643477494489485205891)
      ·
        refine ⟨12395465216241734227808837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8263643477494489485205891 12395465216241734227808837)
        ·
          refine ⟨2324149728045325167714157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12395465216241734227808837 2324149728045325167714157)
          ·
            refine ⟨871556148016996937892809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2324149728045325167714157 871556148016996937892809)
            ·
              refine ⟨653667111012747703419607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 871556148016996937892809 653667111012747703419607)
              ·
                refine ⟨980500666519121555129411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 653667111012747703419607 980500666519121555129411)
                ·
                  refine ⟨1470750999778682332694117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 980500666519121555129411 1470750999778682332694117)
                  ·
                    refine ⟨275765812458502937380147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1470750999778682332694117 275765812458502937380147)
                    ·
                      rfl

theorem cell22_805578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 2, 1, 1, 4].length) (baseStart_805578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_805578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_805578 prefixEnd_805578 := by exact prefixLift 805578
  have htrace : WordTrace (prefixWord ++ tailWord_805578) baseStart_805578 baseEnd_805578 := by
    simpa [prefixWord, tailWord_805578, baseEnd_805578] using wordTrace_append hprefix tailTrace_805578
  have hstable : (prefixWord ++ tailWord_805578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805578).length < 2 ^ (prefixWord ++ tailWord_805578).sum := by decide
  have hdescent : baseEnd_805578 < baseStart_805578 := by decide
  rcases family_descends (prefixWord ++ tailWord_805578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805591 : List Nat := [1, 1, 3, 2, 1, 4, 3, 2, 2, 3]
def baseStart_805591 : Nat := 118140960795 + 805591 * 2 ^ 59
def prefixEnd_805591 : Nat := 4983230072969 + 3 ^ 40 * 805591 * 2
def baseEnd_805591 : Nat := 275770262624175236805107

theorem tailTrace_805591 : CollatzResearch.WordTrace tailWord_805591 prefixEnd_805591 275770262624175236805107 := by
  unfold tailWord_805591
  simp only [CollatzResearch.WordTrace]
  refine ⟨29382317624488865834288627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19588211749659243889525751 29382317624488865834288627)
  ·
    refine ⟨44073476436733298751432941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29382317624488865834288627 44073476436733298751432941)
    ·
      refine ⟨16527553663774987031787353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44073476436733298751432941 16527553663774987031787353)
      ·
        refine ⟨12395665247831240273840515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16527553663774987031787353 12395665247831240273840515)
        ·
          refine ⟨18593497871746860410760773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12395665247831240273840515 18593497871746860410760773)
          ·
            refine ⟨3486280850952536327017645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18593497871746860410760773 3486280850952536327017645)
            ·
              refine ⟨1307355319107201122631617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3486280850952536327017645 1307355319107201122631617)
              ·
                refine ⟨980516489330400841973713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1307355319107201122631617 980516489330400841973713)
                ·
                  refine ⟨735387366997800631480285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 980516489330400841973713 735387366997800631480285)
                  ·
                    refine ⟨275770262624175236805107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 735387366997800631480285 275770262624175236805107)
                    ·
                      rfl

theorem cell22_805591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 2, 2, 3].length) (baseStart_805591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_805591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_805591 prefixEnd_805591 := by exact prefixLift 805591
  have htrace : WordTrace (prefixWord ++ tailWord_805591) baseStart_805591 baseEnd_805591 := by
    simpa [prefixWord, tailWord_805591, baseEnd_805591] using wordTrace_append hprefix tailTrace_805591
  have hstable : (prefixWord ++ tailWord_805591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805591).length < 2 ^ (prefixWord ++ tailWord_805591).sum := by decide
  have hdescent : baseEnd_805591 < baseStart_805591 := by decide
  rcases family_descends (prefixWord ++ tailWord_805591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805608 : List Nat := [2, 1, 4, 1, 5, 1, 1, 1, 1, 5]
def baseStart_805608 : Nat := 118140960795 + 805608 * 2 ^ 59
def prefixEnd_805608 : Nat := 4983230072969 + 3 ^ 40 * 805608 * 2
def baseEnd_805608 : Nat := 275776082071592859130055

theorem tailTrace_805608 : CollatzResearch.WordTrace tailWord_805608 prefixEnd_805608 275776082071592859130055 := by
  unfold tailWord_805608
  simp only [CollatzResearch.WordTrace]
  refine ⟨14691468832713638868828739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19588625110284851825104985 14691468832713638868828739)
  ·
    refine ⟨22037203249070458303243109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14691468832713638868828739 22037203249070458303243109)
    ·
      refine ⟨4131975609200710931858083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22037203249070458303243109 4131975609200710931858083)
      ·
        refine ⟨6197963413801066397787125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4131975609200710931858083 6197963413801066397787125)
        ·
          refine ⟨581059070043849974792543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6197963413801066397787125 581059070043849974792543)
          ·
            refine ⟨871588605065774962188815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 581059070043849974792543 871588605065774962188815)
            ·
              refine ⟨1307382907598662443283223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 871588605065774962188815 1307382907598662443283223)
              ·
                refine ⟨1961074361397993664924835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1307382907598662443283223 1961074361397993664924835)
                ·
                  refine ⟨2941611542096990497387253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1961074361397993664924835 2941611542096990497387253)
                  ·
                    refine ⟨275776082071592859130055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2941611542096990497387253 275776082071592859130055)
                    ·
                      rfl

theorem cell22_805608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 1, 1, 5].length) (baseStart_805608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_805608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_805608 prefixEnd_805608 := by exact prefixLift 805608
  have htrace : WordTrace (prefixWord ++ tailWord_805608) baseStart_805608 baseEnd_805608 := by
    simpa [prefixWord, tailWord_805608, baseEnd_805608] using wordTrace_append hprefix tailTrace_805608
  have hstable : (prefixWord ++ tailWord_805608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805608).length < 2 ^ (prefixWord ++ tailWord_805608).sum := by decide
  have hdescent : baseEnd_805608 < baseStart_805608 := by decide
  rcases family_descends (prefixWord ++ tailWord_805608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805666 : List Nat := [3, 3, 1, 1, 2, 3, 1, 3, 5]
def baseStart_805666 : Nat := 118140960795 + 805666 * 2 ^ 59
def prefixEnd_805666 : Nat := 4983230072969 + 3 ^ 40 * 805666 * 2
def baseEnd_805666 : Nat := 91931978885633347059959

theorem tailTrace_805666 : CollatzResearch.WordTrace tailWord_805666 prefixEnd_805666 91931978885633347059959 := by
  unfold tailWord_805666
  simp only [CollatzResearch.WordTrace]
  refine ⟨7346263274804288410817213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19590035399478102428845901 7346263274804288410817213)
  ·
    refine ⟨2754848728051608154056455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7346263274804288410817213 2754848728051608154056455)
    ·
      refine ⟨4132273092077412231084683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2754848728051608154056455 4132273092077412231084683)
      ·
        refine ⟨6198409638116118346627025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4132273092077412231084683 6198409638116118346627025)
        ·
          refine ⟨4648807228587088759970269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6198409638116118346627025 4648807228587088759970269)
          ·
            refine ⟨1743302710720158284988851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4648807228587088759970269 1743302710720158284988851)
            ·
              refine ⟨2614954066080237427483277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1743302710720158284988851 2614954066080237427483277)
              ·
                refine ⟨980607774780089035306229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2614954066080237427483277 980607774780089035306229)
                ·
                  refine ⟨91931978885633347059959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 980607774780089035306229 91931978885633347059959)
                  ·
                    rfl

theorem cell22_805666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 3, 5].length) (baseStart_805666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_805666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_805666 prefixEnd_805666 := by exact prefixLift 805666
  have htrace : WordTrace (prefixWord ++ tailWord_805666) baseStart_805666 baseEnd_805666 := by
    simpa [prefixWord, tailWord_805666, baseEnd_805666] using wordTrace_append hprefix tailTrace_805666
  have hstable : (prefixWord ++ tailWord_805666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805666).length < 2 ^ (prefixWord ++ tailWord_805666).sum := by decide
  have hdescent : baseEnd_805666 < baseStart_805666 := by decide
  rcases family_descends (prefixWord ++ tailWord_805666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805700 : List Nat := [2, 3, 4, 2, 1, 1, 2, 2, 5]
def baseStart_805700 : Nat := 118140960795 + 805700 * 2 ^ 59
def prefixEnd_805700 : Nat := 4983230072969 + 3 ^ 40 * 805700 * 2
def baseEnd_805700 : Nat := 91935858517245095276591

theorem tailTrace_805700 : CollatzResearch.WordTrace tailWord_805700 prefixEnd_805700 91935858517245095276591 := by
  unfold tailWord_805700
  simp only [CollatzResearch.WordTrace]
  refine ⟨14693146590546988725003277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19590862120729318300004369 14693146590546988725003277)
  ·
    refine ⟨5509929971455120771876229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14693146590546988725003277 5509929971455120771876229)
    ·
      refine ⟨1033111869647835144726793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5509929971455120771876229 1033111869647835144726793)
      ·
        refine ⟨774833902235876358545095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1033111869647835144726793 774833902235876358545095)
        ·
          refine ⟨1162250853353814537817643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 774833902235876358545095 1162250853353814537817643)
          ·
            refine ⟨1743376280030721806726465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1162250853353814537817643 1743376280030721806726465)
            ·
              refine ⟨1307532210023041355044849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1743376280030721806726465 1307532210023041355044849)
              ·
                refine ⟨980649157517281016283637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1307532210023041355044849 980649157517281016283637)
                ·
                  refine ⟨91935858517245095276591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 980649157517281016283637 91935858517245095276591)
                  ·
                    rfl

theorem cell22_805700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 2, 5].length) (baseStart_805700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_805700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_805700 prefixEnd_805700 := by exact prefixLift 805700
  have htrace : WordTrace (prefixWord ++ tailWord_805700) baseStart_805700 baseEnd_805700 := by
    simpa [prefixWord, tailWord_805700, baseEnd_805700] using wordTrace_append hprefix tailTrace_805700
  have hstable : (prefixWord ++ tailWord_805700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805700).length < 2 ^ (prefixWord ++ tailWord_805700).sum := by decide
  have hdescent : baseEnd_805700 < baseStart_805700 := by decide
  rcases family_descends (prefixWord ++ tailWord_805700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805771 : List Nat := [1, 1, 1, 1, 4, 2, 3, 3, 3, 3]
def baseStart_805771 : Nat := 118140960795 + 805771 * 2 ^ 59
def prefixEnd_805771 : Nat := 4983230072969 + 3 ^ 40 * 805771 * 2
def baseEnd_805771 : Nat := 275831880302714767304555

theorem tailTrace_805771 : CollatzResearch.WordTrace tailWord_805771 prefixEnd_805771 275831880302714767304555 := by
  unfold tailWord_805771
  simp only [CollatzResearch.WordTrace]
  refine ⟨29388882763836756575841167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19592588509224504383894111 29388882763836756575841167)
  ·
    refine ⟨44083324145755134863761751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29388882763836756575841167 44083324145755134863761751)
    ·
      refine ⟨66124986218632702295642627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44083324145755134863761751 66124986218632702295642627)
      ·
        refine ⟨99187479327949053443463941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66124986218632702295642627 99187479327949053443463941)
        ·
          refine ⟨18597652373990447520649489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99187479327949053443463941 18597652373990447520649489)
          ·
            refine ⟨13948239280492835640487117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18597652373990447520649489 13948239280492835640487117)
            ·
              refine ⟨5230589730184813365182669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13948239280492835640487117 5230589730184813365182669)
              ·
                refine ⟨1961471148819305011943501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5230589730184813365182669 1961471148819305011943501)
                ·
                  refine ⟨735551680807239379478813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1961471148819305011943501 735551680807239379478813)
                  ·
                    refine ⟨275831880302714767304555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 735551680807239379478813 275831880302714767304555)
                    ·
                      rfl

theorem cell22_805771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 3, 3, 3].length) (baseStart_805771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_805771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_805771 prefixEnd_805771 := by exact prefixLift 805771
  have htrace : WordTrace (prefixWord ++ tailWord_805771) baseStart_805771 baseEnd_805771 := by
    simpa [prefixWord, tailWord_805771, baseEnd_805771] using wordTrace_append hprefix tailTrace_805771
  have hstable : (prefixWord ++ tailWord_805771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805771).length < 2 ^ (prefixWord ++ tailWord_805771).sum := by decide
  have hdescent : baseEnd_805771 < baseStart_805771 := by decide
  rcases family_descends (prefixWord ++ tailWord_805771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805822 : List Nat := [4, 2, 1, 1, 1, 2, 5, 2, 1, 3]
def baseStart_805822 : Nat := 118140960795 + 805822 * 2 ^ 59
def prefixEnd_805822 : Nat := 4983230072969 + 3 ^ 40 * 805822 * 2
def baseEnd_805822 : Nat := 275849338644967634279399

theorem tailTrace_805822 : CollatzResearch.WordTrace tailWord_805822 prefixEnd_805822 275849338644967634279399 := by
  unfold tailWord_805822
  simp only [CollatzResearch.WordTrace]
  refine ⟨3673842860831499035743465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19593828591101328190631813 3673842860831499035743465)
  ·
    refine ⟨2755382145623624276807599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3673842860831499035743465 2755382145623624276807599)
    ·
      refine ⟨4133073218435436415211399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2755382145623624276807599 4133073218435436415211399)
      ·
        refine ⟨6199609827653154622817099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4133073218435436415211399 6199609827653154622817099)
        ·
          refine ⟨9299414741479731934225649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6199609827653154622817099 9299414741479731934225649)
          ·
            refine ⟨6974561056109798950669237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9299414741479731934225649 6974561056109798950669237)
            ·
              refine ⟨653865099010293651625241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6974561056109798950669237 653865099010293651625241)
              ·
                refine ⟨490398824257720238718931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 653865099010293651625241 490398824257720238718931)
                ·
                  refine ⟨735598236386580358078397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 490398824257720238718931 735598236386580358078397)
                  ·
                    refine ⟨275849338644967634279399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 735598236386580358078397 275849338644967634279399)
                    ·
                      rfl

theorem cell22_805822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 5, 2, 1, 3].length) (baseStart_805822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_805822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_805822 prefixEnd_805822 := by exact prefixLift 805822
  have htrace : WordTrace (prefixWord ++ tailWord_805822) baseStart_805822 baseEnd_805822 := by
    simpa [prefixWord, tailWord_805822, baseEnd_805822] using wordTrace_append hprefix tailTrace_805822
  have hstable : (prefixWord ++ tailWord_805822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805822).length < 2 ^ (prefixWord ++ tailWord_805822).sum := by decide
  have hdescent : baseEnd_805822 < baseStart_805822 := by decide
  rcases family_descends (prefixWord ++ tailWord_805822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805848 : List Nat := [2, 1, 2, 2, 2, 3, 3, 2, 1, 4]
def baseStart_805848 : Nat := 118140960795 + 805848 * 2 ^ 59
def prefixEnd_805848 : Nat := 4983230072969 + 3 ^ 40 * 805848 * 2
def baseEnd_805848 : Nat := 275858238976312233129319

theorem tailTrace_805848 : CollatzResearch.WordTrace tailWord_805848 prefixEnd_805848 275858238976312233129319 := by
  unfold tailWord_805848
  simp only [CollatzResearch.WordTrace]
  refine ⟨14695845592278899363197099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19594460789705199150929465 14695845592278899363197099)
  ·
    refine ⟨22043768388418349044795649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14695845592278899363197099 22043768388418349044795649)
    ·
      refine ⟨16532826291313761783596737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22043768388418349044795649 16532826291313761783596737)
      ·
        refine ⟨12399619718485321337697553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16532826291313761783596737 12399619718485321337697553)
        ·
          refine ⟨9299714788863991003273165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12399619718485321337697553 9299714788863991003273165)
          ·
            refine ⟨3487393045823996626227437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9299714788863991003273165 3487393045823996626227437)
            ·
              refine ⟨1307772392183998734835289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3487393045823996626227437 1307772392183998734835289)
              ·
                refine ⟨980829294137999051126467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1307772392183998734835289 980829294137999051126467)
                ·
                  refine ⟨1471243941206998576689701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 980829294137999051126467 1471243941206998576689701)
                  ·
                    refine ⟨275858238976312233129319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1471243941206998576689701 275858238976312233129319)
                    ·
                      rfl

theorem cell22_805848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 2, 1, 4].length) (baseStart_805848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_805848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_805848 prefixEnd_805848 := by exact prefixLift 805848
  have htrace : WordTrace (prefixWord ++ tailWord_805848) baseStart_805848 baseEnd_805848 := by
    simpa [prefixWord, tailWord_805848, baseEnd_805848] using wordTrace_append hprefix tailTrace_805848
  have hstable : (prefixWord ++ tailWord_805848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805848).length < 2 ^ (prefixWord ++ tailWord_805848).sum := by decide
  have hdescent : baseEnd_805848 < baseStart_805848 := by decide
  rcases family_descends (prefixWord ++ tailWord_805848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805936 : List Nat := [2, 1, 1, 1, 2, 4, 3, 1, 7]
def baseStart_805936 : Nat := 118140960795 + 805936 * 2 ^ 59
def prefixEnd_805936 : Nat := 4983230072969 + 3 ^ 40 * 805936 * 2
def baseEnd_805936 : Nat := 91962787724903112309683

theorem tailTrace_805936 : CollatzResearch.WordTrace tailWord_805936 prefixEnd_805936 91962787724903112309683 := by
  unfold tailWord_805936
  simp only [CollatzResearch.WordTrace]
  refine ⟨14697450404119494877798831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19596600538825993170398441 14697450404119494877798831)
  ·
    refine ⟨22046175606179242316698247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14697450404119494877798831 22046175606179242316698247)
    ·
      refine ⟨33069263409268863475047371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22046175606179242316698247 33069263409268863475047371)
      ·
        refine ⟨49603895113903295212571057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33069263409268863475047371 49603895113903295212571057)
        ·
          refine ⟨37202921335427471409428293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49603895113903295212571057 37202921335427471409428293)
          ·
            refine ⟨6975547750392650889267805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37202921335427471409428293 6975547750392650889267805)
            ·
              refine ⟨2615830406397244083475427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6975547750392650889267805 2615830406397244083475427)
              ·
                refine ⟨3923745609595866125213141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2615830406397244083475427 3923745609595866125213141)
                ·
                  refine ⟨91962787724903112309683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3923745609595866125213141 91962787724903112309683)
                  ·
                    rfl

theorem cell22_805936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 1, 7].length) (baseStart_805936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_805936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_805936 prefixEnd_805936 := by exact prefixLift 805936
  have htrace : WordTrace (prefixWord ++ tailWord_805936) baseStart_805936 baseEnd_805936 := by
    simpa [prefixWord, tailWord_805936, baseEnd_805936] using wordTrace_append hprefix tailTrace_805936
  have hstable : (prefixWord ++ tailWord_805936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805936).length < 2 ^ (prefixWord ++ tailWord_805936).sum := by decide
  have hdescent : baseEnd_805936 < baseStart_805936 := by decide
  rcases family_descends (prefixWord ++ tailWord_805936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805983 : List Nat := [1, 1, 2, 3, 1, 1, 3, 5, 1, 4]
def baseStart_805983 : Nat := 118140960795 + 805983 * 2 ^ 59
def prefixEnd_805983 : Nat := 4983230072969 + 3 ^ 40 * 805983 * 2
def baseEnd_805983 : Nat := 275904452235216881003905

theorem tailTrace_805983 : CollatzResearch.WordTrace tailWord_805983 prefixEnd_805983 275904452235216881003905 := by
  unfold tailWord_805983
  simp only [CollatzResearch.WordTrace]
  refine ⟨29396615039068716782558603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19597743359379144521705735 29396615039068716782558603)
  ·
    refine ⟨44094922558603075173837905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29396615039068716782558603 44094922558603075173837905)
    ·
      refine ⟨33071191918952306380378429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44094922558603075173837905 33071191918952306380378429)
      ·
        refine ⟨12401696969607114892641911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33071191918952306380378429 12401696969607114892641911)
        ·
          refine ⟨18602545454410672338962867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12401696969607114892641911 18602545454410672338962867)
          ·
            refine ⟨27903818181616008508444301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18602545454410672338962867 27903818181616008508444301)
            ·
              refine ⟨10463931818106003190666613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27903818181616008508444301 10463931818106003190666613)
              ·
                refine ⟨980993607947437799124995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10463931818106003190666613 980993607947437799124995)
                ·
                  refine ⟨1471490411921156698687493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 980993607947437799124995 1471490411921156698687493)
                  ·
                    refine ⟨275904452235216881003905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1471490411921156698687493 275904452235216881003905)
                    ·
                      rfl

theorem cell22_805983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 5, 1, 4].length) (baseStart_805983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_805983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_805983 prefixEnd_805983 := by exact prefixLift 805983
  have htrace : WordTrace (prefixWord ++ tailWord_805983) baseStart_805983 baseEnd_805983 := by
    simpa [prefixWord, tailWord_805983, baseEnd_805983] using wordTrace_append hprefix tailTrace_805983
  have hstable : (prefixWord ++ tailWord_805983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805983).length < 2 ^ (prefixWord ++ tailWord_805983).sum := by decide
  have hdescent : baseEnd_805983 < baseStart_805983 := by decide
  rcases family_descends (prefixWord ++ tailWord_805983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806011 : List Nat := [1, 1, 1, 1, 1, 4, 1, 3, 3, 6]
def baseStart_806011 : Nat := 118140960795 + 806011 * 2 ^ 59
def prefixEnd_806011 : Nat := 4983230072969 + 3 ^ 40 * 806011 * 2
def baseEnd_806011 : Nat := 275914037207434141303819

theorem tailTrace_806011 : CollatzResearch.WordTrace tailWord_806011 prefixEnd_806011 275914037207434141303819 := by
  unfold tailWord_806011
  simp only [CollatzResearch.WordTrace]
  refine ⟨29397636282967277564577887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19598424188644851709718591 29397636282967277564577887)
  ·
    refine ⟨44096454424450916346866831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29397636282967277564577887 44096454424450916346866831)
    ·
      refine ⟨66144681636676374520300247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44096454424450916346866831 66144681636676374520300247)
      ·
        refine ⟨99217022455014561780450371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66144681636676374520300247 99217022455014561780450371)
        ·
          refine ⟨148825533682521842670675557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99217022455014561780450371 148825533682521842670675557)
          ·
            refine ⟨27904787565472845500751667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 148825533682521842670675557 27904787565472845500751667)
            ·
              refine ⟨41857181348209268251127501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27904787565472845500751667 41857181348209268251127501)
              ·
                refine ⟨15696443005578475594172813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41857181348209268251127501 15696443005578475594172813)
                ·
                  refine ⟨5886166127091928347814805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15696443005578475594172813 5886166127091928347814805)
                  ·
                    refine ⟨275914037207434141303819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5886166127091928347814805 275914037207434141303819)
                    ·
                      rfl

theorem cell22_806011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3, 6].length) (baseStart_806011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_806011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_806011 prefixEnd_806011 := by exact prefixLift 806011
  have htrace : WordTrace (prefixWord ++ tailWord_806011) baseStart_806011 baseEnd_806011 := by
    simpa [prefixWord, tailWord_806011, baseEnd_806011] using wordTrace_append hprefix tailTrace_806011
  have hstable : (prefixWord ++ tailWord_806011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806011).length < 2 ^ (prefixWord ++ tailWord_806011).sum := by decide
  have hdescent : baseEnd_806011 < baseStart_806011 := by decide
  rcases family_descends (prefixWord ++ tailWord_806011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806013 : List Nat := [1, 4, 1, 1, 3, 1, 2, 3, 1, 5]
def baseStart_806013 : Nat := 118140960795 + 806013 * 2 ^ 59
def prefixEnd_806013 : Nat := 4983230072969 + 3 ^ 40 * 806013 * 2
def baseEnd_806013 : Nat := 275914721848306802753813

theorem tailTrace_806013 : CollatzResearch.WordTrace tailWord_806013 prefixEnd_806013 275914721848306802753813 := by
  unfold tailWord_806013
  simp only [CollatzResearch.WordTrace]
  refine ⟨29397709228960031906150693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19598472819306687937433795 29397709228960031906150693)
  ·
    refine ⟨5512070480430005982403255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29397709228960031906150693 5512070480430005982403255)
    ·
      refine ⟨8268105720645008973604883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5512070480430005982403255 8268105720645008973604883)
      ·
        refine ⟨12402158580967513460407325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8268105720645008973604883 12402158580967513460407325)
        ·
          refine ⟨4650809467862817547652747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12402158580967513460407325 4650809467862817547652747)
          ·
            refine ⟨6976214201794226321479121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4650809467862817547652747 6976214201794226321479121)
            ·
              refine ⟨5232160651345669741109341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6976214201794226321479121 5232160651345669741109341)
              ·
                refine ⟨1962060244254626152916003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5232160651345669741109341 1962060244254626152916003)
                ·
                  refine ⟨2943090366381939229374005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1962060244254626152916003 2943090366381939229374005)
                  ·
                    refine ⟨275914721848306802753813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2943090366381939229374005 275914721848306802753813)
                    ·
                      rfl

theorem cell22_806013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 3, 1, 5].length) (baseStart_806013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_806013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_806013 prefixEnd_806013 := by exact prefixLift 806013
  have htrace : WordTrace (prefixWord ++ tailWord_806013) baseStart_806013 baseEnd_806013 := by
    simpa [prefixWord, tailWord_806013, baseEnd_806013] using wordTrace_append hprefix tailTrace_806013
  have hstable : (prefixWord ++ tailWord_806013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806013).length < 2 ^ (prefixWord ++ tailWord_806013).sum := by decide
  have hdescent : baseEnd_806013 < baseStart_806013 := by decide
  rcases family_descends (prefixWord ++ tailWord_806013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806017 : List Nat := [1, 2, 4, 2, 2, 3, 1, 2, 1, 4]
def baseStart_806017 : Nat := 118140960795 + 806017 * 2 ^ 59
def prefixEnd_806017 : Nat := 4983230072969 + 3 ^ 40 * 806017 * 2
def baseEnd_806017 : Nat := 275916091130052125653801

theorem tailTrace_806017 : CollatzResearch.WordTrace tailWord_806017 prefixEnd_806017 275916091130052125653801 := by
  unfold tailWord_806017
  simp only [CollatzResearch.WordTrace]
  refine ⟨29397855120945540589296305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19598570080630360392864203 29397855120945540589296305)
  ·
    refine ⟨22048391340709155441972229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29397855120945540589296305 22048391340709155441972229)
    ·
      refine ⟨4134073376382966645369793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22048391340709155441972229 4134073376382966645369793)
      ·
        refine ⟨3100555032287224984027345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4134073376382966645369793 3100555032287224984027345)
        ·
          refine ⟨2325416274215418738020509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3100555032287224984027345 2325416274215418738020509)
          ·
            refine ⟨872031102830782026757691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2325416274215418738020509 872031102830782026757691)
            ·
              refine ⟨1308046654246173040136537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 872031102830782026757691 1308046654246173040136537)
              ·
                refine ⟨981034990684629780102403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1308046654246173040136537 981034990684629780102403)
                ·
                  refine ⟨1471552486026944670153605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 981034990684629780102403 1471552486026944670153605)
                  ·
                    refine ⟨275916091130052125653801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1471552486026944670153605 275916091130052125653801)
                    ·
                      rfl

theorem cell22_806017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 2, 1, 4].length) (baseStart_806017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_806017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_806017 prefixEnd_806017 := by exact prefixLift 806017
  have htrace : WordTrace (prefixWord ++ tailWord_806017) baseStart_806017 baseEnd_806017 := by
    simpa [prefixWord, tailWord_806017, baseEnd_806017] using wordTrace_append hprefix tailTrace_806017
  have hstable : (prefixWord ++ tailWord_806017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806017).length < 2 ^ (prefixWord ++ tailWord_806017).sum := by decide
  have hdescent : baseEnd_806017 < baseStart_806017 := by decide
  rcases family_descends (prefixWord ++ tailWord_806017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806030 : List Nat := [4, 1, 1, 3, 2, 2, 1, 2, 1, 5]
def baseStart_806030 : Nat := 118140960795 + 806030 * 2 ^ 59
def prefixEnd_806030 : Nat := 4983230072969 + 3 ^ 40 * 806030 * 2
def baseEnd_806030 : Nat := 275920541295724425078761

theorem tailTrace_806030 : CollatzResearch.WordTrace tailWord_806030 prefixEnd_806030 275920541295724425078761 := by
  unfold tailWord_806030
  simp only [CollatzResearch.WordTrace]
  refine ⟨3674791158737305476189943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19598886179932295873013029 3674791158737305476189943)
  ·
    refine ⟨5512186738105958214284915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3674791158737305476189943 5512186738105958214284915)
    ·
      refine ⟨8268280107158937321427373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5512186738105958214284915 8268280107158937321427373)
      ·
        refine ⟨3100605040184601495535265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8268280107158937321427373 3100605040184601495535265)
        ·
          refine ⟨2325453780138451121651449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3100605040184601495535265 2325453780138451121651449)
          ·
            refine ⟨1744090335103838341238587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2325453780138451121651449 1744090335103838341238587)
            ·
              refine ⟨2616135502655757511857881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1744090335103838341238587 2616135502655757511857881)
              ·
                refine ⟨1962101626991818133893411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2616135502655757511857881 1962101626991818133893411)
                ·
                  refine ⟨2943152440487727200840117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1962101626991818133893411 2943152440487727200840117)
                  ·
                    refine ⟨275920541295724425078761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2943152440487727200840117 275920541295724425078761)
                    ·
                      rfl

theorem cell22_806030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 2, 1, 5].length) (baseStart_806030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_806030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_806030 prefixEnd_806030 := by exact prefixLift 806030
  have htrace : WordTrace (prefixWord ++ tailWord_806030) baseStart_806030 baseEnd_806030 := by
    simpa [prefixWord, tailWord_806030, baseEnd_806030] using wordTrace_append hprefix tailTrace_806030
  have hstable : (prefixWord ++ tailWord_806030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806030).length < 2 ^ (prefixWord ++ tailWord_806030).sum := by decide
  have hdescent : baseEnd_806030 < baseStart_806030 := by decide
  rcases family_descends (prefixWord ++ tailWord_806030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806103 : List Nat := [1, 1, 3, 2, 1, 2, 3, 2, 2, 5]
def baseStart_806103 : Nat := 118140960795 + 806103 * 2 ^ 59
def prefixEnd_806103 : Nat := 4983230072969 + 3 ^ 40 * 806103 * 2
def baseEnd_806103 : Nat := 275945530687576568003537

theorem tailTrace_806103 : CollatzResearch.WordTrace tailWord_806103 prefixEnd_806103 275945530687576568003537 := by
  unfold tailWord_806103
  simp only [CollatzResearch.WordTrace]
  refine ⟨29400991798633977276926963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19600661199089318184617975 29400991798633977276926963)
  ·
    refine ⟨44101487697950965915390445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29400991798633977276926963 44101487697950965915390445)
    ·
      refine ⟨16538057886731612218271417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44101487697950965915390445 16538057886731612218271417)
      ·
        refine ⟨12403543415048709163703563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16538057886731612218271417 12403543415048709163703563)
        ·
          refine ⟨18605315122573063745555345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12403543415048709163703563 18605315122573063745555345)
          ·
            refine ⟨13953986341929797809166509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18605315122573063745555345 13953986341929797809166509)
            ·
              refine ⟨5232744878223674178437441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13953986341929797809166509 5232744878223674178437441)
              ·
                refine ⟨3924558658667755633828081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5232744878223674178437441 3924558658667755633828081)
                ·
                  refine ⟨2943418994000816725371061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3924558658667755633828081 2943418994000816725371061)
                  ·
                    refine ⟨275945530687576568003537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2943418994000816725371061 275945530687576568003537)
                    ·
                      rfl

theorem cell22_806103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2, 2, 5].length) (baseStart_806103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_806103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_806103 prefixEnd_806103 := by exact prefixLift 806103
  have htrace : WordTrace (prefixWord ++ tailWord_806103) baseStart_806103 baseEnd_806103 := by
    simpa [prefixWord, tailWord_806103, baseEnd_806103] using wordTrace_append hprefix tailTrace_806103
  have hstable : (prefixWord ++ tailWord_806103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806103).length < 2 ^ (prefixWord ++ tailWord_806103).sum := by decide
  have hdescent : baseEnd_806103 < baseStart_806103 := by decide
  rcases family_descends (prefixWord ++ tailWord_806103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806109 : List Nat := [1, 4, 3, 2, 2, 1, 2, 1, 3, 3]
def baseStart_806109 : Nat := 118140960795 + 806109 * 2 ^ 59
def prefixEnd_806109 : Nat := 4983230072969 + 3 ^ 40 * 806109 * 2
def baseEnd_806109 : Nat := 275947584610194552353519

theorem tailTrace_806109 : CollatzResearch.WordTrace tailWord_806109 prefixEnd_806109 275947584610194552353519 := by
  unfold tailWord_806109
  simp only [CollatzResearch.WordTrace]
  refine ⟨29401210636612240301645381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19600807091074826867763587 29401210636612240301645381)
  ·
    refine ⟨5512726994364795056558509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29401210636612240301645381 5512726994364795056558509)
    ·
      refine ⟨2067272622886798146209441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5512726994364795056558509 2067272622886798146209441)
      ·
        refine ⟨1550454467165098609657081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2067272622886798146209441 1550454467165098609657081)
        ·
          refine ⟨1162840850373823957242811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1550454467165098609657081 1162840850373823957242811)
          ·
            refine ⟨1744261275560735935864217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1162840850373823957242811 1744261275560735935864217)
            ·
              refine ⟨1308195956670551951898163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1744261275560735935864217 1308195956670551951898163)
              ·
                refine ⟨1962293935005827927847245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1308195956670551951898163 1962293935005827927847245)
                ·
                  refine ⟨735860225627185472942717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1962293935005827927847245 735860225627185472942717)
                  ·
                    refine ⟨275947584610194552353519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 735860225627185472942717 275947584610194552353519)
                    ·
                      rfl

theorem cell22_806109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_806109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_806109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_806109 prefixEnd_806109 := by exact prefixLift 806109
  have htrace : WordTrace (prefixWord ++ tailWord_806109) baseStart_806109 baseEnd_806109 := by
    simpa [prefixWord, tailWord_806109, baseEnd_806109] using wordTrace_append hprefix tailTrace_806109
  have hstable : (prefixWord ++ tailWord_806109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806109).length < 2 ^ (prefixWord ++ tailWord_806109).sum := by decide
  have hdescent : baseEnd_806109 < baseStart_806109 := by decide
  rcases family_descends (prefixWord ++ tailWord_806109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806122 : List Nat := [3, 1, 3, 1, 1, 4, 3, 1, 5]
def baseStart_806122 : Nat := 118140960795 + 806122 * 2 ^ 59
def prefixEnd_806122 : Nat := 4983230072969 + 3 ^ 40 * 806122 * 2
def baseEnd_806122 : Nat := 91984011591955617259493

theorem tailTrace_806122 : CollatzResearch.WordTrace tailWord_806122 prefixEnd_806122 91984011591955617259493 := by
  unfold tailWord_806122
  simp only [CollatzResearch.WordTrace]
  refine ⟨7350421196391285880467155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19601123190376762347912413 7350421196391285880467155)
  ·
    refine ⟨11025631794586928820700733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7350421196391285880467155 11025631794586928820700733)
    ·
      refine ⟨4134611922970098307762775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11025631794586928820700733 4134611922970098307762775)
      ·
        refine ⟨6201917884455147461644163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4134611922970098307762775 6201917884455147461644163)
        ·
          refine ⟨9302876826682721192466245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6201917884455147461644163 9302876826682721192466245)
          ·
            refine ⟨1744289405003010223587421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9302876826682721192466245 1744289405003010223587421)
            ·
              refine ⟨654108526876128833845283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1744289405003010223587421 654108526876128833845283)
              ·
                refine ⟨981162790314193250767925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 654108526876128833845283 981162790314193250767925)
                ·
                  refine ⟨91984011591955617259493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 981162790314193250767925 91984011591955617259493)
                  ·
                    rfl

theorem cell22_806122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 3, 1, 5].length) (baseStart_806122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_806122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_806122 prefixEnd_806122 := by exact prefixLift 806122
  have htrace : WordTrace (prefixWord ++ tailWord_806122) baseStart_806122 baseEnd_806122 := by
    simpa [prefixWord, tailWord_806122, baseEnd_806122] using wordTrace_append hprefix tailTrace_806122
  have hstable : (prefixWord ++ tailWord_806122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806122).length < 2 ^ (prefixWord ++ tailWord_806122).sum := by decide
  have hdescent : baseEnd_806122 < baseStart_806122 := by decide
  rcases family_descends (prefixWord ++ tailWord_806122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806180 : List Nat := [2, 3, 1, 3, 1, 1, 1, 2, 4, 4]
def baseStart_806180 : Nat := 118140960795 + 806180 * 2 ^ 59
def prefixEnd_806180 : Nat := 4983230072969 + 3 ^ 40 * 806180 * 2
def baseEnd_806180 : Nat := 275971889361174033828301

theorem tailTrace_806180 : CollatzResearch.WordTrace tailWord_806180 prefixEnd_806180 275971889361174033828301 := by
  unfold tailWord_806180
  simp only [CollatzResearch.WordTrace]
  refine ⟨14701900109677509713739997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19602533479570012951653329 14701900109677509713739997)
  ·
    refine ⟨5513212541129066142652499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14701900109677509713739997 5513212541129066142652499)
    ·
      refine ⟨8269818811693599213978749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5513212541129066142652499 8269818811693599213978749)
      ·
        refine ⟨3101182054385099705242031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8269818811693599213978749 3101182054385099705242031)
        ·
          refine ⟨4651773081577649557863047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3101182054385099705242031 4651773081577649557863047)
          ·
            refine ⟨6977659622366474336794571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4651773081577649557863047 6977659622366474336794571)
            ·
              refine ⟨10466489433549711505191857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6977659622366474336794571 10466489433549711505191857)
              ·
                refine ⟨7849867075162283628893893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10466489433549711505191857 7849867075162283628893893)
                ·
                  refine ⟨1471850076592928180417605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7849867075162283628893893 1471850076592928180417605)
                  ·
                    refine ⟨275971889361174033828301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1471850076592928180417605 275971889361174033828301)
                    ·
                      rfl

theorem cell22_806180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 2, 4, 4].length) (baseStart_806180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_806180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_806180 prefixEnd_806180 := by exact prefixLift 806180
  have htrace : WordTrace (prefixWord ++ tailWord_806180) baseStart_806180 baseEnd_806180 := by
    simpa [prefixWord, tailWord_806180, baseEnd_806180] using wordTrace_append hprefix tailTrace_806180
  have hstable : (prefixWord ++ tailWord_806180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806180).length < 2 ^ (prefixWord ++ tailWord_806180).sum := by decide
  have hdescent : baseEnd_806180 < baseStart_806180 := by decide
  rcases family_descends (prefixWord ++ tailWord_806180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806197 : List Nat := [1, 3, 3, 1, 2, 3, 2, 1, 2, 4]
def baseStart_806197 : Nat := 118140960795 + 806197 * 2 ^ 59
def prefixEnd_806197 : Nat := 4983230072969 + 3 ^ 40 * 806197 * 2
def baseEnd_806197 : Nat := 275977708808591656153249

theorem tailTrace_806197 : CollatzResearch.WordTrace tailWord_806197 prefixEnd_806197 275977708808591656153249 := by
  unfold tailWord_806197
  simp only [CollatzResearch.WordTrace]
  refine ⟨29404420260293431330848845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19602946840195620887232563 29404420260293431330848845)
  ·
    refine ⟨11026657597610036749068317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29404420260293431330848845 11026657597610036749068317)
    ·
      refine ⟨4134996599103763780900619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11026657597610036749068317 4134996599103763780900619)
      ·
        refine ⟨6202494898655645671350929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4134996599103763780900619 6202494898655645671350929)
        ·
          refine ⟨4651871173991734253513197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6202494898655645671350929 4651871173991734253513197)
          ·
            refine ⟨1744451690246900345067449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4651871173991734253513197 1744451690246900345067449)
            ·
              refine ⟨1308338767685175258800587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1744451690246900345067449 1308338767685175258800587)
              ·
                refine ⟨1962508151527762888200881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1308338767685175258800587 1962508151527762888200881)
                ·
                  refine ⟨1471881113645822166150661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1962508151527762888200881 1471881113645822166150661)
                  ·
                    refine ⟨275977708808591656153249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1471881113645822166150661 275977708808591656153249)
                    ·
                      rfl

theorem cell22_806197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_806197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_806197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_806197 prefixEnd_806197 := by exact prefixLift 806197
  have htrace : WordTrace (prefixWord ++ tailWord_806197) baseStart_806197 baseEnd_806197 := by
    simpa [prefixWord, tailWord_806197, baseEnd_806197] using wordTrace_append hprefix tailTrace_806197
  have hstable : (prefixWord ++ tailWord_806197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806197).length < 2 ^ (prefixWord ++ tailWord_806197).sum := by decide
  have hdescent : baseEnd_806197 < baseStart_806197 := by decide
  rcases family_descends (prefixWord ++ tailWord_806197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806223 : List Nat := [1, 1, 2, 1, 1, 2, 1, 2, 11]
def baseStart_806223 : Nat := 118140960795 + 806223 * 2 ^ 59
def prefixEnd_806223 : Nat := 4983230072969 + 3 ^ 40 * 806223 * 2
def baseEnd_806223 : Nat := 91995536379978751667723

theorem tailTrace_806223 : CollatzResearch.WordTrace tailWord_806223 prefixEnd_806223 91995536379978751667723 := by
  unfold tailWord_806223
  simp only [CollatzResearch.WordTrace]
  refine ⟨29405368558199237771295323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19603579038799491847530215 29405368558199237771295323)
  ·
    refine ⟨44108052837298856656942985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29405368558199237771295323 44108052837298856656942985)
    ·
      refine ⟨33081039627974142492707239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44108052837298856656942985 33081039627974142492707239)
      ·
        refine ⟨49621559441961213739060859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33081039627974142492707239 49621559441961213739060859)
        ·
          refine ⟨74432339162941820608591289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49621559441961213739060859 74432339162941820608591289)
          ·
            refine ⟨55824254372206365456443467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74432339162941820608591289 55824254372206365456443467)
            ·
              refine ⟨83736381558309548184665201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55824254372206365456443467 83736381558309548184665201)
              ·
                refine ⟨62802286168732161138498901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83736381558309548184665201 62802286168732161138498901)
                ·
                  refine ⟨91995536379978751667723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 62802286168732161138498901 91995536379978751667723)
                  ·
                    rfl

theorem cell22_806223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 11].length) (baseStart_806223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_806223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_806223 prefixEnd_806223 := by exact prefixLift 806223
  have htrace : WordTrace (prefixWord ++ tailWord_806223) baseStart_806223 baseEnd_806223 := by
    simpa [prefixWord, tailWord_806223, baseEnd_806223] using wordTrace_append hprefix tailTrace_806223
  have hstable : (prefixWord ++ tailWord_806223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806223).length < 2 ^ (prefixWord ++ tailWord_806223).sum := by decide
  have hdescent : baseEnd_806223 < baseStart_806223 := by decide
  rcases family_descends (prefixWord ++ tailWord_806223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806274 : List Nat := [3, 4, 2, 1, 1, 2, 1, 1, 7]
def baseStart_806274 : Nat := 118140960795 + 806274 * 2 ^ 59
def prefixEnd_806274 : Nat := 4983230072969 + 3 ^ 40 * 806274 * 2
def baseEnd_806274 : Nat := 92001355827396373992671

theorem tailTrace_806274 : CollatzResearch.WordTrace tailWord_806274 prefixEnd_806274 92001355827396373992671 := by
  unfold tailWord_806274
  simp only [CollatzResearch.WordTrace]
  refine ⟨7351807170253618370350469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19604819120676315654267917 7351807170253618370350469)
  ·
    refine ⟨1378463844422553444440713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7351807170253618370350469 1378463844422553444440713)
    ·
      refine ⟨1033847883316915083330535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1378463844422553444440713 1033847883316915083330535)
      ·
        refine ⟨1550771824975372624995803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1033847883316915083330535 1550771824975372624995803)
        ·
          refine ⟨2326157737463058937493705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1550771824975372624995803 2326157737463058937493705)
          ·
            refine ⟨1744618303097294203120279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2326157737463058937493705 1744618303097294203120279)
            ·
              refine ⟨2616927454645941304680419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1744618303097294203120279 2616927454645941304680419)
              ·
                refine ⟨3925391181968911957020629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2616927454645941304680419 3925391181968911957020629)
                ·
                  refine ⟨92001355827396373992671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3925391181968911957020629 92001355827396373992671)
                  ·
                    rfl

theorem cell22_806274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_806274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_806274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_806274 prefixEnd_806274 := by exact prefixLift 806274
  have htrace : WordTrace (prefixWord ++ tailWord_806274) baseStart_806274 baseEnd_806274 := by
    simpa [prefixWord, tailWord_806274, baseEnd_806274] using wordTrace_append hprefix tailTrace_806274
  have hstable : (prefixWord ++ tailWord_806274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806274).length < 2 ^ (prefixWord ++ tailWord_806274).sum := by decide
  have hdescent : baseEnd_806274 < baseStart_806274 := by decide
  rcases family_descends (prefixWord ++ tailWord_806274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806334 : List Nat := [4, 2, 1, 1, 1, 1, 1, 6, 2, 3]
def baseStart_806334 : Nat := 118140960795 + 806334 * 2 ^ 59
def prefixEnd_806334 : Nat := 4983230072969 + 3 ^ 40 * 806334 * 2
def baseEnd_806334 : Nat := 276024606708368965477829

theorem tailTrace_806334 : CollatzResearch.WordTrace tailWord_806334 prefixEnd_806334 276024606708368965477829 := by
  unfold tailWord_806334
  simp only [CollatzResearch.WordTrace]
  refine ⟨3676177132599637966073257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19606278040531402485724037 3676177132599637966073257)
  ·
    refine ⟨2757132849449728474554943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3676177132599637966073257 2757132849449728474554943)
    ·
      refine ⟨4135699274174592711832415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2757132849449728474554943 4135699274174592711832415)
      ·
        refine ⟨6203548911261889067748623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4135699274174592711832415 6203548911261889067748623)
        ·
          refine ⟨9305323366892833601622935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6203548911261889067748623 9305323366892833601622935)
          ·
            refine ⟨13957985050339250402434403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9305323366892833601622935 13957985050339250402434403)
            ·
              refine ⟨20936977575508875603651605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13957985050339250402434403 20936977575508875603651605)
              ·
                refine ⟨981420823851978543921169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20936977575508875603651605 981420823851978543921169)
                ·
                  refine ⟨736065617888983907940877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 981420823851978543921169 736065617888983907940877)
                  ·
                    refine ⟨276024606708368965477829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 736065617888983907940877 276024606708368965477829)
                    ·
                      rfl

theorem cell22_806334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 6, 2, 3].length) (baseStart_806334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_806334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_806334 prefixEnd_806334 := by exact prefixLift 806334
  have htrace : WordTrace (prefixWord ++ tailWord_806334) baseStart_806334 baseEnd_806334 := by
    simpa [prefixWord, tailWord_806334, baseEnd_806334] using wordTrace_append hprefix tailTrace_806334
  have hstable : (prefixWord ++ tailWord_806334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806334).length < 2 ^ (prefixWord ++ tailWord_806334).sum := by decide
  have hdescent : baseEnd_806334 < baseStart_806334 := by decide
  rcases family_descends (prefixWord ++ tailWord_806334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806392 : List Nat := [2, 1, 2, 1, 1, 5, 1, 4, 5]
def baseStart_806392 : Nat := 118140960795 + 806392 * 2 ^ 59
def prefixEnd_806392 : Nat := 4983230072969 + 3 ^ 40 * 806392 * 2
def baseEnd_806392 : Nat := 92014820431225382509217

theorem tailTrace_806392 : CollatzResearch.WordTrace tailWord_806392 prefixEnd_806392 92014820431225382509217 := by
  unfold tailWord_806392
  simp only [CollatzResearch.WordTrace]
  refine ⟨14705766247293489817098715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19607688329724653089464953 14705766247293489817098715)
  ·
    refine ⟨22058649370940234725648073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14705766247293489817098715 22058649370940234725648073)
    ·
      refine ⟨16543987028205176044236055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22058649370940234725648073 16543987028205176044236055)
      ·
        refine ⟨24815980542307764066354083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16543987028205176044236055 24815980542307764066354083)
        ·
          refine ⟨37223970813461646099531125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24815980542307764066354083 37223970813461646099531125)
          ·
            refine ⟨3489747263762029321831043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37223970813461646099531125 3489747263762029321831043)
            ·
              refine ⟨5234620895643043982746565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3489747263762029321831043 5234620895643043982746565)
              ·
                refine ⟨981491417933070746764981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5234620895643043982746565 981491417933070746764981)
                ·
                  refine ⟨92014820431225382509217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 981491417933070746764981 92014820431225382509217)
                  ·
                    rfl

theorem cell22_806392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 4, 5].length) (baseStart_806392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_806392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_806392 prefixEnd_806392 := by exact prefixLift 806392
  have htrace : WordTrace (prefixWord ++ tailWord_806392) baseStart_806392 baseEnd_806392 := by
    simpa [prefixWord, tailWord_806392, baseEnd_806392] using wordTrace_append hprefix tailTrace_806392
  have hstable : (prefixWord ++ tailWord_806392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806392).length < 2 ^ (prefixWord ++ tailWord_806392).sum := by decide
  have hdescent : baseEnd_806392 < baseStart_806392 := by decide
  rcases family_descends (prefixWord ++ tailWord_806392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806398 : List Nat := [4, 2, 2, 3, 2, 1, 1, 7]
def baseStart_806398 : Nat := 118140960795 + 806398 * 2 ^ 59
def prefixEnd_806398 : Nat := 4983230072969 + 3 ^ 40 * 806398 * 2
def baseEnd_806398 : Nat := 30671835024032681319737

theorem tailTrace_806398 : CollatzResearch.WordTrace tailWord_806398 prefixEnd_806398 30671835024032681319737 := by
  unfold tailWord_806398
  simp only [CollatzResearch.WordTrace]
  refine ⟨3676468916570655332364481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19607834221710161772610565 3676468916570655332364481)
  ·
    refine ⟨2757351687427991499273361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3676468916570655332364481 2757351687427991499273361)
    ·
      refine ⟨2068013765570993624455021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2757351687427991499273361 2068013765570993624455021)
      ·
        refine ⟨775505162089122609170633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2068013765570993624455021 775505162089122609170633)
        ·
          refine ⟨581628871566841956877975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 775505162089122609170633 581628871566841956877975)
          ·
            refine ⟨872443307350262935316963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 581628871566841956877975 872443307350262935316963)
            ·
              refine ⟨1308664961025394402975445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 872443307350262935316963 1308664961025394402975445)
              ·
                refine ⟨30671835024032681319737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1308664961025394402975445 30671835024032681319737)
                ·
                  rfl

theorem cell22_806398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 7].length) (baseStart_806398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_806398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_806398 prefixEnd_806398 := by exact prefixLift 806398
  have htrace : WordTrace (prefixWord ++ tailWord_806398) baseStart_806398 baseEnd_806398 := by
    simpa [prefixWord, tailWord_806398, baseEnd_806398] using wordTrace_append hprefix tailTrace_806398
  have hstable : (prefixWord ++ tailWord_806398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806398).length < 2 ^ (prefixWord ++ tailWord_806398).sum := by decide
  have hdescent : baseEnd_806398 < baseStart_806398 := by decide
  rcases family_descends (prefixWord ++ tailWord_806398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806407 : List Nat := [1, 1, 4, 3, 2, 1, 1, 1, 1, 7]
def baseStart_806407 : Nat := 118140960795 + 806407 * 2 ^ 59
def prefixEnd_806407 : Nat := 4983230072969 + 3 ^ 40 * 806407 * 2
def baseEnd_806407 : Nat := 276049596100221108402605

theorem tailTrace_806407 : CollatzResearch.WordTrace tailWord_806407 prefixEnd_806407 276049596100221108402605 := by
  unfold tailWord_806407
  simp only [CollatzResearch.WordTrace]
  refine ⟨29412079589532637195993475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19608053059688424797328983 29412079589532637195993475)
  ·
    refine ⟨44118119384298955793990213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29412079589532637195993475 44118119384298955793990213)
    ·
      refine ⟨8272147384556054211373165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44118119384298955793990213 8272147384556054211373165)
      ·
        refine ⟨3102055269208520329264937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8272147384556054211373165 3102055269208520329264937)
        ·
          refine ⟨2326541451906390246948703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3102055269208520329264937 2326541451906390246948703)
          ·
            refine ⟨3489812177859585370423055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2326541451906390246948703 3489812177859585370423055)
            ·
              refine ⟨5234718266789378055634583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3489812177859585370423055 5234718266789378055634583)
              ·
                refine ⟨7852077400184067083451875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5234718266789378055634583 7852077400184067083451875)
                ·
                  refine ⟨11778116100276100625177813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7852077400184067083451875 11778116100276100625177813)
                  ·
                    refine ⟨276049596100221108402605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11778116100276100625177813 276049596100221108402605)
                    ·
                      rfl

theorem cell22_806407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 7].length) (baseStart_806407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_806407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_806407 prefixEnd_806407 := by exact prefixLift 806407
  have htrace : WordTrace (prefixWord ++ tailWord_806407) baseStart_806407 baseEnd_806407 := by
    simpa [prefixWord, tailWord_806407, baseEnd_806407] using wordTrace_append hprefix tailTrace_806407
  have hstable : (prefixWord ++ tailWord_806407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806407).length < 2 ^ (prefixWord ++ tailWord_806407).sum := by decide
  have hdescent : baseEnd_806407 < baseStart_806407 := by decide
  rcases family_descends (prefixWord ++ tailWord_806407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806484 : List Nat := [2, 4, 1, 1, 1, 2, 2, 3, 2, 4]
def baseStart_806484 : Nat := 118140960795 + 806484 * 2 ^ 59
def prefixEnd_806484 : Nat := 4983230072969 + 3 ^ 40 * 806484 * 2
def baseEnd_806484 : Nat := 276075954773818574227369

theorem tailTrace_806484 : CollatzResearch.WordTrace tailWord_806484 prefixEnd_806484 276075954773818574227369 := by
  unfold tailWord_806484
  simp only [CollatzResearch.WordTrace]
  refine ⟨14707444005126839673273253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19609925340169119564364337 14707444005126839673273253)
  ·
    refine ⟨2757645750961282438738735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14707444005126839673273253 2757645750961282438738735)
    ·
      refine ⟨4136468626441923658108103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2757645750961282438738735 4136468626441923658108103)
      ·
        refine ⟨6204702939662885487162155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4136468626441923658108103 6204702939662885487162155)
        ·
          refine ⟨9307054409494328230743233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6204702939662885487162155 9307054409494328230743233)
          ·
            refine ⟨6980290807120746173057425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9307054409494328230743233 6980290807120746173057425)
            ·
              refine ⟨5235218105340559629793069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6980290807120746173057425 5235218105340559629793069)
              ·
                refine ⟨1963206789502709861172401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5235218105340559629793069 1963206789502709861172401)
                ·
                  refine ⟨1472405092127032395879301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1963206789502709861172401 1472405092127032395879301)
                  ·
                    refine ⟨276075954773818574227369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1472405092127032395879301 276075954773818574227369)
                    ·
                      rfl

theorem cell22_806484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_806484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_806484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_806484 prefixEnd_806484 := by exact prefixLift 806484
  have htrace : WordTrace (prefixWord ++ tailWord_806484) baseStart_806484 baseEnd_806484 := by
    simpa [prefixWord, tailWord_806484, baseEnd_806484] using wordTrace_append hprefix tailTrace_806484
  have hstable : (prefixWord ++ tailWord_806484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806484).length < 2 ^ (prefixWord ++ tailWord_806484).sum := by decide
  have hdescent : baseEnd_806484 < baseStart_806484 := by decide
  rcases family_descends (prefixWord ++ tailWord_806484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806561 : List Nat := [1, 2, 3, 3, 2, 2, 2, 2, 5]
def baseStart_806561 : Nat := 118140960795 + 806561 * 2 ^ 59
def prefixEnd_806561 : Nat := 4983230072969 + 3 ^ 40 * 806561 * 2
def baseEnd_806561 : Nat := 92034104482472013350711

theorem tailTrace_806561 : CollatzResearch.WordTrace tailWord_806561 prefixEnd_806561 92034104482472013350711 := by
  unfold tailWord_806561
  simp only [CollatzResearch.WordTrace]
  refine ⟨29417696430974721497099537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19611797620649814331399691 29417696430974721497099537)
  ·
    refine ⟨22063272323231041122824653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29417696430974721497099537 22063272323231041122824653)
    ·
      refine ⟨8273727121211640421059245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22063272323231041122824653 8273727121211640421059245)
      ·
        refine ⟨3102647670454365157897217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8273727121211640421059245 3102647670454365157897217)
        ·
          refine ⟨2326985752840773868422913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3102647670454365157897217 2326985752840773868422913)
          ·
            refine ⟨1745239314630580401317185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2326985752840773868422913 1745239314630580401317185)
            ·
              refine ⟨1308929485972935300987889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1745239314630580401317185 1308929485972935300987889)
              ·
                refine ⟨981697114479701475740917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1308929485972935300987889 981697114479701475740917)
                ·
                  refine ⟨92034104482472013350711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 981697114479701475740917 92034104482472013350711)
                  ·
                    rfl

theorem cell22_806561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 2, 5].length) (baseStart_806561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_806561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_806561 prefixEnd_806561 := by exact prefixLift 806561
  have htrace : WordTrace (prefixWord ++ tailWord_806561) baseStart_806561 baseEnd_806561 := by
    simpa [prefixWord, tailWord_806561, baseEnd_806561] using wordTrace_append hprefix tailTrace_806561
  have hstable : (prefixWord ++ tailWord_806561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806561).length < 2 ^ (prefixWord ++ tailWord_806561).sum := by decide
  have hdescent : baseEnd_806561 < baseStart_806561 := by decide
  rcases family_descends (prefixWord ++ tailWord_806561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806572 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 12]
def baseStart_806572 : Nat := 118140960795 + 806572 * 2 ^ 59
def prefixEnd_806572 : Nat := 4983230072969 + 3 ^ 40 * 806572 * 2
def baseEnd_806572 : Nat := 92035359657405226009033

theorem tailTrace_806572 : CollatzResearch.WordTrace tailWord_806572 prefixEnd_806572 92035359657405226009033 := by
  unfold tailWord_806572
  simp only [CollatzResearch.WordTrace]
  refine ⟨14709048816967435187874985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19612065089289913583833313 14709048816967435187874985)
  ·
    refine ⟨11031786612725576390906239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14709048816967435187874985 11031786612725576390906239)
    ·
      refine ⟨16547679919088364586359359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11031786612725576390906239 16547679919088364586359359)
      ·
        refine ⟨24821519878632546879539039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16547679919088364586359359 24821519878632546879539039)
        ·
          refine ⟨37232279817948820319308559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24821519878632546879539039 37232279817948820319308559)
          ·
            refine ⟨55848419726923230478962839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37232279817948820319308559 55848419726923230478962839)
            ·
              refine ⟨83772629590384845718444259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55848419726923230478962839 83772629590384845718444259)
              ·
                refine ⟨125658944385577268577666389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83772629590384845718444259 125658944385577268577666389)
                ·
                  refine ⟨92035359657405226009033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 125658944385577268577666389 92035359657405226009033)
                  ·
                    rfl

theorem cell22_806572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 12].length) (baseStart_806572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_806572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_806572 prefixEnd_806572 := by exact prefixLift 806572
  have htrace : WordTrace (prefixWord ++ tailWord_806572) baseStart_806572 baseEnd_806572 := by
    simpa [prefixWord, tailWord_806572, baseEnd_806572] using wordTrace_append hprefix tailTrace_806572
  have hstable : (prefixWord ++ tailWord_806572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806572).length < 2 ^ (prefixWord ++ tailWord_806572).sum := by decide
  have hdescent : baseEnd_806572 < baseStart_806572 := by decide
  rcases family_descends (prefixWord ++ tailWord_806572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806589 : List Nat := [1, 4, 1, 2, 1, 2, 3, 2, 6]
def baseStart_806589 : Nat := 118140960795 + 806589 * 2 ^ 59
def prefixEnd_806589 : Nat := 4983230072969 + 3 ^ 40 * 806589 * 2
def baseEnd_806589 : Nat := 92037299473211100117349

theorem tailTrace_806589 : CollatzResearch.WordTrace tailWord_806589 prefixEnd_806589 92037299473211100117349 := by
  unfold tailWord_806589
  simp only [CollatzResearch.WordTrace]
  refine ⟨29418717674873282279118821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19612478449915521519412547 29418717674873282279118821)
  ·
    refine ⟨5516009564038740427334779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29418717674873282279118821 5516009564038740427334779)
    ·
      refine ⟨8274014346058110641002169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5516009564038740427334779 8274014346058110641002169)
      ·
        refine ⟨6205510759543582980751627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8274014346058110641002169 6205510759543582980751627)
        ·
          refine ⟨9308266139315374471127441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6205510759543582980751627 9308266139315374471127441)
          ·
            refine ⟨6981199604486530853345581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9308266139315374471127441 6981199604486530853345581)
            ·
              refine ⟨2617949851682449070004593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6981199604486530853345581 2617949851682449070004593)
              ·
                refine ⟨1963462388761836802503445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2617949851682449070004593 1963462388761836802503445)
                ·
                  refine ⟨92037299473211100117349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1963462388761836802503445 92037299473211100117349)
                  ·
                    rfl

theorem cell22_806589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 2, 6].length) (baseStart_806589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_806589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_806589 prefixEnd_806589 := by exact prefixLift 806589
  have htrace : WordTrace (prefixWord ++ tailWord_806589) baseStart_806589 baseEnd_806589 := by
    simpa [prefixWord, tailWord_806589, baseEnd_806589] using wordTrace_append hprefix tailTrace_806589
  have hstable : (prefixWord ++ tailWord_806589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806589).length < 2 ^ (prefixWord ++ tailWord_806589).sum := by decide
  have hdescent : baseEnd_806589 < baseStart_806589 := by decide
  rcases family_descends (prefixWord ++ tailWord_806589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806773 : List Nat := [1, 3, 4, 1, 1, 1, 2, 2, 4, 3]
def baseStart_806773 : Nat := 118140960795 + 806773 * 2 ^ 59
def prefixEnd_806773 : Nat := 4983230072969 + 3 ^ 40 * 806773 * 2
def baseEnd_806773 : Nat := 276174885379918153751483

theorem tailTrace_806773 : CollatzResearch.WordTrace tailWord_806773 prefixEnd_806773 276174885379918153751483 := by
  unfold tailWord_806773
  simp only [CollatzResearch.WordTrace]
  refine ⟨29425428706206681703816973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19616952470804454469211315 29425428706206681703816973)
  ·
    refine ⟨11034535764827505638931365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29425428706206681703816973 11034535764827505638931365)
    ·
      refine ⟨2068975455905157307299631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11034535764827505638931365 2068975455905157307299631)
      ·
        refine ⟨3103463183857735960949447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2068975455905157307299631 3103463183857735960949447)
        ·
          refine ⟨4655194775786603941424171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3103463183857735960949447 4655194775786603941424171)
          ·
            refine ⟨6982792163679905912136257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4655194775786603941424171 6982792163679905912136257)
            ·
              refine ⟨5237094122759929434102193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6982792163679905912136257 5237094122759929434102193)
              ·
                refine ⟨3927820592069947075576645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5237094122759929434102193 3927820592069947075576645)
                ·
                  refine ⟨736466361013115076670621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3927820592069947075576645 736466361013115076670621)
                  ·
                    refine ⟨276174885379918153751483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 736466361013115076670621 276174885379918153751483)
                    ·
                      rfl

theorem cell22_806773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_806773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_806773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_806773 prefixEnd_806773 := by exact prefixLift 806773
  have htrace : WordTrace (prefixWord ++ tailWord_806773) baseStart_806773 baseEnd_806773 := by
    simpa [prefixWord, tailWord_806773, baseEnd_806773] using wordTrace_append hprefix tailTrace_806773
  have hstable : (prefixWord ++ tailWord_806773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806773).length < 2 ^ (prefixWord ++ tailWord_806773).sum := by decide
  have hdescent : baseEnd_806773 < baseStart_806773 := by decide
  rcases family_descends (prefixWord ++ tailWord_806773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806895 : List Nat := [1, 1, 2, 1, 4, 2, 5, 1, 1, 4]
def baseStart_806895 : Nat := 118140960795 + 806895 * 2 ^ 59
def prefixEnd_806895 : Nat := 4983230072969 + 3 ^ 40 * 806895 * 2
def baseEnd_806895 : Nat := 276216648473150502201109

theorem tailTrace_806895 : CollatzResearch.WordTrace tailWord_806895 prefixEnd_806895 276216648473150502201109 := by
  unfold tailWord_806895
  simp only [CollatzResearch.WordTrace]
  refine ⟨29429878411764696539758139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19619918941176464359838759 29429878411764696539758139)
  ·
    refine ⟨44144817617647044809637209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29429878411764696539758139 44144817617647044809637209)
    ·
      refine ⟨33108613213235283607227907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44144817617647044809637209 33108613213235283607227907)
      ·
        refine ⟨49662919819852925410841861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33108613213235283607227907 49662919819852925410841861)
        ·
          refine ⟨9311797466222423514532849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49662919819852925410841861 9311797466222423514532849)
          ·
            refine ⟨6983848099666817635899637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9311797466222423514532849 6983848099666817635899637)
            ·
              refine ⟨654735759343764153365591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6983848099666817635899637 654735759343764153365591)
              ·
                refine ⟨982103639015646230048387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 654735759343764153365591 982103639015646230048387)
                ·
                  refine ⟨1473155458523469345072581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 982103639015646230048387 1473155458523469345072581)
                  ·
                    refine ⟨276216648473150502201109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1473155458523469345072581 276216648473150502201109)
                    ·
                      rfl

theorem cell22_806895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 5, 1, 1, 4].length) (baseStart_806895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_806895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_806895 prefixEnd_806895 := by exact prefixLift 806895
  have htrace : WordTrace (prefixWord ++ tailWord_806895) baseStart_806895 baseEnd_806895 := by
    simpa [prefixWord, tailWord_806895, baseEnd_806895] using wordTrace_append hprefix tailTrace_806895
  have hstable : (prefixWord ++ tailWord_806895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806895).length < 2 ^ (prefixWord ++ tailWord_806895).sum := by decide
  have hdescent : baseEnd_806895 < baseStart_806895 := by decide
  rcases family_descends (prefixWord ++ tailWord_806895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806906 : List Nat := [3, 1, 1, 1, 1, 2, 1, 1, 5, 6]
def baseStart_806906 : Nat := 118140960795 + 806906 * 2 ^ 59
def prefixEnd_806906 : Nat := 4983230072969 + 3 ^ 40 * 806906 * 2
def baseEnd_806906 : Nat := 276220413997950140176075

theorem tailTrace_806906 : CollatzResearch.WordTrace tailWord_806906 prefixEnd_806906 276220413997950140176075 := by
  unfold tailWord_806906
  simp only [CollatzResearch.WordTrace]
  refine ⟨7357569903681211354602143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19620186409816563612272381 7357569903681211354602143)
  ·
    refine ⟨11036354855521817031903215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7357569903681211354602143 11036354855521817031903215)
    ·
      refine ⟨16554532283282725547854823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11036354855521817031903215 16554532283282725547854823)
      ·
        refine ⟨24831798424924088321782235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16554532283282725547854823 24831798424924088321782235)
        ·
          refine ⟨37247697637386132482673353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24831798424924088321782235 37247697637386132482673353)
          ·
            refine ⟨27935773228039599362005015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37247697637386132482673353 27935773228039599362005015)
            ·
              refine ⟨41903659842059399043007523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27935773228039599362005015 41903659842059399043007523)
              ·
                refine ⟨62855489763089098564511285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41903659842059399043007523 62855489763089098564511285)
                ·
                  refine ⟨5892702165289602990422933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62855489763089098564511285 5892702165289602990422933)
                  ·
                    refine ⟨276220413997950140176075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5892702165289602990422933 276220413997950140176075)
                    ·
                      rfl

theorem cell22_806906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 5, 6].length) (baseStart_806906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_806906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_806906 prefixEnd_806906 := by exact prefixLift 806906
  have htrace : WordTrace (prefixWord ++ tailWord_806906) baseStart_806906 baseEnd_806906 := by
    simpa [prefixWord, tailWord_806906, baseEnd_806906] using wordTrace_append hprefix tailTrace_806906
  have hstable : (prefixWord ++ tailWord_806906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806906).length < 2 ^ (prefixWord ++ tailWord_806906).sum := by decide
  have hdescent : baseEnd_806906 < baseStart_806906 := by decide
  rcases family_descends (prefixWord ++ tailWord_806906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_806940 : List Nat := [2, 2, 3, 1, 3, 1, 3, 1, 2, 4]
def baseStart_806940 : Nat := 118140960795 + 806940 * 2 ^ 59
def prefixEnd_806940 : Nat := 4983230072969 + 3 ^ 40 * 806940 * 2
def baseEnd_806940 : Nat := 276232052892785384825971

theorem tailTrace_806940 : CollatzResearch.WordTrace tailWord_806940 prefixEnd_806940 276232052892785384825971 := by
  unfold tailWord_806940
  simp only [CollatzResearch.WordTrace]
  refine ⟨14715759848300834612573137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19621013131067779483430849 14715759848300834612573137)
  ·
    refine ⟨11036819886225625959429853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14715759848300834612573137 11036819886225625959429853)
    ·
      refine ⟨4138807457334609734786195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11036819886225625959429853 4138807457334609734786195)
      ·
        refine ⟨6208211186001914602179293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4138807457334609734786195 6208211186001914602179293)
        ·
          refine ⟨2328079194750717975817235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6208211186001914602179293 2328079194750717975817235)
          ·
            refine ⟨3492118792126076963725853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2328079194750717975817235 3492118792126076963725853)
            ·
              refine ⟨1309544547047278861397195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3492118792126076963725853 1309544547047278861397195)
              ·
                refine ⟨1964316820570918292095793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1309544547047278861397195 1964316820570918292095793)
                ·
                  refine ⟨1473237615428188719071845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1964316820570918292095793 1473237615428188719071845)
                  ·
                    refine ⟨276232052892785384825971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1473237615428188719071845 276232052892785384825971)
                    ·
                      rfl

theorem cell22_806940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_806940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_806940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_806940 prefixEnd_806940 := by exact prefixLift 806940
  have htrace : WordTrace (prefixWord ++ tailWord_806940) baseStart_806940 baseEnd_806940 := by
    simpa [prefixWord, tailWord_806940, baseEnd_806940] using wordTrace_append hprefix tailTrace_806940
  have hstable : (prefixWord ++ tailWord_806940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_806940).length < 2 ^ (prefixWord ++ tailWord_806940).sum := by decide
  have hdescent : baseEnd_806940 < baseStart_806940 := by decide
  rcases family_descends (prefixWord ++ tailWord_806940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807004 : List Nat := [2, 2, 4, 1, 1, 2, 3, 3, 1, 3]
def baseStart_807004 : Nat := 118140960795 + 807004 * 2 ^ 59
def prefixEnd_807004 : Nat := 4983230072969 + 3 ^ 40 * 807004 * 2
def baseEnd_807004 : Nat := 276253961400710551225775

theorem tailTrace_807004 : CollatzResearch.WordTrace tailWord_807004 prefixEnd_807004 276253961400710551225775 := by
  unfold tailWord_807004
  simp only [CollatzResearch.WordTrace]
  refine ⟨14716926984184904077738033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19622569312246538770317377 14716926984184904077738033)
  ·
    refine ⟨11037695238138678058303525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14716926984184904077738033 11037695238138678058303525)
    ·
      refine ⟨2069567857151002135931911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11037695238138678058303525 2069567857151002135931911)
      ·
        refine ⟨3104351785726503203897867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2069567857151002135931911 3104351785726503203897867)
        ·
          refine ⟨4656527678589754805846801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3104351785726503203897867 4656527678589754805846801)
          ·
            refine ⟨3492395758942316104385101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4656527678589754805846801 3492395758942316104385101)
            ·
              refine ⟨1309648409603368539144413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3492395758942316104385101 1309648409603368539144413)
              ·
                refine ⟨491118153601263202179155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1309648409603368539144413 491118153601263202179155)
                ·
                  refine ⟨736677230401894803268733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 491118153601263202179155 736677230401894803268733)
                  ·
                    refine ⟨276253961400710551225775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 736677230401894803268733 276253961400710551225775)
                    ·
                      rfl

theorem cell22_807004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_807004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_807004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_807004 prefixEnd_807004 := by exact prefixLift 807004
  have htrace : WordTrace (prefixWord ++ tailWord_807004) baseStart_807004 baseEnd_807004 := by
    simpa [prefixWord, tailWord_807004, baseEnd_807004] using wordTrace_append hprefix tailTrace_807004
  have hstable : (prefixWord ++ tailWord_807004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807004).length < 2 ^ (prefixWord ++ tailWord_807004).sum := by decide
  have hdescent : baseEnd_807004 < baseStart_807004 := by decide
  rcases family_descends (prefixWord ++ tailWord_807004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807064 : List Nat := [2, 1, 2, 4, 3, 1, 3, 1, 1, 4]
def baseStart_807064 : Nat := 118140960795 + 807064 * 2 ^ 59
def prefixEnd_807064 : Nat := 4983230072969 + 3 ^ 40 * 807064 * 2
def baseEnd_807064 : Nat := 276274500626890394725591

theorem tailTrace_807064 : CollatzResearch.WordTrace tailWord_807064 prefixEnd_807064 276274500626890394725591 := by
  unfold tailWord_807064
  simp only [CollatzResearch.WordTrace]
  refine ⟨14718021174076219201330123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19624028232101625601773497 14718021174076219201330123)
  ·
    refine ⟨22077031761114328801995185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14718021174076219201330123 22077031761114328801995185)
    ·
      refine ⟨16557773820835746601496389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22077031761114328801995185 16557773820835746601496389)
      ·
        refine ⟨3104582591406702487780573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16557773820835746601496389 3104582591406702487780573)
        ·
          refine ⟨1164218471777513432917715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3104582591406702487780573 1164218471777513432917715)
          ·
            refine ⟨1746327707666270149376573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1164218471777513432917715 1746327707666270149376573)
            ·
              refine ⟨654872890374851306016215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1746327707666270149376573 654872890374851306016215)
              ·
                refine ⟨982309335562276959024323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 654872890374851306016215 982309335562276959024323)
                ·
                  refine ⟨1473464003343415438536485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 982309335562276959024323 1473464003343415438536485)
                  ·
                    refine ⟨276274500626890394725591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1473464003343415438536485 276274500626890394725591)
                    ·
                      rfl

theorem cell22_807064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 3, 1, 1, 4].length) (baseStart_807064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_807064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_807064 prefixEnd_807064 := by exact prefixLift 807064
  have htrace : WordTrace (prefixWord ++ tailWord_807064) baseStart_807064 baseEnd_807064 := by
    simpa [prefixWord, tailWord_807064, baseEnd_807064] using wordTrace_append hprefix tailTrace_807064
  have hstable : (prefixWord ++ tailWord_807064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807064).length < 2 ^ (prefixWord ++ tailWord_807064).sum := by decide
  have hdescent : baseEnd_807064 < baseStart_807064 := by decide
  rcases family_descends (prefixWord ++ tailWord_807064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807073 : List Nat := [1, 2, 3, 3, 1, 12]
def baseStart_807073 : Nat := 118140960795 + 807073 * 2 ^ 59
def prefixEnd_807073 : Nat := 4983230072969 + 3 ^ 40 * 807073 * 2
def baseEnd_807073 : Nat := 3410834339639720632723

theorem tailTrace_807073 : CollatzResearch.WordTrace tailWord_807073 prefixEnd_807073 3410834339639720632723 := by
  unfold tailWord_807073
  simp only [CollatzResearch.WordTrace]
  refine ⟨29436370605119832939737873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19624247070079888626491915 29436370605119832939737873)
  ·
    refine ⟨22077277953839874704803405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29436370605119832939737873 22077277953839874704803405)
    ·
      refine ⟨8278979232689953014301277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22077277953839874704803405 8278979232689953014301277)
      ·
        refine ⟨3104617212258732380362979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8278979232689953014301277 3104617212258732380362979)
        ·
          refine ⟨4656925818388098570544469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3104617212258732380362979 4656925818388098570544469)
          ·
            refine ⟨3410834339639720632723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 4656925818388098570544469 3410834339639720632723)
            ·
              rfl

theorem cell22_807073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 12].length) (baseStart_807073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_807073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_807073 prefixEnd_807073 := by exact prefixLift 807073
  have htrace : WordTrace (prefixWord ++ tailWord_807073) baseStart_807073 baseEnd_807073 := by
    simpa [prefixWord, tailWord_807073, baseEnd_807073] using wordTrace_append hprefix tailTrace_807073
  have hstable : (prefixWord ++ tailWord_807073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807073).length < 2 ^ (prefixWord ++ tailWord_807073).sum := by decide
  have hdescent : baseEnd_807073 < baseStart_807073 := by decide
  rcases family_descends (prefixWord ++ tailWord_807073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807077 : List Nat := [1, 3, 1, 2, 1, 3, 4, 2, 2, 3]
def baseStart_807077 : Nat := 118140960795 + 807077 * 2 ^ 59
def prefixEnd_807077 : Nat := 4983230072969 + 3 ^ 40 * 807077 * 2
def baseEnd_807077 : Nat := 276278950792562694150551

theorem tailTrace_807077 : CollatzResearch.WordTrace tailWord_807077 prefixEnd_807077 276278950792562694150551 := by
  unfold tailWord_807077
  simp only [CollatzResearch.WordTrace]
  refine ⟨29436516497105341622883485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19624344331403561081922323 29436516497105341622883485)
  ·
    refine ⟨11038693686414503108581307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29436516497105341622883485 11038693686414503108581307)
    ·
      refine ⟨16558040529621754662871961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11038693686414503108581307 16558040529621754662871961)
      ·
        refine ⟨12418530397216315997153971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16558040529621754662871961 12418530397216315997153971)
        ·
          refine ⟨18627795595824473995730957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12418530397216315997153971 18627795595824473995730957)
          ·
            refine ⟨6985423348434177748399109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18627795595824473995730957 6985423348434177748399109)
            ·
              refine ⟨1309766877831408327824833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6985423348434177748399109 1309766877831408327824833)
              ·
                refine ⟨982325158373556245868625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1309766877831408327824833 982325158373556245868625)
                ·
                  refine ⟨736743868780167184401469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 982325158373556245868625 736743868780167184401469)
                  ·
                    refine ⟨276278950792562694150551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 736743868780167184401469 276278950792562694150551)
                    ·
                      rfl

theorem cell22_807077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 2, 2, 3].length) (baseStart_807077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_807077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_807077 prefixEnd_807077 := by exact prefixLift 807077
  have htrace : WordTrace (prefixWord ++ tailWord_807077) baseStart_807077 baseEnd_807077 := by
    simpa [prefixWord, tailWord_807077, baseEnd_807077] using wordTrace_append hprefix tailTrace_807077
  have hstable : (prefixWord ++ tailWord_807077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807077).length < 2 ^ (prefixWord ++ tailWord_807077).sum := by decide
  have hdescent : baseEnd_807077 < baseStart_807077 := by decide
  rcases family_descends (prefixWord ++ tailWord_807077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807079 : List Nat := [1, 1, 6, 2, 2, 1, 1, 4, 4]
def baseStart_807079 : Nat := 118140960795 + 807079 * 2 ^ 59
def prefixEnd_807079 : Nat := 4983230072969 + 3 ^ 40 * 807079 * 2
def baseEnd_807079 : Nat := 92093211811145118533515

theorem tailTrace_807079 : CollatzResearch.WordTrace tailWord_807079 prefixEnd_807079 92093211811145118533515 := by
  unfold tailWord_807079
  simp only [CollatzResearch.WordTrace]
  refine ⟨29436589443098095964456291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19624392962065397309637527 29436589443098095964456291)
  ·
    refine ⟨44154884164647143946684437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29436589443098095964456291 44154884164647143946684437)
    ·
      refine ⟨2069760195217834872500833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 44154884164647143946684437 2069760195217834872500833)
      ·
        refine ⟨1552320146413376154375625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2069760195217834872500833 1552320146413376154375625)
        ·
          refine ⟨1164240109810032115781719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1552320146413376154375625 1164240109810032115781719)
          ·
            refine ⟨1746360164715048173672579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1164240109810032115781719 1746360164715048173672579)
            ·
              refine ⟨2619540247072572260508869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1746360164715048173672579 2619540247072572260508869)
              ·
                refine ⟨491163796326107298845413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2619540247072572260508869 491163796326107298845413)
                ·
                  refine ⟨92093211811145118533515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 491163796326107298845413 92093211811145118533515)
                  ·
                    rfl

theorem cell22_807079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 4, 4].length) (baseStart_807079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_807079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_807079 prefixEnd_807079 := by exact prefixLift 807079
  have htrace : WordTrace (prefixWord ++ tailWord_807079) baseStart_807079 baseEnd_807079 := by
    simpa [prefixWord, tailWord_807079, baseEnd_807079] using wordTrace_append hprefix tailTrace_807079
  have hstable : (prefixWord ++ tailWord_807079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807079).length < 2 ^ (prefixWord ++ tailWord_807079).sum := by decide
  have hdescent : baseEnd_807079 < baseStart_807079 := by decide
  rcases family_descends (prefixWord ++ tailWord_807079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807103 : List Nat := [1, 1, 2, 2, 2, 2, 1, 1, 4, 6]
def baseStart_807103 : Nat := 118140960795 + 807103 * 2 ^ 59
def prefixEnd_807103 : Nat := 4983230072969 + 3 ^ 40 * 807103 * 2
def baseEnd_807103 : Nat := 276287851123907293000471

theorem tailTrace_807103 : CollatzResearch.WordTrace tailWord_807103 prefixEnd_807103 276287851123907293000471 := by
  unfold tailWord_807103
  simp only [CollatzResearch.WordTrace]
  refine ⟨29437464795011148063329963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19624976530007432042219975 29437464795011148063329963)
  ·
    refine ⟨44156197192516722094994945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29437464795011148063329963 44156197192516722094994945)
    ·
      refine ⟨33117147894387541571246209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44156197192516722094994945 33117147894387541571246209)
      ·
        refine ⟨24837860920790656178434657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33117147894387541571246209 24837860920790656178434657)
        ·
          refine ⟨18628395690592992133825993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24837860920790656178434657 18628395690592992133825993)
          ·
            refine ⟨13971296767944744100369495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18628395690592992133825993 13971296767944744100369495)
            ·
              refine ⟨20956945151917116150554243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13971296767944744100369495 20956945151917116150554243)
              ·
                refine ⟨31435417727875674225831365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20956945151917116150554243 31435417727875674225831365)
                ·
                  refine ⟨5894140823976688917343381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31435417727875674225831365 5894140823976688917343381)
                  ·
                    refine ⟨276287851123907293000471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5894140823976688917343381 276287851123907293000471)
                    ·
                      rfl

theorem cell22_807103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4, 6].length) (baseStart_807103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_807103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_807103 prefixEnd_807103 := by exact prefixLift 807103
  have htrace : WordTrace (prefixWord ++ tailWord_807103) baseStart_807103 baseEnd_807103 := by
    simpa [prefixWord, tailWord_807103, baseEnd_807103] using wordTrace_append hprefix tailTrace_807103
  have hstable : (prefixWord ++ tailWord_807103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807103).length < 2 ^ (prefixWord ++ tailWord_807103).sum := by decide
  have hdescent : baseEnd_807103 < baseStart_807103 := by decide
  rcases family_descends (prefixWord ++ tailWord_807103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807165 : List Nat := [1, 4, 1, 1, 1, 1, 1, 5, 3, 4]
def baseStart_807165 : Nat := 118140960795 + 807165 * 2 ^ 59
def prefixEnd_807165 : Nat := 4983230072969 + 3 ^ 40 * 807165 * 2
def baseEnd_807165 : Nat := 276309074990959797950281

theorem tailTrace_807165 : CollatzResearch.WordTrace tailWord_807165 prefixEnd_807165 276309074990959797950281 := by
  unfold tailWord_807165
  simp only [CollatzResearch.WordTrace]
  refine ⟨29439726120786532652086949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19626484080524355101391299 29439726120786532652086949)
  ·
    refine ⟨5519948647647474872266303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29439726120786532652086949 5519948647647474872266303)
    ·
      refine ⟨8279922971471212308399455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5519948647647474872266303 8279922971471212308399455)
      ·
        refine ⟨12419884457206818462599183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8279922971471212308399455 12419884457206818462599183)
        ·
          refine ⟨18629826685810227693898775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12419884457206818462599183 18629826685810227693898775)
          ·
            refine ⟨27944740028715341540848163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18629826685810227693898775 27944740028715341540848163)
            ·
              refine ⟨41917110043073012311272245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27944740028715341540848163 41917110043073012311272245)
              ·
                refine ⟨3929729066538094904181773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41917110043073012311272245 3929729066538094904181773)
                ·
                  refine ⟨1473648399951785589068165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3929729066538094904181773 1473648399951785589068165)
                  ·
                    refine ⟨276309074990959797950281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1473648399951785589068165 276309074990959797950281)
                    ·
                      rfl

theorem cell22_807165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5, 3, 4].length) (baseStart_807165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_807165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_807165 prefixEnd_807165 := by exact prefixLift 807165
  have htrace : WordTrace (prefixWord ++ tailWord_807165) baseStart_807165 baseEnd_807165 := by
    simpa [prefixWord, tailWord_807165, baseEnd_807165] using wordTrace_append hprefix tailTrace_807165
  have hstable : (prefixWord ++ tailWord_807165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807165).length < 2 ^ (prefixWord ++ tailWord_807165).sum := by decide
  have hdescent : baseEnd_807165 < baseStart_807165 := by decide
  rcases family_descends (prefixWord ++ tailWord_807165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807182 : List Nat := [4, 1, 1, 2, 1, 2, 1, 5, 1, 4]
def baseStart_807182 : Nat := 118140960795 + 807182 * 2 ^ 59
def prefixEnd_807182 : Nat := 4983230072969 + 3 ^ 40 * 807182 * 2
def baseEnd_807182 : Nat := 276314894438377420275229

theorem tailTrace_807182 : CollatzResearch.WordTrace tailWord_807182 prefixEnd_807182 276314894438377420275229 := by
  unfold tailWord_807182
  simp only [CollatzResearch.WordTrace]
  refine ⟨3680043270215618069431975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19626897441149963036970533 3680043270215618069431975)
  ·
    refine ⟨5520064905323427104147963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3680043270215618069431975 5520064905323427104147963)
    ·
      refine ⟨8280097357985140656221945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5520064905323427104147963 8280097357985140656221945)
      ·
        refine ⟨6210073018488855492166459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8280097357985140656221945 6210073018488855492166459)
        ·
          refine ⟨9315109527733283238249689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6210073018488855492166459 9315109527733283238249689)
          ·
            refine ⟨6986332145799962428687267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9315109527733283238249689 6986332145799962428687267)
            ·
              refine ⟨10479498218699943643030901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6986332145799962428687267 10479498218699943643030901)
              ·
                refine ⟨982452958003119716534147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10479498218699943643030901 982452958003119716534147)
                ·
                  refine ⟨1473679437004679574801221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 982452958003119716534147 1473679437004679574801221)
                  ·
                    refine ⟨276314894438377420275229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1473679437004679574801221 276314894438377420275229)
                    ·
                      rfl

theorem cell22_807182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 5, 1, 4].length) (baseStart_807182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_807182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_807182 prefixEnd_807182 := by exact prefixLift 807182
  have htrace : WordTrace (prefixWord ++ tailWord_807182) baseStart_807182 baseEnd_807182 := by
    simpa [prefixWord, tailWord_807182, baseEnd_807182] using wordTrace_append hprefix tailTrace_807182
  have hstable : (prefixWord ++ tailWord_807182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807182).length < 2 ^ (prefixWord ++ tailWord_807182).sum := by decide
  have hdescent : baseEnd_807182 < baseStart_807182 := by decide
  rcases family_descends (prefixWord ++ tailWord_807182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807255 : List Nat := [1, 1, 3, 2, 3, 1, 1, 1, 1, 8]
def baseStart_807255 : Nat := 118140960795 + 807255 * 2 ^ 59
def prefixEnd_807255 : Nat := 4983230072969 + 3 ^ 40 * 807255 * 2
def baseEnd_807255 : Nat := 276339883830229563200005

theorem tailTrace_807255 : CollatzResearch.WordTrace tailWord_807255 prefixEnd_807255 276339883830229563200005 := by
  unfold tailWord_807255
  simp only [CollatzResearch.WordTrace]
  refine ⟨29443008690460478022863219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19628672460306985348575479 29443008690460478022863219)
  ·
    refine ⟨44164513035690717034294829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29443008690460478022863219 44164513035690717034294829)
    ·
      refine ⟨16561692388384018887860561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44164513035690717034294829 16561692388384018887860561)
      ·
        refine ⟨12421269291288014165895421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16561692388384018887860561 12421269291288014165895421)
        ·
          refine ⟨4657975984233005312210783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12421269291288014165895421 4657975984233005312210783)
          ·
            refine ⟨6986963976349507968316175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4657975984233005312210783 6986963976349507968316175)
            ·
              refine ⟨10480445964524261952474263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6986963976349507968316175 10480445964524261952474263)
              ·
                refine ⟨15720668946786392928711395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10480445964524261952474263 15720668946786392928711395)
                ·
                  refine ⟨23581003420179589393067093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15720668946786392928711395 23581003420179589393067093)
                  ·
                    refine ⟨276339883830229563200005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 23581003420179589393067093 276339883830229563200005)
                    ·
                      rfl

theorem cell22_807255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 8].length) (baseStart_807255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_807255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_807255 prefixEnd_807255 := by exact prefixLift 807255
  have htrace : WordTrace (prefixWord ++ tailWord_807255) baseStart_807255 baseEnd_807255 := by
    simpa [prefixWord, tailWord_807255, baseEnd_807255] using wordTrace_append hprefix tailTrace_807255
  have hstable : (prefixWord ++ tailWord_807255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807255).length < 2 ^ (prefixWord ++ tailWord_807255).sum := by decide
  have hdescent : baseEnd_807255 < baseStart_807255 := by decide
  rcases family_descends (prefixWord ++ tailWord_807255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807257 : List Nat := [1, 2, 1, 2, 2, 2, 1, 5, 3, 3]
def baseStart_807257 : Nat := 118140960795 + 807257 * 2 ^ 59
def prefixEnd_807257 : Nat := 4983230072969 + 3 ^ 40 * 807257 * 2
def baseEnd_807257 : Nat := 276340568471102224649999

theorem tailTrace_807257 : CollatzResearch.WordTrace tailWord_807257 prefixEnd_807257 276340568471102224649999 := by
  unfold tailWord_807257
  simp only [CollatzResearch.WordTrace]
  refine ⟨29443081636453232364436025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19628721090968821576290683 29443081636453232364436025)
  ·
    refine ⟨22082311227339924273327019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29443081636453232364436025 22082311227339924273327019)
    ·
      refine ⟨33123466841009886409990529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22082311227339924273327019 33123466841009886409990529)
      ·
        refine ⟨24842600130757414807492897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33123466841009886409990529 24842600130757414807492897)
        ·
          refine ⟨18631950098068061105619673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24842600130757414807492897 18631950098068061105619673)
          ·
            refine ⟨13973962573551045829214755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18631950098068061105619673 13973962573551045829214755)
            ·
              refine ⟨20960943860326568743822133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13973962573551045829214755 20960943860326568743822133)
              ·
                refine ⟨1965088486905615819733325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20960943860326568743822133 1965088486905615819733325)
                ·
                  refine ⟨736908182589605932399997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1965088486905615819733325 736908182589605932399997)
                  ·
                    refine ⟨276340568471102224649999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 736908182589605932399997 276340568471102224649999)
                    ·
                      rfl

theorem cell22_807257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 5, 3, 3].length) (baseStart_807257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_807257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_807257 prefixEnd_807257 := by exact prefixLift 807257
  have htrace : WordTrace (prefixWord ++ tailWord_807257) baseStart_807257 baseEnd_807257 := by
    simpa [prefixWord, tailWord_807257, baseEnd_807257] using wordTrace_append hprefix tailTrace_807257
  have hstable : (prefixWord ++ tailWord_807257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807257).length < 2 ^ (prefixWord ++ tailWord_807257).sum := by decide
  have hdescent : baseEnd_807257 < baseStart_807257 := by decide
  rcases family_descends (prefixWord ++ tailWord_807257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807274 : List Nat := [3, 1, 3, 3, 1, 1, 1, 1, 5, 3]
def baseStart_807274 : Nat := 118140960795 + 807274 * 2 ^ 59
def prefixEnd_807274 : Nat := 4983230072969 + 3 ^ 40 * 807274 * 2
def baseEnd_807274 : Nat := 276346387918519846974947

theorem tailTrace_807274 : CollatzResearch.WordTrace tailWord_807274 prefixEnd_807274 276346387918519846974947 := by
  unfold tailWord_807274
  simp only [CollatzResearch.WordTrace]
  refine ⟨7360925419347911066951219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19629134451594429511869917 7360925419347911066951219)
  ·
    refine ⟨11041388129021866600426829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7360925419347911066951219 11041388129021866600426829)
    ·
      refine ⟨4140520548383199975160061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11041388129021866600426829 4140520548383199975160061)
      ·
        refine ⟨1552695205643699990685023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4140520548383199975160061 1552695205643699990685023)
        ·
          refine ⟨2329042808465549986027535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1552695205643699990685023 2329042808465549986027535)
          ·
            refine ⟨3493564212698324979041303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2329042808465549986027535 3493564212698324979041303)
            ·
              refine ⟨5240346319047487468561955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3493564212698324979041303 5240346319047487468561955)
              ·
                refine ⟨7860519478571231202842933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5240346319047487468561955 7860519478571231202842933)
                ·
                  refine ⟨736923701116052925266525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7860519478571231202842933 736923701116052925266525)
                  ·
                    refine ⟨276346387918519846974947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 736923701116052925266525 276346387918519846974947)
                    ·
                      rfl

theorem cell22_807274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 5, 3].length) (baseStart_807274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_807274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_807274 prefixEnd_807274 := by exact prefixLift 807274
  have htrace : WordTrace (prefixWord ++ tailWord_807274) baseStart_807274 baseEnd_807274 := by
    simpa [prefixWord, tailWord_807274, baseEnd_807274] using wordTrace_append hprefix tailTrace_807274
  have hstable : (prefixWord ++ tailWord_807274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807274).length < 2 ^ (prefixWord ++ tailWord_807274).sum := by decide
  have hdescent : baseEnd_807274 < baseStart_807274 := by decide
  rcases family_descends (prefixWord ++ tailWord_807274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807291 : List Nat := [1, 1, 1, 1, 1, 8, 2, 3, 1, 3]
def baseStart_807291 : Nat := 118140960795 + 807291 * 2 ^ 59
def prefixEnd_807291 : Nat := 4983230072969 + 3 ^ 40 * 807291 * 2
def baseEnd_807291 : Nat := 276352207365937469299895

theorem tailTrace_807291 : CollatzResearch.WordTrace tailWord_807291 prefixEnd_807291 276352207365937469299895 := by
  unfold tailWord_807291
  simp only [CollatzResearch.WordTrace]
  refine ⟨29444321718330056171173727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19629547812220037447449151 29444321718330056171173727)
  ·
    refine ⟨44166482577495084256760591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29444321718330056171173727 44166482577495084256760591)
    ·
      refine ⟨66249723866242626385140887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44166482577495084256760591 66249723866242626385140887)
      ·
        refine ⟨99374585799363939577711331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66249723866242626385140887 99374585799363939577711331)
        ·
          refine ⟨149061878699045909366566997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99374585799363939577711331 149061878699045909366566997)
          ·
            refine ⟨1746818891004444250389457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 149061878699045909366566997 1746818891004444250389457)
            ·
              refine ⟨1310114168253333187792093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1746818891004444250389457 1310114168253333187792093)
              ·
                refine ⟨491292813094999945422035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1310114168253333187792093 491292813094999945422035)
                ·
                  refine ⟨736939219642499918133053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 491292813094999945422035 736939219642499918133053)
                  ·
                    refine ⟨276352207365937469299895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 736939219642499918133053 276352207365937469299895)
                    ·
                      rfl

theorem cell22_807291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 3, 1, 3].length) (baseStart_807291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_807291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_807291 prefixEnd_807291 := by exact prefixLift 807291
  have htrace : WordTrace (prefixWord ++ tailWord_807291) baseStart_807291 baseEnd_807291 := by
    simpa [prefixWord, tailWord_807291, baseEnd_807291] using wordTrace_append hprefix tailTrace_807291
  have hstable : (prefixWord ++ tailWord_807291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807291).length < 2 ^ (prefixWord ++ tailWord_807291).sum := by decide
  have hdescent : baseEnd_807291 < baseStart_807291 := by decide
  rcases family_descends (prefixWord ++ tailWord_807291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807332 : List Nat := [2, 3, 1, 2, 1, 1, 4, 2, 6]
def baseStart_807332 : Nat := 118140960795 + 807332 * 2 ^ 59
def prefixEnd_807332 : Nat := 4983230072969 + 3 ^ 40 * 807332 * 2
def baseEnd_807332 : Nat := 92122080834609009674923

theorem tailTrace_807332 : CollatzResearch.WordTrace tailWord_807332 prefixEnd_807332 92122080834609009674923 := by
  unfold tailWord_807332
  simp only [CollatzResearch.WordTrace]
  refine ⟨14722908555590760086708125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19630544740787680115610833 14722908555590760086708125)
  ·
    refine ⟨5521090708346535032515547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14722908555590760086708125 5521090708346535032515547)
    ·
      refine ⟨8281636062519802548773321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5521090708346535032515547 8281636062519802548773321)
      ·
        refine ⟨6211227046889851911579991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8281636062519802548773321 6211227046889851911579991)
        ·
          refine ⟨9316840570334777867369987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6211227046889851911579991 9316840570334777867369987)
          ·
            refine ⟨13975260855502166801054981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9316840570334777867369987 13975260855502166801054981)
            ·
              refine ⟨2620361410406656275197809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13975260855502166801054981 2620361410406656275197809)
              ·
                refine ⟨1965271057804992206398357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2620361410406656275197809 1965271057804992206398357)
                ·
                  refine ⟨92122080834609009674923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1965271057804992206398357 92122080834609009674923)
                  ·
                    rfl

theorem cell22_807332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 2, 6].length) (baseStart_807332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_807332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_807332 prefixEnd_807332 := by exact prefixLift 807332
  have htrace : WordTrace (prefixWord ++ tailWord_807332) baseStart_807332 baseEnd_807332 := by
    simpa [prefixWord, tailWord_807332, baseEnd_807332] using wordTrace_append hprefix tailTrace_807332
  have hstable : (prefixWord ++ tailWord_807332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807332).length < 2 ^ (prefixWord ++ tailWord_807332).sum := by decide
  have hdescent : baseEnd_807332 < baseStart_807332 := by decide
  rcases family_descends (prefixWord ++ tailWord_807332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807381 : List Nat := [1, 3, 2, 3, 1, 3, 1, 3, 2, 3]
def baseStart_807381 : Nat := 118140960795 + 807381 * 2 ^ 59
def prefixEnd_807381 : Nat := 4983230072969 + 3 ^ 40 * 807381 * 2
def baseEnd_807381 : Nat := 276383016205207234549619

theorem tailTrace_807381 : CollatzResearch.WordTrace tailWord_807381 prefixEnd_807381 276383016205207234549619 := by
  unfold tailWord_807381
  simp only [CollatzResearch.WordTrace]
  refine ⟨29447604288004001541949997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19631736192002667694633331 29447604288004001541949997)
  ·
    refine ⟨11042851608001500578231249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29447604288004001541949997 11042851608001500578231249)
    ·
      refine ⟨8282138706001125433673437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11042851608001500578231249 8282138706001125433673437)
      ·
        refine ⟨3105802014750422037627539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8282138706001125433673437 3105802014750422037627539)
        ·
          refine ⟨4658703022125633056441309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3105802014750422037627539 4658703022125633056441309)
          ·
            refine ⟨1747013633297112396165491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4658703022125633056441309 1747013633297112396165491)
            ·
              refine ⟨2620520449945668594248237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1747013633297112396165491 2620520449945668594248237)
              ·
                refine ⟨982695168729625722843089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2620520449945668594248237 982695168729625722843089)
                ·
                  refine ⟨737021376547219292132317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 982695168729625722843089 737021376547219292132317)
                  ·
                    refine ⟨276383016205207234549619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 737021376547219292132317 276383016205207234549619)
                    ·
                      rfl

theorem cell22_807381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 3, 2, 3].length) (baseStart_807381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_807381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_807381 prefixEnd_807381 := by exact prefixLift 807381
  have htrace : WordTrace (prefixWord ++ tailWord_807381) baseStart_807381 baseEnd_807381 := by
    simpa [prefixWord, tailWord_807381, baseEnd_807381] using wordTrace_append hprefix tailTrace_807381
  have hstable : (prefixWord ++ tailWord_807381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807381).length < 2 ^ (prefixWord ++ tailWord_807381).sum := by decide
  have hdescent : baseEnd_807381 < baseStart_807381 := by decide
  rcases family_descends (prefixWord ++ tailWord_807381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807484 : List Nat := [2, 2, 2, 2, 3, 1, 1, 3, 6]
def baseStart_807484 : Nat := 118140960795 + 807484 * 2 ^ 59
def prefixEnd_807484 : Nat := 4983230072969 + 3 ^ 40 * 807484 * 2
def baseEnd_807484 : Nat := 92139425070049766408101

theorem tailTrace_807484 : CollatzResearch.WordTrace tailWord_807484 prefixEnd_807484 92139425070049766408101 := by
  unfold tailWord_807484
  simp only [CollatzResearch.WordTrace]
  refine ⟨14725680503315425066474753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19634240671087233421966337 14725680503315425066474753)
  ·
    refine ⟨11044260377486568799856065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14725680503315425066474753 11044260377486568799856065)
    ·
      refine ⟨8283195283114926599892049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11044260377486568799856065 8283195283114926599892049)
      ·
        refine ⟨6212396462336194949919037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8283195283114926599892049 6212396462336194949919037)
        ·
          refine ⟨2329648673376073106219639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6212396462336194949919037 2329648673376073106219639)
          ·
            refine ⟨3494473010064109659329459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2329648673376073106219639 3494473010064109659329459)
            ·
              refine ⟨5241709515096164488994189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3494473010064109659329459 5241709515096164488994189)
              ·
                refine ⟨1965641068161061683372821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5241709515096164488994189 1965641068161061683372821)
                ·
                  refine ⟨92139425070049766408101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1965641068161061683372821 92139425070049766408101)
                  ·
                    rfl

theorem cell22_807484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 3, 6].length) (baseStart_807484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_807484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_807484 prefixEnd_807484 := by exact prefixLift 807484
  have htrace : WordTrace (prefixWord ++ tailWord_807484) baseStart_807484 baseEnd_807484 := by
    simpa [prefixWord, tailWord_807484, baseEnd_807484] using wordTrace_append hprefix tailTrace_807484
  have hstable : (prefixWord ++ tailWord_807484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807484).length < 2 ^ (prefixWord ++ tailWord_807484).sum := by decide
  have hdescent : baseEnd_807484 < baseStart_807484 := by decide
  rcases family_descends (prefixWord ++ tailWord_807484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807499 : List Nat := [1, 1, 1, 1, 3, 1, 7, 1, 1, 5]
def baseStart_807499 : Nat := 118140960795 + 807499 * 2 ^ 59
def prefixEnd_807499 : Nat := 4983230072969 + 3 ^ 40 * 807499 * 2
def baseEnd_807499 : Nat := 276423410016694260099257

theorem tailTrace_807499 : CollatzResearch.WordTrace tailWord_807499 prefixEnd_807499 276423410016694260099257 := by
  unfold tailWord_807499
  simp only [CollatzResearch.WordTrace]
  refine ⟨29451908101576507694745551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19634605401051005129830367 29451908101576507694745551)
  ·
    refine ⟨44177862152364761542118327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29451908101576507694745551 44177862152364761542118327)
    ·
      refine ⟨66266793228547142313177491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44177862152364761542118327 66266793228547142313177491)
      ·
        refine ⟨99400189842820713469766237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66266793228547142313177491 99400189842820713469766237)
        ·
          refine ⟨37275071191057767551162339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99400189842820713469766237 37275071191057767551162339)
          ·
            refine ⟨55912606786586651326743509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37275071191057767551162339 55912606786586651326743509)
            ·
              refine ⟨1310451721560624640470551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 55912606786586651326743509 1310451721560624640470551)
              ·
                refine ⟨1965677582340936960705827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1310451721560624640470551 1965677582340936960705827)
                ·
                  refine ⟨2948516373511405441058741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1965677582340936960705827 2948516373511405441058741)
                  ·
                    refine ⟨276423410016694260099257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2948516373511405441058741 276423410016694260099257)
                    ·
                      rfl

theorem cell22_807499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 1, 1, 5].length) (baseStart_807499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_807499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_807499 prefixEnd_807499 := by exact prefixLift 807499
  have htrace : WordTrace (prefixWord ++ tailWord_807499) baseStart_807499 baseEnd_807499 := by
    simpa [prefixWord, tailWord_807499, baseEnd_807499] using wordTrace_append hprefix tailTrace_807499
  have hstable : (prefixWord ++ tailWord_807499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807499).length < 2 ^ (prefixWord ++ tailWord_807499).sum := by decide
  have hdescent : baseEnd_807499 < baseStart_807499 := by decide
  rcases family_descends (prefixWord ++ tailWord_807499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807501 : List Nat := [1, 6, 1, 1, 2, 1, 2, 2, 6]
def baseStart_807501 : Nat := 118140960795 + 807501 * 2 ^ 59
def prefixEnd_807501 : Nat := 4983230072969 + 3 ^ 40 * 807501 * 2
def baseEnd_807501 : Nat := 92141364885855640516417

theorem tailTrace_807501 : CollatzResearch.WordTrace tailWord_807501 prefixEnd_807501 92141364885855640516417 := by
  unfold tailWord_807501
  simp only [CollatzResearch.WordTrace]
  refine ⟨29451981047569262036318357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19634654031712841357545571 29451981047569262036318357)
  ·
    refine ⟨1380561611604809157952423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 29451981047569262036318357 1380561611604809157952423)
    ·
      refine ⟨2070842417407213736928635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1380561611604809157952423 2070842417407213736928635)
      ·
        refine ⟨3106263626110820605392953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2070842417407213736928635 3106263626110820605392953)
        ·
          refine ⟨2329697719583115454044715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3106263626110820605392953 2329697719583115454044715)
          ·
            refine ⟨3494546579374673181067073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2329697719583115454044715 3494546579374673181067073)
            ·
              refine ⟨2620909934531004885800305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3494546579374673181067073 2620909934531004885800305)
              ·
                refine ⟨1965682450898253664350229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2620909934531004885800305 1965682450898253664350229)
                ·
                  refine ⟨92141364885855640516417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1965682450898253664350229 92141364885855640516417)
                  ·
                    rfl

theorem cell22_807501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_807501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_807501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_807501 prefixEnd_807501 := by exact prefixLift 807501
  have htrace : WordTrace (prefixWord ++ tailWord_807501) baseStart_807501 baseEnd_807501 := by
    simpa [prefixWord, tailWord_807501, baseEnd_807501] using wordTrace_append hprefix tailTrace_807501
  have hstable : (prefixWord ++ tailWord_807501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807501).length < 2 ^ (prefixWord ++ tailWord_807501).sum := by decide
  have hdescent : baseEnd_807501 < baseStart_807501 := by decide
  rcases family_descends (prefixWord ++ tailWord_807501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807554 : List Nat := [3, 4, 3, 1, 1, 2, 1, 2, 1, 4]
def baseStart_807554 : Nat := 118140960795 + 807554 * 2 ^ 59
def prefixEnd_807554 : Nat := 4983230072969 + 3 ^ 40 * 807554 * 2
def baseEnd_807554 : Nat := 276442237640692449974089

theorem tailTrace_807554 : CollatzResearch.WordTrace tailWord_807554 prefixEnd_807554 276442237640692449974089 := by
  unfold tailWord_807554
  simp only [CollatzResearch.WordTrace]
  refine ⟨7363478529094313021999429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19635942744251501391998477 7363478529094313021999429)
  ·
    refine ⟨1380652224205183691624893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7363478529094313021999429 1380652224205183691624893)
    ·
      refine ⟨517744584076943884359335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1380652224205183691624893 517744584076943884359335)
      ·
        refine ⟨776616876115415826539003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 517744584076943884359335 776616876115415826539003)
        ·
          refine ⟨1164925314173123739808505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 776616876115415826539003 1164925314173123739808505)
          ·
            refine ⟨873693985629842804856379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1164925314173123739808505 873693985629842804856379)
            ·
              refine ⟨1310540978444764207284569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 873693985629842804856379 1310540978444764207284569)
              ·
                refine ⟨982905733833573155463427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1310540978444764207284569 982905733833573155463427)
                ·
                  refine ⟨1474358600750359733195141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 982905733833573155463427 1474358600750359733195141)
                  ·
                    refine ⟨276442237640692449974089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1474358600750359733195141 276442237640692449974089)
                    ·
                      rfl

theorem cell22_807554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_807554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_807554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_807554 prefixEnd_807554 := by exact prefixLift 807554
  have htrace : WordTrace (prefixWord ++ tailWord_807554) baseStart_807554 baseEnd_807554 := by
    simpa [prefixWord, tailWord_807554, baseEnd_807554] using wordTrace_append hprefix tailTrace_807554
  have hstable : (prefixWord ++ tailWord_807554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807554).length < 2 ^ (prefixWord ++ tailWord_807554).sum := by decide
  have hdescent : baseEnd_807554 < baseStart_807554 := by decide
  rcases family_descends (prefixWord ++ tailWord_807554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807589 : List Nat := [1, 3, 1, 2, 1, 2, 1, 4, 2, 5]
def baseStart_807589 : Nat := 118140960795 + 807589 * 2 ^ 59
def prefixEnd_807589 : Nat := 4983230072969 + 3 ^ 40 * 807589 * 2
def baseEnd_807589 : Nat := 276454218855964025348981

theorem tailTrace_807589 : CollatzResearch.WordTrace tailWord_807589 prefixEnd_807589 276454218855964025348981 := by
  unfold tailWord_807589
  simp only [CollatzResearch.WordTrace]
  refine ⟨29455190671250453065521821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19636793780833635377014547 29455190671250453065521821)
  ·
    refine ⟨11045696501718919899570683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29455190671250453065521821 11045696501718919899570683)
    ·
      refine ⟨16568544752578379849356025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11045696501718919899570683 16568544752578379849356025)
      ·
        refine ⟨12426408564433784887017019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16568544752578379849356025 12426408564433784887017019)
        ·
          refine ⟨18639612846650677330525529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12426408564433784887017019 18639612846650677330525529)
          ·
            refine ⟨13979709634988007997894147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18639612846650677330525529 13979709634988007997894147)
            ·
              refine ⟨20969564452482011996841221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13979709634988007997894147 20969564452482011996841221)
              ·
                refine ⟨3931793334840377249407729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20969564452482011996841221 3931793334840377249407729)
                ·
                  refine ⟨2948845001130282937055797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3931793334840377249407729 2948845001130282937055797)
                  ·
                    refine ⟨276454218855964025348981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2948845001130282937055797 276454218855964025348981)
                    ·
                      rfl

theorem cell22_807589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4, 2, 5].length) (baseStart_807589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_807589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_807589 prefixEnd_807589 := by exact prefixLift 807589
  have htrace : WordTrace (prefixWord ++ tailWord_807589) baseStart_807589 baseEnd_807589 := by
    simpa [prefixWord, tailWord_807589, baseEnd_807589] using wordTrace_append hprefix tailTrace_807589
  have hstable : (prefixWord ++ tailWord_807589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807589).length < 2 ^ (prefixWord ++ tailWord_807589).sum := by decide
  have hdescent : baseEnd_807589 < baseStart_807589 := by decide
  rcases family_descends (prefixWord ++ tailWord_807589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807629 : List Nat := [1, 6, 2, 1, 2, 1, 2, 3, 1, 3]
def baseStart_807629 : Nat := 118140960795 + 807629 * 2 ^ 59
def prefixEnd_807629 : Nat := 4983230072969 + 3 ^ 40 * 807629 * 2
def baseEnd_807629 : Nat := 276467911673417254348859

theorem tailTrace_807629 : CollatzResearch.WordTrace tailWord_807629 prefixEnd_807629 276467911673417254348859 := by
  unfold tailWord_807629
  simp only [CollatzResearch.WordTrace]
  refine ⟨29456649591105539896977941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19637766394070359931318627 29456649591105539896977941)
  ·
    refine ⟨1380780449583072182670841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 29456649591105539896977941 1380780449583072182670841)
    ·
      refine ⟨1035585337187304137003131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1380780449583072182670841 1035585337187304137003131)
      ·
        refine ⟨1553378005780956205504697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1035585337187304137003131 1553378005780956205504697)
        ·
          refine ⟨1165033504335717154128523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1553378005780956205504697 1165033504335717154128523)
          ·
            refine ⟨1747550256503575731192785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1165033504335717154128523 1747550256503575731192785)
            ·
              refine ⟨1310662692377681798394589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1747550256503575731192785 1310662692377681798394589)
              ·
                refine ⟨491498509641630674397971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1310662692377681798394589 491498509641630674397971)
                ·
                  refine ⟨737247764462446011596957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 491498509641630674397971 737247764462446011596957)
                  ·
                    refine ⟨276467911673417254348859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 737247764462446011596957 276467911673417254348859)
                    ·
                      rfl

theorem cell22_807629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_807629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_807629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_807629 prefixEnd_807629 := by exact prefixLift 807629
  have htrace : WordTrace (prefixWord ++ tailWord_807629) baseStart_807629 baseEnd_807629 := by
    simpa [prefixWord, tailWord_807629, baseEnd_807629] using wordTrace_append hprefix tailTrace_807629
  have hstable : (prefixWord ++ tailWord_807629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807629).length < 2 ^ (prefixWord ++ tailWord_807629).sum := by decide
  have hdescent : baseEnd_807629 < baseStart_807629 := by decide
  rcases family_descends (prefixWord ++ tailWord_807629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807653 : List Nat := [1, 3, 1, 4, 1, 2, 2, 4, 4]
def baseStart_807653 : Nat := 118140960795 + 807653 * 2 ^ 59
def prefixEnd_807653 : Nat := 4983230072969 + 3 ^ 40 * 807653 * 2
def baseEnd_807653 : Nat := 92158709121296397249595

theorem tailTrace_807653 : CollatzResearch.WordTrace tailWord_807653 prefixEnd_807653 92158709121296397249595 := by
  unfold tailWord_807653
  simp only [CollatzResearch.WordTrace]
  refine ⟨29457524943018591995851613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19638349962012394663901075 29457524943018591995851613)
  ·
    refine ⟨11046571853631971998444355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29457524943018591995851613 11046571853631971998444355)
    ·
      refine ⟨16569857780447957997666533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11046571853631971998444355 16569857780447957997666533)
      ·
        refine ⟨3106848333833992124562475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16569857780447957997666533 3106848333833992124562475)
        ·
          refine ⟨4660272500750988186843713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3106848333833992124562475 4660272500750988186843713)
          ·
            refine ⟨3495204375563241140132785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4660272500750988186843713 3495204375563241140132785)
            ·
              refine ⟨2621403281672430855099589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3495204375563241140132785 2621403281672430855099589)
              ·
                refine ⟨491513115313580785331173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2621403281672430855099589 491513115313580785331173)
                ·
                  refine ⟨92158709121296397249595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 491513115313580785331173 92158709121296397249595)
                  ·
                    rfl

theorem cell22_807653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 4, 4].length) (baseStart_807653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_807653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_807653 prefixEnd_807653 := by exact prefixLift 807653
  have htrace : WordTrace (prefixWord ++ tailWord_807653) baseStart_807653 baseEnd_807653 := by
    simpa [prefixWord, tailWord_807653, baseEnd_807653] using wordTrace_append hprefix tailTrace_807653
  have hstable : (prefixWord ++ tailWord_807653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807653).length < 2 ^ (prefixWord ++ tailWord_807653).sum := by decide
  have hdescent : baseEnd_807653 < baseStart_807653 := by decide
  rcases family_descends (prefixWord ++ tailWord_807653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807664 : List Nat := [2, 1, 1, 1, 3, 1, 4, 9]
def baseStart_807664 : Nat := 118140960795 + 807664 * 2 ^ 59
def prefixEnd_807664 : Nat := 4983230072969 + 3 ^ 40 * 807664 * 2
def baseEnd_807664 : Nat := 30719988098743203302639

theorem tailTrace_807664 : CollatzResearch.WordTrace tailWord_807664 prefixEnd_807664 30719988098743203302639 := by
  unfold tailWord_807664
  simp only [CollatzResearch.WordTrace]
  refine ⟨14728963072989370437251023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19638617430652493916334697 14728963072989370437251023)
  ·
    refine ⟨22093444609484055655876535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14728963072989370437251023 22093444609484055655876535)
    ·
      refine ⟨33140166914226083483814803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22093444609484055655876535 33140166914226083483814803)
      ·
        refine ⟨49710250371339125225722205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33140166914226083483814803 49710250371339125225722205)
        ·
          refine ⟨18641343889252171959645827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49710250371339125225722205 18641343889252171959645827)
          ·
            refine ⟨27962015833878257939468741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18641343889252171959645827 27962015833878257939468741)
            ·
              refine ⟨5242877968852173363650389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27962015833878257939468741 5242877968852173363650389)
              ·
                refine ⟨30719988098743203302639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5242877968852173363650389 30719988098743203302639)
                ·
                  rfl

theorem cell22_807664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 9].length) (baseStart_807664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_807664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_807664 prefixEnd_807664 := by exact prefixLift 807664
  have htrace : WordTrace (prefixWord ++ tailWord_807664) baseStart_807664 baseEnd_807664 := by
    simpa [prefixWord, tailWord_807664, baseEnd_807664] using wordTrace_append hprefix tailTrace_807664
  have hstable : (prefixWord ++ tailWord_807664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807664).length < 2 ^ (prefixWord ++ tailWord_807664).sum := by decide
  have hdescent : baseEnd_807664 < baseStart_807664 := by decide
  rcases family_descends (prefixWord ++ tailWord_807664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807666 : List Nat := [3, 2, 1, 3, 1, 2, 1, 2, 1, 6]
def baseStart_807666 : Nat := 118140960795 + 807666 * 2 ^ 59
def prefixEnd_807666 : Nat := 4983230072969 + 3 ^ 40 * 807666 * 2
def baseEnd_807666 : Nat := 276480577529561491173745

theorem tailTrace_807666 : CollatzResearch.WordTrace tailWord_807666 prefixEnd_807666 276480577529561491173745 := by
  unfold tailWord_807666
  simp only [CollatzResearch.WordTrace]
  refine ⟨7364499772992873804018713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19638666061314330144049901 7364499772992873804018713)
  ·
    refine ⟨5523374829744655353014035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7364499772992873804018713 5523374829744655353014035)
    ·
      refine ⟨8285062244616983029521053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5523374829744655353014035 8285062244616983029521053)
      ·
        refine ⟨3106898341731368636070395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8285062244616983029521053 3106898341731368636070395)
        ·
          refine ⟨4660347512597052954105593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3106898341731368636070395 4660347512597052954105593)
          ·
            refine ⟨3495260634447789715579195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4660347512597052954105593 3495260634447789715579195)
            ·
              refine ⟨5242890951671684573368793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3495260634447789715579195 5242890951671684573368793)
              ·
                refine ⟨3932168213753763430026595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5242890951671684573368793 3932168213753763430026595)
                ·
                  refine ⟨5898252320630645145039893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3932168213753763430026595 5898252320630645145039893)
                  ·
                    refine ⟨276480577529561491173745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5898252320630645145039893 276480577529561491173745)
                    ·
                      rfl

theorem cell22_807666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 2, 1, 6].length) (baseStart_807666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_807666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_807666 prefixEnd_807666 := by exact prefixLift 807666
  have htrace : WordTrace (prefixWord ++ tailWord_807666) baseStart_807666 baseEnd_807666 := by
    simpa [prefixWord, tailWord_807666, baseEnd_807666] using wordTrace_append hprefix tailTrace_807666
  have hstable : (prefixWord ++ tailWord_807666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807666).length < 2 ^ (prefixWord ++ tailWord_807666).sum := by decide
  have hdescent : baseEnd_807666 < baseStart_807666 := by decide
  rcases family_descends (prefixWord ++ tailWord_807666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807679 : List Nat := [1, 1, 2, 2, 1, 3, 1, 1, 1, 9]
def baseStart_807679 : Nat := 118140960795 + 807679 * 2 ^ 59
def prefixEnd_807679 : Nat := 4983230072969 + 3 ^ 40 * 807679 * 2
def baseEnd_807679 : Nat := 276485027695233790598705

theorem tailTrace_807679 : CollatzResearch.WordTrace tailWord_807679 prefixEnd_807679 276485027695233790598705 := by
  unfold tailWord_807679
  simp only [CollatzResearch.WordTrace]
  refine ⟨29458473240924398436298091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19638982160616265624198727 29458473240924398436298091)
  ·
    refine ⟨44187709861386597654447137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29458473240924398436298091 44187709861386597654447137)
    ·
      refine ⟨33140782396039948240835353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44187709861386597654447137 33140782396039948240835353)
      ·
        refine ⟨24855586797029961180626515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33140782396039948240835353 24855586797029961180626515)
        ·
          refine ⟨37283380195544941770939773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24855586797029961180626515 37283380195544941770939773)
          ·
            refine ⟨13981267573329353164102415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37283380195544941770939773 13981267573329353164102415)
            ·
              refine ⟨20971901359994029746153623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13981267573329353164102415 20971901359994029746153623)
              ·
                refine ⟨31457852039991044619230435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20971901359994029746153623 31457852039991044619230435)
                ·
                  refine ⟨47186778059986566928845653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31457852039991044619230435 47186778059986566928845653)
                  ·
                    refine ⟨276485027695233790598705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 47186778059986566928845653 276485027695233790598705)
                    ·
                      rfl

theorem cell22_807679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 9].length) (baseStart_807679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_807679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_807679 prefixEnd_807679 := by exact prefixLift 807679
  have htrace : WordTrace (prefixWord ++ tailWord_807679) baseStart_807679 baseEnd_807679 := by
    simpa [prefixWord, tailWord_807679, baseEnd_807679] using wordTrace_append hprefix tailTrace_807679
  have hstable : (prefixWord ++ tailWord_807679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807679).length < 2 ^ (prefixWord ++ tailWord_807679).sum := by decide
  have hdescent : baseEnd_807679 < baseStart_807679 := by decide
  rcases family_descends (prefixWord ++ tailWord_807679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807820 : List Nat := [2, 2, 1, 2, 1, 2, 5, 2, 2, 3]
def baseStart_807820 : Nat := 118140960795 + 807820 * 2 ^ 59
def prefixEnd_807820 : Nat := 4983230072969 + 3 ^ 40 * 807820 * 2
def baseEnd_807820 : Nat := 276533294876756422823273

theorem tailTrace_807820 : CollatzResearch.WordTrace tailWord_807820 prefixEnd_807820 276533294876756422823273 := by
  unfold tailWord_807820
  simp only [CollatzResearch.WordTrace]
  refine ⟨14731807966706789758590457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19642410622275719678120609 14731807966706789758590457)
  ·
    refine ⟨11048855975030092318942843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14731807966706789758590457 11048855975030092318942843)
    ·
      refine ⟨16573283962545138478414265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11048855975030092318942843 16573283962545138478414265)
      ·
        refine ⟨12429962971908853858810699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16573283962545138478414265 12429962971908853858810699)
        ·
          refine ⟨18644944457863280788216049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12429962971908853858810699 18644944457863280788216049)
          ·
            refine ⟨13983708343397460591162037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18644944457863280788216049 13983708343397460591162037)
            ·
              refine ⟨1310972657193511930421441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13983708343397460591162037 1310972657193511930421441)
              ·
                refine ⟨983229492895133947816081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1310972657193511930421441 983229492895133947816081)
                ·
                  refine ⟨737422119671350460862061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 983229492895133947816081 737422119671350460862061)
                  ·
                    refine ⟨276533294876756422823273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 737422119671350460862061 276533294876756422823273)
                    ·
                      rfl

theorem cell22_807820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 2, 2, 3].length) (baseStart_807820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_807820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_807820 prefixEnd_807820 := by exact prefixLift 807820
  have htrace : WordTrace (prefixWord ++ tailWord_807820) baseStart_807820 baseEnd_807820 := by
    simpa [prefixWord, tailWord_807820, baseEnd_807820] using wordTrace_append hprefix tailTrace_807820
  have hstable : (prefixWord ++ tailWord_807820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807820).length < 2 ^ (prefixWord ++ tailWord_807820).sum := by decide
  have hdescent : baseEnd_807820 < baseStart_807820 := by decide
  rcases family_descends (prefixWord ++ tailWord_807820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807837 : List Nat := [1, 4, 2, 1, 2, 1, 5, 1, 2, 3]
def baseStart_807837 : Nat := 118140960795 + 807837 * 2 ^ 59
def prefixEnd_807837 : Nat := 4983230072969 + 3 ^ 40 * 807837 * 2
def baseEnd_807837 : Nat := 276539114324174045148221

theorem tailTrace_807837 : CollatzResearch.WordTrace tailWord_807837 prefixEnd_807837 276539114324174045148221 := by
  unfold tailWord_807837
  simp only [CollatzResearch.WordTrace]
  refine ⟨29464235974351991420549765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19642823982901327613699843 29464235974351991420549765)
  ·
    refine ⟨5524544245190998391353081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29464235974351991420549765 5524544245190998391353081)
    ·
      refine ⟨4143408183893248793514811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5524544245190998391353081 4143408183893248793514811)
      ·
        refine ⟨6215112275839873190272217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4143408183893248793514811 6215112275839873190272217)
        ·
          refine ⟨4661334206879904892704163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6215112275839873190272217 4661334206879904892704163)
          ·
            refine ⟨6992001310319857339056245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4661334206879904892704163 6992001310319857339056245)
            ·
              refine ⟨655500122842486625536523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6992001310319857339056245 655500122842486625536523)
              ·
                refine ⟨983250184263729938304785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 655500122842486625536523 983250184263729938304785)
                ·
                  refine ⟨737437638197797453728589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 983250184263729938304785 737437638197797453728589)
                  ·
                    refine ⟨276539114324174045148221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 737437638197797453728589 276539114324174045148221)
                    ·
                      rfl

theorem cell22_807837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 5, 1, 2, 3].length) (baseStart_807837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_807837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_807837 prefixEnd_807837 := by exact prefixLift 807837
  have htrace : WordTrace (prefixWord ++ tailWord_807837) baseStart_807837 baseEnd_807837 := by
    simpa [prefixWord, tailWord_807837, baseEnd_807837] using wordTrace_append hprefix tailTrace_807837
  have hstable : (prefixWord ++ tailWord_807837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807837).length < 2 ^ (prefixWord ++ tailWord_807837).sum := by decide
  have hdescent : baseEnd_807837 < baseStart_807837 := by decide
  rcases family_descends (prefixWord ++ tailWord_807837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807953 : List Nat := [1, 2, 2, 1, 1, 2, 1, 4, 4, 4]
def baseStart_807953 : Nat := 118140960795 + 807953 * 2 ^ 59
def prefixEnd_807953 : Nat := 4983230072969 + 3 ^ 40 * 807953 * 2
def baseEnd_807953 : Nat := 276578823494788409247865

theorem tailTrace_807953 : CollatzResearch.WordTrace tailWord_807953 prefixEnd_807953 276578823494788409247865 := by
  unfold tailWord_807953
  simp only [CollatzResearch.WordTrace]
  refine ⟨29468466841931743231772513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19645644561287828821181675 29468466841931743231772513)
  ·
    refine ⟨22101350131448807423829385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29468466841931743231772513 22101350131448807423829385)
    ·
      refine ⟨16576012598586605567872039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22101350131448807423829385 16576012598586605567872039)
      ·
        refine ⟨24864018897879908351808059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16576012598586605567872039 24864018897879908351808059)
        ·
          refine ⟨37296028346819862527712089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24864018897879908351808059 37296028346819862527712089)
          ·
            refine ⟨27972021260114896895784067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37296028346819862527712089 27972021260114896895784067)
            ·
              refine ⟨41958031890172345343676101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27972021260114896895784067 41958031890172345343676101)
              ·
                refine ⟨7867130979407314751939269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41958031890172345343676101 7867130979407314751939269)
                ·
                  refine ⟨1475087058638871515988613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7867130979407314751939269 1475087058638871515988613)
                  ·
                    refine ⟨276578823494788409247865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1475087058638871515988613 276578823494788409247865)
                    ·
                      rfl

theorem cell22_807953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 4].length) (baseStart_807953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_807953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_807953 prefixEnd_807953 := by exact prefixLift 807953
  have htrace : WordTrace (prefixWord ++ tailWord_807953) baseStart_807953 baseEnd_807953 := by
    simpa [prefixWord, tailWord_807953, baseEnd_807953] using wordTrace_append hprefix tailTrace_807953
  have hstable : (prefixWord ++ tailWord_807953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807953).length < 2 ^ (prefixWord ++ tailWord_807953).sum := by decide
  have hdescent : baseEnd_807953 < baseStart_807953 := by decide
  rcases family_descends (prefixWord ++ tailWord_807953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_807970 : List Nat := [3, 3, 1, 1, 1, 4, 1, 1, 1, 6]
def baseStart_807970 : Nat := 118140960795 + 807970 * 2 ^ 59
def prefixEnd_807970 : Nat := 4983230072969 + 3 ^ 40 * 807970 * 2
def baseEnd_807970 : Nat := 276584642942206031572813

theorem tailTrace_807970 : CollatzResearch.WordTrace tailWord_807970 prefixEnd_807970 276584642942206031572813 := by
  unfold tailWord_807970
  simp only [CollatzResearch.WordTrace]
  refine ⟨7367271720717538783785341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19646057921913436756760909 7367271720717538783785341)
  ·
    refine ⟨2762726895269077043919503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7367271720717538783785341 2762726895269077043919503)
    ·
      refine ⟨4144090342903615565879255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2762726895269077043919503 4144090342903615565879255)
      ·
        refine ⟨6216135514355423348818883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4144090342903615565879255 6216135514355423348818883)
        ·
          refine ⟨9324203271533135023228325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6216135514355423348818883 9324203271533135023228325)
          ·
            refine ⟨1748288113412462816855311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9324203271533135023228325 1748288113412462816855311)
            ·
              refine ⟨2622432170118694225282967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1748288113412462816855311 2622432170118694225282967)
              ·
                refine ⟨3933648255178041337924451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2622432170118694225282967 3933648255178041337924451)
                ·
                  refine ⟨5900472382767062006886677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3933648255178041337924451 5900472382767062006886677)
                  ·
                    refine ⟨276584642942206031572813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5900472382767062006886677 276584642942206031572813)
                    ·
                      rfl

theorem cell22_807970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_807970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_807970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_807970 prefixEnd_807970 := by exact prefixLift 807970
  have htrace : WordTrace (prefixWord ++ tailWord_807970) baseStart_807970 baseEnd_807970 := by
    simpa [prefixWord, tailWord_807970, baseEnd_807970] using wordTrace_append hprefix tailTrace_807970
  have hstable : (prefixWord ++ tailWord_807970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_807970).length < 2 ^ (prefixWord ++ tailWord_807970).sum := by decide
  have hdescent : baseEnd_807970 < baseStart_807970 := by decide
  rcases family_descends (prefixWord ++ tailWord_807970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808060 : List Nat := [2, 2, 2, 1, 1, 3, 2, 2, 3, 4]
def baseStart_808060 : Nat := 118140960795 + 808060 * 2 ^ 59
def prefixEnd_808060 : Nat := 4983230072969 + 3 ^ 40 * 808060 * 2
def baseEnd_808060 : Nat := 276615451781475796822537

theorem tailTrace_808060 : CollatzResearch.WordTrace tailWord_808060 prefixEnd_808060 276615451781475796822537 := by
  unfold tailWord_808060
  simp only [CollatzResearch.WordTrace]
  refine ⟨14736184726272050252958817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19648246301696067003945089 14736184726272050252958817)
  ·
    refine ⟨11052138544704037689719113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14736184726272050252958817 11052138544704037689719113)
    ·
      refine ⟨8289103908528028267289335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11052138544704037689719113 8289103908528028267289335)
      ·
        refine ⟨12433655862792042400934003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8289103908528028267289335 12433655862792042400934003)
        ·
          refine ⟨18650483794188063601401005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12433655862792042400934003 18650483794188063601401005)
          ·
            refine ⟨6993931422820523850525377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18650483794188063601401005 6993931422820523850525377)
            ·
              refine ⟨5245448567115392887894033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6993931422820523850525377 5245448567115392887894033)
              ·
                refine ⟨3934086425336544665920525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5245448567115392887894033 3934086425336544665920525)
                ·
                  refine ⟨1475282409501204249720197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3934086425336544665920525 1475282409501204249720197)
                  ·
                    refine ⟨276615451781475796822537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1475282409501204249720197 276615451781475796822537)
                    ·
                      rfl

theorem cell22_808060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2, 3, 4].length) (baseStart_808060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_808060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_808060 prefixEnd_808060 := by exact prefixLift 808060
  have htrace : WordTrace (prefixWord ++ tailWord_808060) baseStart_808060 baseEnd_808060 := by
    simpa [prefixWord, tailWord_808060, baseEnd_808060] using wordTrace_append hprefix tailTrace_808060
  have hstable : (prefixWord ++ tailWord_808060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808060).length < 2 ^ (prefixWord ++ tailWord_808060).sum := by decide
  have hdescent : baseEnd_808060 < baseStart_808060 := by decide
  rcases family_descends (prefixWord ++ tailWord_808060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808124 : List Nat := [2, 2, 2, 3, 2, 1, 2, 3, 2, 3]
def baseStart_808124 : Nat := 118140960795 + 808124 * 2 ^ 59
def prefixEnd_808124 : Nat := 4983230072969 + 3 ^ 40 * 808124 * 2
def baseEnd_808124 : Nat := 276637360289400963222341

theorem tailTrace_808124 : CollatzResearch.WordTrace tailWord_808124 prefixEnd_808124 276637360289400963222341 := by
  unfold tailWord_808124
  simp only [CollatzResearch.WordTrace]
  refine ⟨14737351862156119718123713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19649802482874826290831617 14737351862156119718123713)
  ·
    refine ⟨11053013896617089788592785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14737351862156119718123713 11053013896617089788592785)
    ·
      refine ⟨8289760422462817341444589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11053013896617089788592785 8289760422462817341444589)
      ·
        refine ⟨3108660158423556503041721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8289760422462817341444589 3108660158423556503041721)
        ·
          refine ⟨2331495118817667377281291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3108660158423556503041721 2331495118817667377281291)
          ·
            refine ⟨3497242678226501065921937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2331495118817667377281291 3497242678226501065921937)
            ·
              refine ⟨2622932008669875799441453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3497242678226501065921937 2622932008669875799441453)
              ·
                refine ⟨983599503251203424790545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2622932008669875799441453 983599503251203424790545)
                ·
                  refine ⟨737699627438402568592909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 983599503251203424790545 737699627438402568592909)
                  ·
                    refine ⟨276637360289400963222341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 737699627438402568592909 276637360289400963222341)
                    ·
                      rfl

theorem cell22_808124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 3, 2, 3].length) (baseStart_808124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_808124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_808124 prefixEnd_808124 := by exact prefixLift 808124
  have htrace : WordTrace (prefixWord ++ tailWord_808124) baseStart_808124 baseEnd_808124 := by
    simpa [prefixWord, tailWord_808124, baseEnd_808124] using wordTrace_append hprefix tailTrace_808124
  have hstable : (prefixWord ++ tailWord_808124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808124).length < 2 ^ (prefixWord ++ tailWord_808124).sum := by decide
  have hdescent : baseEnd_808124 < baseStart_808124 := by decide
  rcases family_descends (prefixWord ++ tailWord_808124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_808227 : List Nat := [1, 1, 1, 4, 2, 3, 3, 1, 6]
def baseStart_808227 : Nat := 118140960795 + 808227 * 2 ^ 59
def prefixEnd_808227 : Nat := 4983230072969 + 3 ^ 40 * 808227 * 2
def baseEnd_808227 : Nat := 92224206431447675965675

theorem tailTrace_808227 : CollatzResearch.WordTrace tailWord_808227 prefixEnd_808227 92224206431447675965675 := by
  unfold tailWord_808227
  simp only [CollatzResearch.WordTrace]
  refine ⟨29478460442939088027246935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19652306961959392018164623 29478460442939088027246935)
  ·
    refine ⟨44217690664408632040870403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29478460442939088027246935 44217690664408632040870403)
    ·
      refine ⟨66326535996612948061305605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44217690664408632040870403 66326535996612948061305605)
      ·
        refine ⟨12436225499364927761494801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66326535996612948061305605 12436225499364927761494801)
        ·
          refine ⟨9327169124523695821121101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12436225499364927761494801 9327169124523695821121101)
          ·
            refine ⟨3497688421696385932920413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9327169124523695821121101 3497688421696385932920413)
            ·
              refine ⟨1311633158136144724845155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3497688421696385932920413 1311633158136144724845155)
              ·
                refine ⟨1967449737204217087267733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1311633158136144724845155 1967449737204217087267733)
                ·
                  refine ⟨92224206431447675965675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1967449737204217087267733 92224206431447675965675)
                  ·
                    rfl

theorem cell22_808227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 1, 6].length) (baseStart_808227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_808227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_808227 prefixEnd_808227 := by exact prefixLift 808227
  have htrace : WordTrace (prefixWord ++ tailWord_808227) baseStart_808227 baseEnd_808227 := by
    simpa [prefixWord, tailWord_808227, baseEnd_808227] using wordTrace_append hprefix tailTrace_808227
  have hstable : (prefixWord ++ tailWord_808227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_808227).length < 2 ^ (prefixWord ++ tailWord_808227).sum := by decide
  have hdescent : baseEnd_808227 < baseStart_808227 := by decide
  rcases family_descends (prefixWord ++ tailWord_808227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
