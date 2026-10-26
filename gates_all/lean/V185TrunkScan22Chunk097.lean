import V185TrunkScan22Chunk096

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_869054 : List Nat := [4, 2, 1, 1, 2, 1, 4, 2, 1, 4]
def baseStart_869054 : Nat := 118140960795 + 869054 * 2 ^ 59
def prefixEnd_869054 : Nat := 4983230072969 + 3 ^ 40 * 869054 * 2
def baseEnd_869054 : Nat := 297494944475032037285533

theorem tailTrace_869054 : CollatzResearch.WordTrace tailWord_869054 prefixEnd_869054 297494944475032037285533 := by
  unfold tailWord_869054
  simp only [CollatzResearch.WordTrace]
  refine ⟨3962125424196656931472777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21131335595715503634521477 3962125424196656931472777)
  ·
    refine ⟨2971594068147492698604583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3962125424196656931472777 2971594068147492698604583)
    ·
      refine ⟨4457391102221239047906875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2971594068147492698604583 4457391102221239047906875)
      ·
        refine ⟨6686086653331858571860313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4457391102221239047906875 6686086653331858571860313)
        ·
          refine ⟨5014564989998893928895235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6686086653331858571860313 5014564989998893928895235)
          ·
            refine ⟨7521847484998340893342853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5014564989998893928895235 7521847484998340893342853)
            ·
              refine ⟨1410346403437188917501785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7521847484998340893342853 1410346403437188917501785)
              ·
                refine ⟨1057759802577891688126339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1410346403437188917501785 1057759802577891688126339)
                ·
                  refine ⟨1586639703866837532189509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1057759802577891688126339 1586639703866837532189509)
                  ·
                    refine ⟨297494944475032037285533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1586639703866837532189509 297494944475032037285533)
                    ·
                      rfl

theorem cell22_869054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_869054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_869054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_869054 prefixEnd_869054 := by exact prefixLift 869054
  have htrace : WordTrace (prefixWord ++ tailWord_869054) baseStart_869054 baseEnd_869054 := by
    simpa [prefixWord, tailWord_869054, baseEnd_869054] using wordTrace_append hprefix tailTrace_869054
  have hstable : (prefixWord ++ tailWord_869054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869054).length < 2 ^ (prefixWord ++ tailWord_869054).sum := by decide
  have hdescent : baseEnd_869054 < baseStart_869054 := by decide
  rcases family_descends (prefixWord ++ tailWord_869054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869062 : List Nat := [6, 1, 2, 1, 2, 2, 1, 3, 1, 3]
def baseStart_869062 : Nat := 118140960795 + 869062 * 2 ^ 59
def prefixEnd_869062 : Nat := 4983230072969 + 3 ^ 40 * 869062 * 2
def baseEnd_869062 : Nat := 297497683038522683085509

theorem tailTrace_869062 : CollatzResearch.WordTrace tailWord_869062 prefixEnd_869062 297497683038522683085509 := by
  unfold tailWord_869062
  simp only [CollatzResearch.WordTrace]
  refine ⟨990540474298258525564795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 21131530118362848545382293 990540474298258525564795)
  ·
    refine ⟨1485810711447387788347193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 990540474298258525564795 1485810711447387788347193)
    ·
      refine ⟨1114358033585540841260395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1485810711447387788347193 1114358033585540841260395)
      ·
        refine ⟨1671537050378311261890593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1114358033585540841260395 1671537050378311261890593)
        ·
          refine ⟨1253652787783733446417945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1671537050378311261890593 1253652787783733446417945)
          ·
            refine ⟨940239590837800084813459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1253652787783733446417945 940239590837800084813459)
            ·
              refine ⟨1410359386256700127220189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 940239590837800084813459 1410359386256700127220189)
              ·
                refine ⟨528884769846262547707571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1410359386256700127220189 528884769846262547707571)
                ·
                  refine ⟨793327154769393821561357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 528884769846262547707571 793327154769393821561357)
                  ·
                    refine ⟨297497683038522683085509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 793327154769393821561357 297497683038522683085509)
                    ·
                      rfl

theorem cell22_869062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_869062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_869062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_869062 prefixEnd_869062 := by exact prefixLift 869062
  have htrace : WordTrace (prefixWord ++ tailWord_869062) baseStart_869062 baseEnd_869062 := by
    simpa [prefixWord, tailWord_869062, baseEnd_869062] using wordTrace_append hprefix tailTrace_869062
  have hstable : (prefixWord ++ tailWord_869062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869062).length < 2 ^ (prefixWord ++ tailWord_869062).sum := by decide
  have hdescent : baseEnd_869062 < baseStart_869062 := by decide
  rcases family_descends (prefixWord ++ tailWord_869062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869065 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 8, 4]
def baseStart_869065 : Nat := 118140960795 + 869065 * 2 ^ 59
def prefixEnd_869065 : Nat := 4983230072969 + 3 ^ 40 * 869065 * 2
def baseEnd_869065 : Nat := 297498709999831675260499

theorem tailTrace_869065 : CollatzResearch.WordTrace tailWord_869065 prefixEnd_869065 297498709999831675260499 := by
  unfold tailWord_869065
  simp only [CollatzResearch.WordTrace]
  refine ⟨31697404596533404330432649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21131603064355602886955099 31697404596533404330432649)
  ·
    refine ⟨23773053447400053247824487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31697404596533404330432649 23773053447400053247824487)
    ·
      refine ⟨35659580171100079871736731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23773053447400053247824487 35659580171100079871736731)
      ·
        refine ⟨53489370256650119807605097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35659580171100079871736731 53489370256650119807605097)
        ·
          refine ⟨40117027692487589855703823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53489370256650119807605097 40117027692487589855703823)
          ·
            refine ⟨60175541538731384783555735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40117027692487589855703823 60175541538731384783555735)
            ·
              refine ⟨90263312308097077175333603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60175541538731384783555735 90263312308097077175333603)
              ·
                refine ⟨135394968462145615763000405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90263312308097077175333603 135394968462145615763000405)
                ·
                  refine ⟨1586659786665768934722661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 135394968462145615763000405 1586659786665768934722661)
                  ·
                    refine ⟨297498709999831675260499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1586659786665768934722661 297498709999831675260499)
                    ·
                      rfl

theorem cell22_869065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 8, 4].length) (baseStart_869065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_869065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_869065 prefixEnd_869065 := by exact prefixLift 869065
  have htrace : WordTrace (prefixWord ++ tailWord_869065) baseStart_869065 baseEnd_869065 := by
    simpa [prefixWord, tailWord_869065, baseEnd_869065] using wordTrace_append hprefix tailTrace_869065
  have hstable : (prefixWord ++ tailWord_869065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869065).length < 2 ^ (prefixWord ++ tailWord_869065).sum := by decide
  have hdescent : baseEnd_869065 < baseStart_869065 := by decide
  rcases family_descends (prefixWord ++ tailWord_869065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869080 : List Nat := [2, 1, 2, 2, 3, 2, 10]
def baseStart_869080 : Nat := 118140960795 + 869080 * 2 ^ 59
def prefixEnd_869080 : Nat := 4983230072969 + 3 ^ 40 * 869080 * 2
def baseEnd_869080 : Nat := 11018660918754690227239

theorem tailTrace_869080 : CollatzResearch.WordTrace tailWord_869080 prefixEnd_869080 11018660918754690227239 := by
  unfold tailWord_869080
  simp only [CollatzResearch.WordTrace]
  refine ⟨15848975845739530946114347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21131967794319374594819129 15848975845739530946114347)
  ·
    refine ⟨23773463768609296419171521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15848975845739530946114347 23773463768609296419171521)
    ·
      refine ⟨17830097826456972314378641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23773463768609296419171521 17830097826456972314378641)
      ·
        refine ⟨13372573369842729235783981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17830097826456972314378641 13372573369842729235783981)
        ·
          refine ⟨5014715013691023463418993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13372573369842729235783981 5014715013691023463418993)
          ·
            refine ⟨3761036260268267597564245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5014715013691023463418993 3761036260268267597564245)
            ·
              refine ⟨11018660918754690227239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3761036260268267597564245 11018660918754690227239)
              ·
                rfl

theorem cell22_869080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 10].length) (baseStart_869080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_869080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_869080 prefixEnd_869080 := by exact prefixLift 869080
  have htrace : WordTrace (prefixWord ++ tailWord_869080) baseStart_869080 baseEnd_869080 := by
    simpa [prefixWord, tailWord_869080, baseEnd_869080] using wordTrace_append hprefix tailTrace_869080
  have hstable : (prefixWord ++ tailWord_869080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869080).length < 2 ^ (prefixWord ++ tailWord_869080).sum := by decide
  have hdescent : baseEnd_869080 < baseStart_869080 := by decide
  rcases family_descends (prefixWord ++ tailWord_869080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869082 : List Nat := [3, 1, 1, 2, 2, 2, 3, 2, 2, 4]
def baseStart_869082 : Nat := 118140960795 + 869082 * 2 ^ 59
def prefixEnd_869082 : Nat := 4983230072969 + 3 ^ 40 * 869082 * 2
def baseEnd_869082 : Nat := 297504529447249297585447

theorem tailTrace_869082 : CollatzResearch.WordTrace tailWord_869082 prefixEnd_869082 297504529447249297585447 := by
  unfold tailWord_869082
  simp only [CollatzResearch.WordTrace]
  refine ⟨7924506159367954058450375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21132016424981210822534333 7924506159367954058450375)
  ·
    refine ⟨11886759239051931087675563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7924506159367954058450375 11886759239051931087675563)
    ·
      refine ⟨17830138858577896631513345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11886759239051931087675563 17830138858577896631513345)
      ·
        refine ⟨13372604143933422473635009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17830138858577896631513345 13372604143933422473635009)
        ·
          refine ⟨10029453107950066855226257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13372604143933422473635009 10029453107950066855226257)
          ·
            refine ⟨7522089830962550141419693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10029453107950066855226257 7522089830962550141419693)
            ·
              refine ⟨2820783686610956303032385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7522089830962550141419693 2820783686610956303032385)
              ·
                refine ⟨2115587764958217227274289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2820783686610956303032385 2115587764958217227274289)
                ·
                  refine ⟨1586690823718662920455717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2115587764958217227274289 1586690823718662920455717)
                  ·
                    refine ⟨297504529447249297585447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1586690823718662920455717 297504529447249297585447)
                    ·
                      rfl

theorem cell22_869082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 2, 2, 4].length) (baseStart_869082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_869082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_869082 prefixEnd_869082 := by exact prefixLift 869082
  have htrace : WordTrace (prefixWord ++ tailWord_869082) baseStart_869082 baseEnd_869082 := by
    simpa [prefixWord, tailWord_869082, baseEnd_869082] using wordTrace_append hprefix tailTrace_869082
  have hstable : (prefixWord ++ tailWord_869082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869082).length < 2 ^ (prefixWord ++ tailWord_869082).sum := by decide
  have hdescent : baseEnd_869082 < baseStart_869082 := by decide
  rcases family_descends (prefixWord ++ tailWord_869082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869112 : List Nat := [2, 1, 2, 1, 1, 2, 4, 1, 5, 3]
def baseStart_869112 : Nat := 118140960795 + 869112 * 2 ^ 59
def prefixEnd_869112 : Nat := 4983230072969 + 3 ^ 40 * 869112 * 2
def baseEnd_869112 : Nat := 297514799060339219335355

theorem tailTrace_869112 : CollatzResearch.WordTrace tailWord_869112 prefixEnd_869112 297514799060339219335355 := by
  unfold tailWord_869112
  simp only [CollatzResearch.WordTrace]
  refine ⟨15849559413681565678696795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21132745884908754238262393 15849559413681565678696795)
  ·
    refine ⟨23774339120522348518045193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15849559413681565678696795 23774339120522348518045193)
    ·
      refine ⟨17830754340391761388533895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23774339120522348518045193 17830754340391761388533895)
      ·
        refine ⟨26746131510587642082800843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17830754340391761388533895 26746131510587642082800843)
        ·
          refine ⟨40119197265881463124201265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26746131510587642082800843 40119197265881463124201265)
          ·
            refine ⟨30089397949411097343150949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40119197265881463124201265 30089397949411097343150949)
            ·
              refine ⟨5641762115514580751840803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30089397949411097343150949 5641762115514580751840803)
              ·
                refine ⟨8462643173271871127761205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5641762115514580751840803 8462643173271871127761205)
                ·
                  refine ⟨793372797494237918227613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8462643173271871127761205 793372797494237918227613)
                  ·
                    refine ⟨297514799060339219335355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 793372797494237918227613 297514799060339219335355)
                    ·
                      rfl

theorem cell22_869112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 5, 3].length) (baseStart_869112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_869112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_869112 prefixEnd_869112 := by exact prefixLift 869112
  have htrace : WordTrace (prefixWord ++ tailWord_869112) baseStart_869112 baseEnd_869112 := by
    simpa [prefixWord, tailWord_869112, baseEnd_869112] using wordTrace_append hprefix tailTrace_869112
  have hstable : (prefixWord ++ tailWord_869112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869112).length < 2 ^ (prefixWord ++ tailWord_869112).sum := by decide
  have hdescent : baseEnd_869112 < baseStart_869112 := by decide
  rcases family_descends (prefixWord ++ tailWord_869112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869125 : List Nat := [1, 3, 1, 1, 2, 1, 1, 3, 9]
def baseStart_869125 : Nat := 118140960795 + 869125 * 2 ^ 59
def prefixEnd_869125 : Nat := 4983230072969 + 3 ^ 40 * 869125 * 2
def baseEnd_869125 : Nat := 99173083075337172920105

theorem tailTrace_869125 : CollatzResearch.WordTrace tailWord_869125 prefixEnd_869125 99173083075337172920105 := by
  unfold tailWord_869125
  simp only [CollatzResearch.WordTrace]
  refine ⟨31699592976316034577616829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21133061984210689718411219 31699592976316034577616829)
  ·
    refine ⟨11887347366118512966606311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31699592976316034577616829 11887347366118512966606311)
    ·
      refine ⟨17831021049177769449909467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11887347366118512966606311 17831021049177769449909467)
      ·
        refine ⟨26746531573766654174864201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17831021049177769449909467 26746531573766654174864201)
        ·
          refine ⟨20059898680324990631148151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26746531573766654174864201 20059898680324990631148151)
          ·
            refine ⟨30089848020487485946722227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20059898680324990631148151 30089848020487485946722227)
            ·
              refine ⟨45134772030731228920083341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30089848020487485946722227 45134772030731228920083341)
              ·
                refine ⟨16925539511524210845031253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45134772030731228920083341 16925539511524210845031253)
                ·
                  refine ⟨99173083075337172920105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 16925539511524210845031253 99173083075337172920105)
                  ·
                    rfl

theorem cell22_869125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 9].length) (baseStart_869125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_869125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_869125 prefixEnd_869125 := by exact prefixLift 869125
  have htrace : WordTrace (prefixWord ++ tailWord_869125) baseStart_869125 baseEnd_869125 := by
    simpa [prefixWord, tailWord_869125, baseEnd_869125] using wordTrace_append hprefix tailTrace_869125
  have hstable : (prefixWord ++ tailWord_869125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869125).length < 2 ^ (prefixWord ++ tailWord_869125).sum := by decide
  have hdescent : baseEnd_869125 < baseStart_869125 := by decide
  rcases family_descends (prefixWord ++ tailWord_869125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869146 : List Nat := [3, 1, 1, 3, 2, 1, 3, 4, 1, 3]
def baseStart_869146 : Nat := 118140960795 + 869146 * 2 ^ 59
def prefixEnd_869146 : Nat := 4983230072969 + 3 ^ 40 * 869146 * 2
def baseEnd_869146 : Nat := 297526437955174463985251

theorem tailTrace_869146 : CollatzResearch.WordTrace tailWord_869146 prefixEnd_869146 297526437955174463985251 := by
  unfold tailWord_869146
  simp only [CollatzResearch.WordTrace]
  refine ⟨7925089727309988791032823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21133572606159970109420861 7925089727309988791032823)
  ·
    refine ⟨11887634590964983186549235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7925089727309988791032823 11887634590964983186549235)
    ·
      refine ⟨17831451886447474779823853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11887634590964983186549235 17831451886447474779823853)
      ·
        refine ⟨6686794457417803042433945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17831451886447474779823853 6686794457417803042433945)
        ·
          refine ⟨5015095843063352281825459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6686794457417803042433945 5015095843063352281825459)
          ·
            refine ⟨7522643764595028422738189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5015095843063352281825459 7522643764595028422738189)
            ·
              refine ⟨2820991411723135658526821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7522643764595028422738189 2820991411723135658526821)
              ·
                refine ⟨528935889698087935973779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2820991411723135658526821 528935889698087935973779)
                ·
                  refine ⟨793403834547131903960669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 528935889698087935973779 793403834547131903960669)
                  ·
                    refine ⟨297526437955174463985251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 793403834547131903960669 297526437955174463985251)
                    ·
                      rfl

theorem cell22_869146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 4, 1, 3].length) (baseStart_869146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_869146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_869146 prefixEnd_869146 := by exact prefixLift 869146
  have htrace : WordTrace (prefixWord ++ tailWord_869146) baseStart_869146 baseEnd_869146 := by
    simpa [prefixWord, tailWord_869146, baseEnd_869146] using wordTrace_append hprefix tailTrace_869146
  have hstable : (prefixWord ++ tailWord_869146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869146).length < 2 ^ (prefixWord ++ tailWord_869146).sum := by decide
  have hdescent : baseEnd_869146 < baseStart_869146 := by decide
  rcases family_descends (prefixWord ++ tailWord_869146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869157 : List Nat := [1, 3, 1, 2, 3, 1, 3, 1, 2, 5]
def baseStart_869157 : Nat := 118140960795 + 869157 * 2 ^ 59
def prefixEnd_869157 : Nat := 4983230072969 + 3 ^ 40 * 869157 * 2
def baseEnd_869157 : Nat := 297530203479974101960217

theorem tailTrace_869157 : CollatzResearch.WordTrace tailWord_869157 prefixEnd_869157 297530203479974101960217 := by
  unfold tailWord_869157
  simp only [CollatzResearch.WordTrace]
  refine ⟨31700760112200104042781725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21133840074800069361854483 31700760112200104042781725)
  ·
    refine ⟨11887785042075039016043147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31700760112200104042781725 11887785042075039016043147)
    ·
      refine ⟨17831677563112558524064721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11887785042075039016043147 17831677563112558524064721)
      ·
        refine ⟨13373758172334418893048541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17831677563112558524064721 13373758172334418893048541)
        ·
          refine ⟨5015159314625407084893203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13373758172334418893048541 5015159314625407084893203)
          ·
            refine ⟨7522738971938110627339805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5015159314625407084893203 7522738971938110627339805)
            ·
              refine ⟨2821027114476791485252427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7522738971938110627339805 2821027114476791485252427)
              ·
                refine ⟨4231540671715187227878641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2821027114476791485252427 4231540671715187227878641)
                ·
                  refine ⟨3173655503786390420908981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4231540671715187227878641 3173655503786390420908981)
                  ·
                    refine ⟨297530203479974101960217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3173655503786390420908981 297530203479974101960217)
                    ·
                      rfl

theorem cell22_869157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 1, 2, 5].length) (baseStart_869157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_869157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_869157 prefixEnd_869157 := by exact prefixLift 869157
  have htrace : WordTrace (prefixWord ++ tailWord_869157) baseStart_869157 baseEnd_869157 := by
    simpa [prefixWord, tailWord_869157, baseEnd_869157] using wordTrace_append hprefix tailTrace_869157
  have hstable : (prefixWord ++ tailWord_869157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869157).length < 2 ^ (prefixWord ++ tailWord_869157).sum := by decide
  have hdescent : baseEnd_869157 < baseStart_869157 := by decide
  rcases family_descends (prefixWord ++ tailWord_869157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869217 : List Nat := [1, 2, 3, 1, 1, 1, 2, 1, 6, 4]
def baseStart_869217 : Nat := 118140960795 + 869217 * 2 ^ 59
def prefixEnd_869217 : Nat := 4983230072969 + 3 ^ 40 * 869217 * 2
def baseEnd_869217 : Nat := 297550742706153945460033

theorem tailTrace_869217 : CollatzResearch.WordTrace tailWord_869217 prefixEnd_869217 297550742706153945460033 := by
  unfold tailWord_869217
  simp only [CollatzResearch.WordTrace]
  refine ⟨31702948491982734289965905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21135298994655156193310603 31702948491982734289965905)
  ·
    refine ⟨23777211368987050717474429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31702948491982734289965905 23777211368987050717474429)
    ·
      refine ⟨8916454263370144019052911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23777211368987050717474429 8916454263370144019052911)
      ·
        refine ⟨13374681395055216028579367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8916454263370144019052911 13374681395055216028579367)
        ·
          refine ⟨20062022092582824042869051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13374681395055216028579367 20062022092582824042869051)
          ·
            refine ⟨30093033138874236064303577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20062022092582824042869051 30093033138874236064303577)
            ·
              refine ⟨22569774854155677048227683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30093033138874236064303577 22569774854155677048227683)
              ·
                refine ⟨33854662281233515572341525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22569774854155677048227683 33854662281233515572341525)
                ·
                  refine ⟨1586937294432821042453509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 33854662281233515572341525 1586937294432821042453509)
                  ·
                    refine ⟨297550742706153945460033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1586937294432821042453509 297550742706153945460033)
                    ·
                      rfl

theorem cell22_869217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 6, 4].length) (baseStart_869217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_869217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_869217 prefixEnd_869217 := by exact prefixLift 869217
  have htrace : WordTrace (prefixWord ++ tailWord_869217) baseStart_869217 baseEnd_869217 := by
    simpa [prefixWord, tailWord_869217, baseEnd_869217] using wordTrace_append hprefix tailTrace_869217
  have hstable : (prefixWord ++ tailWord_869217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869217).length < 2 ^ (prefixWord ++ tailWord_869217).sum := by decide
  have hdescent : baseEnd_869217 < baseStart_869217 := by decide
  rcases family_descends (prefixWord ++ tailWord_869217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869219 : List Nat := [1, 1, 1, 5, 3, 1, 3, 1, 1, 5]
def baseStart_869219 : Nat := 118140960795 + 869219 * 2 ^ 59
def prefixEnd_869219 : Nat := 4983230072969 + 3 ^ 40 * 869219 * 2
def baseEnd_869219 : Nat := 297551427347026606910027

theorem tailTrace_869219 : CollatzResearch.WordTrace tailWord_869219 prefixEnd_869219 297551427347026606910027 := by
  unfold tailWord_869219
  simp only [CollatzResearch.WordTrace]
  refine ⟨31703021437975488631538711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21135347625316992421025807 31703021437975488631538711)
  ·
    refine ⟨47554532156963232947308067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31703021437975488631538711 47554532156963232947308067)
    ·
      refine ⟨71331798235444849420962101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47554532156963232947308067 71331798235444849420962101)
      ·
        refine ⟨6687356084572954633215197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71331798235444849420962101 6687356084572954633215197)
        ·
          refine ⟨2507758531714857987455699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6687356084572954633215197 2507758531714857987455699)
          ·
            refine ⟨3761637797572286981183549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2507758531714857987455699 3761637797572286981183549)
            ·
              refine ⟨1410614174089607617943831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3761637797572286981183549 1410614174089607617943831)
              ·
                refine ⟨2115921261134411426915747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1410614174089607617943831 2115921261134411426915747)
                ·
                  refine ⟨3173881891701617140373621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2115921261134411426915747 3173881891701617140373621)
                  ·
                    refine ⟨297551427347026606910027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3173881891701617140373621 297551427347026606910027)
                    ·
                      rfl

theorem cell22_869219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 1, 1, 5].length) (baseStart_869219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_869219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_869219 prefixEnd_869219 := by exact prefixLift 869219
  have htrace : WordTrace (prefixWord ++ tailWord_869219) baseStart_869219 baseEnd_869219 := by
    simpa [prefixWord, tailWord_869219, baseEnd_869219] using wordTrace_append hprefix tailTrace_869219
  have hstable : (prefixWord ++ tailWord_869219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869219).length < 2 ^ (prefixWord ++ tailWord_869219).sum := by decide
  have hdescent : baseEnd_869219 < baseStart_869219 := by decide
  rcases family_descends (prefixWord ++ tailWord_869219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869238 : List Nat := [5, 1, 1, 3, 1, 1, 3, 3, 4]
def baseStart_869238 : Nat := 118140960795 + 869238 * 2 ^ 59
def prefixEnd_869238 : Nat := 4983230072969 + 3 ^ 40 * 869238 * 2
def baseEnd_869238 : Nat := 99185977145105630228323

theorem tailTrace_869238 : CollatzResearch.WordTrace tailWord_869238 prefixEnd_869238 99185977145105630228323 := by
  unfold tailWord_869238
  simp only [CollatzResearch.WordTrace]
  refine ⟨1981482151556665929780023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21135809616604436584320245 1981482151556665929780023)
  ·
    refine ⟨2972223227334998894670035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1981482151556665929780023 2972223227334998894670035)
    ·
      refine ⟨4458334841002498342005053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2972223227334998894670035 4458334841002498342005053)
      ·
        refine ⟨1671875565375936878251895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4458334841002498342005053 1671875565375936878251895)
        ·
          refine ⟨2507813348063905317377843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1671875565375936878251895 2507813348063905317377843)
          ·
            refine ⟨3761720022095857976066765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2507813348063905317377843 3761720022095857976066765)
            ·
              refine ⟨1410645008285946741025037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3761720022095857976066765 1410645008285946741025037)
              ·
                refine ⟨528991878107230027884389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1410645008285946741025037 528991878107230027884389)
                ·
                  refine ⟨99185977145105630228323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 528991878107230027884389 99185977145105630228323)
                  ·
                    rfl

theorem cell22_869238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 3, 4].length) (baseStart_869238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_869238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_869238 prefixEnd_869238 := by exact prefixLift 869238
  have htrace : WordTrace (prefixWord ++ tailWord_869238) baseStart_869238 baseEnd_869238 := by
    simpa [prefixWord, tailWord_869238, baseEnd_869238] using wordTrace_append hprefix tailTrace_869238
  have hstable : (prefixWord ++ tailWord_869238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869238).length < 2 ^ (prefixWord ++ tailWord_869238).sum := by decide
  have hdescent : baseEnd_869238 < baseStart_869238 := by decide
  rcases family_descends (prefixWord ++ tailWord_869238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869266 : List Nat := [3, 2, 3, 2, 2, 1, 2, 7]
def baseStart_869266 : Nat := 118140960795 + 869266 * 2 ^ 59
def prefixEnd_869266 : Nat := 4983230072969 + 3 ^ 40 * 869266 * 2
def baseEnd_869266 : Nat := 33063057378614905664987

theorem tailTrace_869266 : CollatzResearch.WordTrace tailWord_869266 prefixEnd_869266 33063057378614905664987 := by
  unfold tailWord_869266
  simp only [CollatzResearch.WordTrace]
  refine ⟨7926183917201303914624913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21136490445870143772333101 7926183917201303914624913)
  ·
    refine ⟨5944637937900977935968685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7926183917201303914624913 5944637937900977935968685)
    ·
      refine ⟨2229239226712866725988257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5944637937900977935968685 2229239226712866725988257)
      ·
        refine ⟨1671929420034650044491193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2229239226712866725988257 1671929420034650044491193)
        ·
          refine ⟨1253947065025987533368395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1671929420034650044491193 1253947065025987533368395)
          ·
            refine ⟨1880920597538981300052593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1253947065025987533368395 1880920597538981300052593)
            ·
              refine ⟨1410690448154235975039445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1880920597538981300052593 1410690448154235975039445)
              ·
                refine ⟨33063057378614905664987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1410690448154235975039445 33063057378614905664987)
                ·
                  rfl

theorem cell22_869266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 7].length) (baseStart_869266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_869266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_869266 prefixEnd_869266 := by exact prefixLift 869266
  have htrace : WordTrace (prefixWord ++ tailWord_869266) baseStart_869266 baseEnd_869266 := by
    simpa [prefixWord, tailWord_869266, baseEnd_869266] using wordTrace_append hprefix tailTrace_869266
  have hstable : (prefixWord ++ tailWord_869266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869266).length < 2 ^ (prefixWord ++ tailWord_869266).sum := by decide
  have hdescent : baseEnd_869266 < baseStart_869266 := by decide
  rcases family_descends (prefixWord ++ tailWord_869266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869292 : List Nat := [2, 2, 1, 1, 1, 1, 2, 4, 1, 7]
def baseStart_869292 : Nat := 118140960795 + 869292 * 2 ^ 59
def prefixEnd_869292 : Nat := 4983230072969 + 3 ^ 40 * 869292 * 2
def baseEnd_869292 : Nat := 297576416738878749834803

theorem tailTrace_869292 : CollatzResearch.WordTrace tailWord_869292 prefixEnd_869292 297576416738878749834803 := by
  unfold tailWord_869292
  simp only [CollatzResearch.WordTrace]
  refine ⟨15852841983355511049473065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21137122644474014732630753 15852841983355511049473065)
  ·
    refine ⟨11889631487516633287104799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15852841983355511049473065 11889631487516633287104799)
    ·
      refine ⟨17834447231274949930657199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11889631487516633287104799 17834447231274949930657199)
      ·
        refine ⟨26751670846912424895985799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17834447231274949930657199 26751670846912424895985799)
        ·
          refine ⟨40127506270368637343978699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26751670846912424895985799 40127506270368637343978699)
          ·
            refine ⟨60191259405552956015968049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40127506270368637343978699 60191259405552956015968049)
            ·
              refine ⟨45143444554164717011976037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60191259405552956015968049 45143444554164717011976037)
              ·
                refine ⟨8464395853905884439745507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45143444554164717011976037 8464395853905884439745507)
                ·
                  refine ⟨12696593780858826659618261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8464395853905884439745507 12696593780858826659618261)
                  ·
                    refine ⟨297576416738878749834803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12696593780858826659618261 297576416738878749834803)
                    ·
                      rfl

theorem cell22_869292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 7].length) (baseStart_869292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_869292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_869292 prefixEnd_869292 := by exact prefixLift 869292
  have htrace : WordTrace (prefixWord ++ tailWord_869292) baseStart_869292 baseEnd_869292 := by
    simpa [prefixWord, tailWord_869292, baseEnd_869292] using wordTrace_append hprefix tailTrace_869292
  have hstable : (prefixWord ++ tailWord_869292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869292).length < 2 ^ (prefixWord ++ tailWord_869292).sum := by decide
  have hdescent : baseEnd_869292 < baseStart_869292 := by decide
  rcases family_descends (prefixWord ++ tailWord_869292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869324 : List Nat := [2, 2, 1, 4, 1, 1, 1, 1, 5, 4]
def baseStart_869324 : Nat := 118140960795 + 869324 * 2 ^ 59
def prefixEnd_869324 : Nat := 4983230072969 + 3 ^ 40 * 869324 * 2
def baseEnd_869324 : Nat := 297587370992841333034705

theorem tailTrace_869324 : CollatzResearch.WordTrace tailWord_869324 prefixEnd_869324 297587370992841333034705 := by
  unfold tailWord_869324
  simp only [CollatzResearch.WordTrace]
  refine ⟨15853425551297545782055513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21137900735063394376074017 15853425551297545782055513)
  ·
    refine ⟨11890069163473159336541635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15853425551297545782055513 11890069163473159336541635)
    ·
      refine ⟨17835103745209739004812453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11890069163473159336541635 17835103745209739004812453)
      ·
        refine ⟨3344081952226826063402335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17835103745209739004812453 3344081952226826063402335)
        ·
          refine ⟨5016122928340239095103503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3344081952226826063402335 5016122928340239095103503)
          ·
            refine ⟨7524184392510358642655255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5016122928340239095103503 7524184392510358642655255)
            ·
              refine ⟨11286276588765537963982883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7524184392510358642655255 11286276588765537963982883)
              ·
                refine ⟨16929414883148306945974325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11286276588765537963982883 16929414883148306945974325)
                ·
                  refine ⟨1587132645295153776185093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16929414883148306945974325 1587132645295153776185093)
                  ·
                    refine ⟨297587370992841333034705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1587132645295153776185093 297587370992841333034705)
                    ·
                      rfl

theorem cell22_869324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 5, 4].length) (baseStart_869324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_869324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_869324 prefixEnd_869324 := by exact prefixLift 869324
  have htrace : WordTrace (prefixWord ++ tailWord_869324) baseStart_869324 baseEnd_869324 := by
    simpa [prefixWord, tailWord_869324, baseEnd_869324] using wordTrace_append hprefix tailTrace_869324
  have hstable : (prefixWord ++ tailWord_869324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869324).length < 2 ^ (prefixWord ++ tailWord_869324).sum := by decide
  have hdescent : baseEnd_869324 < baseStart_869324 := by decide
  rcases family_descends (prefixWord ++ tailWord_869324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869341 : List Nat := [1, 4, 3, 1, 2, 1, 2, 1, 3, 4]
def baseStart_869341 : Nat := 118140960795 + 869341 * 2 ^ 59
def prefixEnd_869341 : Nat := 4983230072969 + 3 ^ 40 * 869341 * 2
def baseEnd_869341 : Nat := 297593190440258955359653

theorem tailTrace_869341 : CollatzResearch.WordTrace tailWord_869341 prefixEnd_869341 297593190440258955359653 := by
  unfold tailWord_869341
  simp only [CollatzResearch.WordTrace]
  refine ⟨31707471143533503467479877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21138314095689002311653251 31707471143533503467479877)
  ·
    refine ⟨5945150839412531900152477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31707471143533503467479877 5945150839412531900152477)
    ·
      refine ⟨2229431564779699462557179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5945150839412531900152477 2229431564779699462557179)
      ·
        refine ⟨3344147347169549193835769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2229431564779699462557179 3344147347169549193835769)
        ·
          refine ⟨2508110510377161895376827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3344147347169549193835769 2508110510377161895376827)
          ·
            refine ⟨3762165765565742843065241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2508110510377161895376827 3762165765565742843065241)
            ·
              refine ⟨2821624324174307132298931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3762165765565742843065241 2821624324174307132298931)
              ·
                refine ⟨4232436486261460698448397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2821624324174307132298931 4232436486261460698448397)
                ·
                  refine ⟨1587163682348047761918149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4232436486261460698448397 1587163682348047761918149)
                  ·
                    refine ⟨297593190440258955359653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1587163682348047761918149 297593190440258955359653)
                    ·
                      rfl

theorem cell22_869341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_869341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_869341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_869341 prefixEnd_869341 := by exact prefixLift 869341
  have htrace : WordTrace (prefixWord ++ tailWord_869341) baseStart_869341 baseEnd_869341 := by
    simpa [prefixWord, tailWord_869341, baseEnd_869341] using wordTrace_append hprefix tailTrace_869341
  have hstable : (prefixWord ++ tailWord_869341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869341).length < 2 ^ (prefixWord ++ tailWord_869341).sum := by decide
  have hdescent : baseEnd_869341 < baseStart_869341 := by decide
  rcases family_descends (prefixWord ++ tailWord_869341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869358 : List Nat := [4, 1, 2, 1, 4, 1, 1, 3, 1, 4]
def baseStart_869358 : Nat := 118140960795 + 869358 * 2 ^ 59
def prefixEnd_869358 : Nat := 4983230072969 + 3 ^ 40 * 869358 * 2
def baseEnd_869358 : Nat := 297599009887676577684601

theorem tailTrace_869358 : CollatzResearch.WordTrace tailWord_869358 prefixEnd_869358 297599009887676577684601 := by
  unfold tailWord_869358
  simp only [CollatzResearch.WordTrace]
  refine ⟨3963511398058989421356091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21138727456314610247232485 3963511398058989421356091)
  ·
    refine ⟨5945267097088484132034137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3963511398058989421356091 5945267097088484132034137)
    ·
      refine ⟨4458950322816363099025603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5945267097088484132034137 4458950322816363099025603)
      ·
        refine ⟨6688425484224544648538405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4458950322816363099025603 6688425484224544648538405)
        ·
          refine ⟨1254079778292102121600951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6688425484224544648538405 1254079778292102121600951)
          ·
            refine ⟨1881119667438153182401427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1254079778292102121600951 1881119667438153182401427)
            ·
              refine ⟨2821679501157229773602141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1881119667438153182401427 2821679501157229773602141)
              ·
                refine ⟨1058129812933961165100803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2821679501157229773602141 1058129812933961165100803)
                ·
                  refine ⟨1587194719400941747651205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1058129812933961165100803 1587194719400941747651205)
                  ·
                    refine ⟨297599009887676577684601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1587194719400941747651205 297599009887676577684601)
                    ·
                      rfl

theorem cell22_869358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_869358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_869358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_869358 prefixEnd_869358 := by exact prefixLift 869358
  have htrace : WordTrace (prefixWord ++ tailWord_869358) baseStart_869358 baseEnd_869358 := by
    simpa [prefixWord, tailWord_869358, baseEnd_869358] using wordTrace_append hprefix tailTrace_869358
  have hstable : (prefixWord ++ tailWord_869358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869358).length < 2 ^ (prefixWord ++ tailWord_869358).sum := by decide
  have hdescent : baseEnd_869358 < baseStart_869358 := by decide
  rcases family_descends (prefixWord ++ tailWord_869358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869369 : List Nat := [1, 2, 1, 3, 1, 3, 2, 1, 4, 4]
def baseStart_869369 : Nat := 118140960795 + 869369 * 2 ^ 59
def prefixEnd_869369 : Nat := 4983230072969 + 3 ^ 40 * 869369 * 2
def baseEnd_869369 : Nat := 297602775412476215659567

theorem tailTrace_869369 : CollatzResearch.WordTrace tailWord_869369 prefixEnd_869369 297602775412476215659567 := by
  unfold tailWord_869369
  simp only [CollatzResearch.WordTrace]
  refine ⟨31708492387432064249499161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21138994924954709499666107 31708492387432064249499161)
  ·
    refine ⟨23781369290574048187124371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31708492387432064249499161 23781369290574048187124371)
    ·
      refine ⟨35672053935861072280686557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23781369290574048187124371 35672053935861072280686557)
      ·
        refine ⟨13377020225947902105257459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35672053935861072280686557 13377020225947902105257459)
        ·
          refine ⟨20065530338921853157886189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13377020225947902105257459 20065530338921853157886189)
          ·
            refine ⟨7524573877095694934207321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20065530338921853157886189 7524573877095694934207321)
            ·
              refine ⟨5643430407821771200655491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7524573877095694934207321 5643430407821771200655491)
              ·
                refine ⟨8465145611732656800983237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5643430407821771200655491 8465145611732656800983237)
                ·
                  refine ⟨1587214802199873150184357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8465145611732656800983237 1587214802199873150184357)
                  ·
                    refine ⟨297602775412476215659567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1587214802199873150184357 297602775412476215659567)
                    ·
                      rfl

theorem cell22_869369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 4, 4].length) (baseStart_869369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_869369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_869369 prefixEnd_869369 := by exact prefixLift 869369
  have htrace : WordTrace (prefixWord ++ tailWord_869369) baseStart_869369 baseEnd_869369 := by
    simpa [prefixWord, tailWord_869369, baseEnd_869369] using wordTrace_append hprefix tailTrace_869369
  have hstable : (prefixWord ++ tailWord_869369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869369).length < 2 ^ (prefixWord ++ tailWord_869369).sum := by decide
  have hdescent : baseEnd_869369 < baseStart_869369 := by decide
  rcases family_descends (prefixWord ++ tailWord_869369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869418 : List Nat := [3, 1, 4, 1, 4, 1, 8]
def baseStart_869418 : Nat := 118140960795 + 869418 * 2 ^ 59
def prefixEnd_869418 : Nat := 4983230072969 + 3 ^ 40 * 869418 * 2
def baseEnd_869418 : Nat := 11022946263476163747571

theorem tailTrace_869418 : CollatzResearch.WordTrace tailWord_869418 prefixEnd_869418 11022946263476163747571 := by
  unfold tailWord_869418
  simp only [CollatzResearch.WordTrace]
  refine ⟨7927569891063636404508227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21140186376169697078688605 7927569891063636404508227)
  ·
    refine ⟨11891354836595454606762341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7927569891063636404508227 11891354836595454606762341)
    ·
      refine ⟨2229629031861647738767939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11891354836595454606762341 2229629031861647738767939)
      ·
        refine ⟨3344443547792471608151909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2229629031861647738767939 3344443547792471608151909)
        ·
          refine ⟨627083165211088426528483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3344443547792471608151909 627083165211088426528483)
          ·
            refine ⟨940624747816632639792725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 627083165211088426528483 940624747816632639792725)
            ·
              refine ⟨11022946263476163747571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 940624747816632639792725 11022946263476163747571)
              ·
                rfl

theorem cell22_869418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 8].length) (baseStart_869418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_869418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_869418 prefixEnd_869418 := by exact prefixLift 869418
  have htrace : WordTrace (prefixWord ++ tailWord_869418) baseStart_869418 baseEnd_869418 := by
    simpa [prefixWord, tailWord_869418, baseEnd_869418] using wordTrace_append hprefix tailTrace_869418
  have hstable : (prefixWord ++ tailWord_869418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869418).length < 2 ^ (prefixWord ++ tailWord_869418).sum := by decide
  have hdescent : baseEnd_869418 < baseStart_869418 := by decide
  rcases family_descends (prefixWord ++ tailWord_869418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869433 : List Nat := [1, 2, 1, 5, 2, 1, 3, 1, 3, 3]
def baseStart_869433 : Nat := 118140960795 + 869433 * 2 ^ 59
def prefixEnd_869433 : Nat := 4983230072969 + 3 ^ 40 * 869433 * 2
def baseEnd_869433 : Nat := 297624683920401382059371

theorem tailTrace_869433 : CollatzResearch.WordTrace tailWord_869433 prefixEnd_869433 297624683920401382059371 := by
  unfold tailWord_869433
  simp only [CollatzResearch.WordTrace]
  refine ⟨31710826659200203179828953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21140551106133468786552635 31710826659200203179828953)
  ·
    refine ⟨23783119994400152384871715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31710826659200203179828953 23783119994400152384871715)
    ·
      refine ⟨35674679991600228577307573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23783119994400152384871715 35674679991600228577307573)
      ·
        refine ⟨3344501249212521429122585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35674679991600228577307573 3344501249212521429122585)
        ·
          refine ⟨2508375936909391071841939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3344501249212521429122585 2508375936909391071841939)
          ·
            refine ⟨3762563905364086607762909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2508375936909391071841939 3762563905364086607762909)
            ·
              refine ⟨1410961464511532477911091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3762563905364086607762909 1410961464511532477911091)
              ·
                refine ⟨2116442196767298716866637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1410961464511532477911091 2116442196767298716866637)
                ·
                  refine ⟨793665823787737018824989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2116442196767298716866637 793665823787737018824989)
                  ·
                    refine ⟨297624683920401382059371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 793665823787737018824989 297624683920401382059371)
                    ·
                      rfl

theorem cell22_869433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 1, 3, 3].length) (baseStart_869433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_869433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_869433 prefixEnd_869433 := by exact prefixLift 869433
  have htrace : WordTrace (prefixWord ++ tailWord_869433) baseStart_869433 baseEnd_869433 := by
    simpa [prefixWord, tailWord_869433, baseEnd_869433] using wordTrace_append hprefix tailTrace_869433
  have hstable : (prefixWord ++ tailWord_869433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869433).length < 2 ^ (prefixWord ++ tailWord_869433).sum := by decide
  have hdescent : baseEnd_869433 < baseStart_869433 := by decide
  rcases family_descends (prefixWord ++ tailWord_869433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869480 : List Nat := [2, 1, 4, 4, 1, 1, 2, 2, 5]
def baseStart_869480 : Nat := 118140960795 + 869480 * 2 ^ 59
def prefixEnd_869480 : Nat := 4983230072969 + 3 ^ 40 * 869480 * 2
def baseEnd_869480 : Nat := 99213590993636308711409

theorem tailTrace_869480 : CollatzResearch.WordTrace tailWord_869480 prefixEnd_869480 99213590993636308711409 := by
  unfold tailWord_869480
  simp only [CollatzResearch.WordTrace]
  refine ⟨15856270445014965103394947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21141693926686620137859929 15856270445014965103394947)
  ·
    refine ⟨23784405667522447655092421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15856270445014965103394947 23784405667522447655092421)
    ·
      refine ⟨4459576062660458935329829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23784405667522447655092421 4459576062660458935329829)
      ·
        refine ⟨836170511748836050374343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4459576062660458935329829 836170511748836050374343)
        ·
          refine ⟨1254255767623254075561515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 836170511748836050374343 1254255767623254075561515)
          ·
            refine ⟨1881383651434881113342273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1254255767623254075561515 1881383651434881113342273)
            ·
              refine ⟨1411037738576160835006705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1881383651434881113342273 1411037738576160835006705)
              ·
                refine ⟨1058278303932120626255029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1411037738576160835006705 1058278303932120626255029)
                ·
                  refine ⟨99213590993636308711409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1058278303932120626255029 99213590993636308711409)
                  ·
                    rfl

theorem cell22_869480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 2, 5].length) (baseStart_869480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_869480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_869480 prefixEnd_869480 := by exact prefixLift 869480
  have htrace : WordTrace (prefixWord ++ tailWord_869480) baseStart_869480 baseEnd_869480 := by
    simpa [prefixWord, tailWord_869480, baseEnd_869480] using wordTrace_append hprefix tailTrace_869480
  have hstable : (prefixWord ++ tailWord_869480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869480).length < 2 ^ (prefixWord ++ tailWord_869480).sum := by decide
  have hdescent : baseEnd_869480 < baseStart_869480 := by decide
  rcases family_descends (prefixWord ++ tailWord_869480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869540 : List Nat := [2, 3, 1, 2, 3, 1, 3, 2, 2, 3]
def baseStart_869540 : Nat := 118140960795 + 869540 * 2 ^ 59
def prefixEnd_869540 : Nat := 4983230072969 + 3 ^ 40 * 869540 * 2
def baseEnd_869540 : Nat := 297661312207088769634043

theorem tailTrace_869540 : CollatzResearch.WordTrace tailWord_869540 prefixEnd_869540 297661312207088769634043 := by
  unfold tailWord_869540
  simp only [CollatzResearch.WordTrace]
  refine ⟨15857364634906280226987037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21143152846541706969316049 15857364634906280226987037)
  ·
    refine ⟨5946511738089855085120139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15857364634906280226987037 5946511738089855085120139)
    ·
      refine ⟨8919767607134782627680209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5946511738089855085120139 8919767607134782627680209)
      ·
        refine ⟨6689825705351086970760157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8919767607134782627680209 6689825705351086970760157)
        ·
          refine ⟨2508684639506657614035059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6689825705351086970760157 2508684639506657614035059)
          ·
            refine ⟨3763026959259986421052589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2508684639506657614035059 3763026959259986421052589)
            ·
              refine ⟨1411135109722494907894721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3763026959259986421052589 1411135109722494907894721)
              ·
                refine ⟨1058351332291871180921041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1411135109722494907894721 1058351332291871180921041)
                ·
                  refine ⟨793763499218903385690781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1058351332291871180921041 793763499218903385690781)
                  ·
                    refine ⟨297661312207088769634043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 793763499218903385690781 297661312207088769634043)
                    ·
                      rfl

theorem cell22_869540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 2, 2, 3].length) (baseStart_869540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_869540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_869540 prefixEnd_869540 := by exact prefixLift 869540
  have htrace : WordTrace (prefixWord ++ tailWord_869540) baseStart_869540 baseEnd_869540 := by
    simpa [prefixWord, tailWord_869540, baseEnd_869540] using wordTrace_append hprefix tailTrace_869540
  have hstable : (prefixWord ++ tailWord_869540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869540).length < 2 ^ (prefixWord ++ tailWord_869540).sum := by decide
  have hdescent : baseEnd_869540 < baseStart_869540 := by decide
  rcases family_descends (prefixWord ++ tailWord_869540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869626 : List Nat := [3, 1, 1, 1, 1, 4, 2, 1, 8]
def baseStart_869626 : Nat := 118140960795 + 869626 * 2 ^ 59
def prefixEnd_869626 : Nat := 4983230072969 + 3 ^ 40 * 869626 * 2
def baseEnd_869626 : Nat := 99230250588204403994593

theorem tailTrace_869626 : CollatzResearch.WordTrace tailWord_869626 prefixEnd_869626 99230250588204403994593 := by
  unfold tailWord_869626
  simp only [CollatzResearch.WordTrace]
  refine ⟨7929466486875249285401183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21145243965000664761069821 7929466486875249285401183)
  ·
    refine ⟨11894199730312873928101775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7929466486875249285401183 11894199730312873928101775)
    ·
      refine ⟨17841299595469310892152663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11894199730312873928101775 17841299595469310892152663)
      ·
        refine ⟨26761949393203966338228995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17841299595469310892152663 26761949393203966338228995)
        ·
          refine ⟨40142924089805949507343493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26761949393203966338228995 40142924089805949507343493)
          ·
            refine ⟨7526798266838615532626905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40142924089805949507343493 7526798266838615532626905)
            ·
              refine ⟨5645098700128961649470179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7526798266838615532626905 5645098700128961649470179)
              ·
                refine ⟨8467648050193442474205269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5645098700128961649470179 8467648050193442474205269)
                ·
                  refine ⟨99230250588204403994593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8467648050193442474205269 99230250588204403994593)
                  ·
                    rfl

theorem cell22_869626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 8].length) (baseStart_869626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_869626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_869626 prefixEnd_869626 := by exact prefixLift 869626
  have htrace : WordTrace (prefixWord ++ tailWord_869626) baseStart_869626 baseEnd_869626 := by
    simpa [prefixWord, tailWord_869626, baseEnd_869626] using wordTrace_append hprefix tailTrace_869626
  have hstable : (prefixWord ++ tailWord_869626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869626).length < 2 ^ (prefixWord ++ tailWord_869626).sum := by decide
  have hdescent : baseEnd_869626 < baseStart_869626 := by decide
  rcases family_descends (prefixWord ++ tailWord_869626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869709 : List Nat := [1, 6, 1, 3, 1, 1, 1, 1, 4, 3]
def baseStart_869709 : Nat := 118140960795 + 869709 * 2 ^ 59
def prefixEnd_869709 : Nat := 4983230072969 + 3 ^ 40 * 869709 * 2
def baseEnd_869709 : Nat := 297719164360828662158525

theorem tailTrace_869709 : CollatzResearch.WordTrace tailWord_869709 prefixEnd_869709 297719164360828662158525 := by
  unfold tailWord_869709
  simp only [CollatzResearch.WordTrace]
  refine ⟨31720893206200302316876181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21147262137466868211250787 31720893206200302316876181)
  ·
    refine ⟨1486916869040639171103571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 31720893206200302316876181 1486916869040639171103571)
    ·
      refine ⟨2230375303560958756655357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1486916869040639171103571 2230375303560958756655357)
      ·
        refine ⟨836390738835359533745759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2230375303560958756655357 836390738835359533745759)
        ·
          refine ⟨1254586108253039300618639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 836390738835359533745759 1254586108253039300618639)
          ·
            refine ⟨1881879162379558950927959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1254586108253039300618639 1881879162379558950927959)
            ·
              refine ⟨2822818743569338426391939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1881879162379558950927959 2822818743569338426391939)
              ·
                refine ⟨4234228115354007639587909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2822818743569338426391939 4234228115354007639587909)
                ·
                  refine ⟨793917771628876432422733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4234228115354007639587909 793917771628876432422733)
                  ·
                    refine ⟨297719164360828662158525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 793917771628876432422733 297719164360828662158525)
                    ·
                      rfl

theorem cell22_869709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_869709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_869709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_869709 prefixEnd_869709 := by exact prefixLift 869709
  have htrace : WordTrace (prefixWord ++ tailWord_869709) baseStart_869709 baseEnd_869709 := by
    simpa [prefixWord, tailWord_869709, baseEnd_869709] using wordTrace_append hprefix tailTrace_869709
  have hstable : (prefixWord ++ tailWord_869709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869709).length < 2 ^ (prefixWord ++ tailWord_869709).sum := by decide
  have hdescent : baseEnd_869709 < baseStart_869709 := by decide
  rcases family_descends (prefixWord ++ tailWord_869709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869720 : List Nat := [2, 1, 2, 2, 1, 1, 6, 1, 3, 3]
def baseStart_869720 : Nat := 118140960795 + 869720 * 2 ^ 59
def prefixEnd_869720 : Nat := 4983230072969 + 3 ^ 40 * 869720 * 2
def baseEnd_869720 : Nat := 297722929885628300133491

theorem tailTrace_869720 : CollatzResearch.WordTrace tailWord_869720 prefixEnd_869720 297722929885628300133491 := by
  unfold tailWord_869720
  simp only [CollatzResearch.WordTrace]
  refine ⟨15860647204580225597763307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21147529606106967463684409 15860647204580225597763307)
  ·
    refine ⟨23790970806870338396644961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15860647204580225597763307 23790970806870338396644961)
    ·
      refine ⟨17843228105152753797483721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23790970806870338396644961 17843228105152753797483721)
      ·
        refine ⟨13382421078864565348112791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17843228105152753797483721 13382421078864565348112791)
        ·
          refine ⟨20073631618296848022169187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13382421078864565348112791 20073631618296848022169187)
          ·
            refine ⟨30110447427445272033253781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20073631618296848022169187 30110447427445272033253781)
            ·
              refine ⟨1411427223161497126558771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 30110447427445272033253781 1411427223161497126558771)
              ·
                refine ⟨2117140834742245689838157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1411427223161497126558771 2117140834742245689838157)
                ·
                  refine ⟨793927813028342133689309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2117140834742245689838157 793927813028342133689309)
                  ·
                    refine ⟨297722929885628300133491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 793927813028342133689309 297722929885628300133491)
                    ·
                      rfl

theorem cell22_869720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 1, 3, 3].length) (baseStart_869720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_869720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_869720 prefixEnd_869720 := by exact prefixLift 869720
  have htrace : WordTrace (prefixWord ++ tailWord_869720) baseStart_869720 baseEnd_869720 := by
    simpa [prefixWord, tailWord_869720, baseEnd_869720] using wordTrace_append hprefix tailTrace_869720
  have hstable : (prefixWord ++ tailWord_869720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869720).length < 2 ^ (prefixWord ++ tailWord_869720).sum := by decide
  have hdescent : baseEnd_869720 < baseStart_869720 := by decide
  rcases family_descends (prefixWord ++ tailWord_869720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869784 : List Nat := [2, 1, 2, 5, 2, 2, 2, 1, 5]
def baseStart_869784 : Nat := 118140960795 + 869784 * 2 ^ 59
def prefixEnd_869784 : Nat := 4983230072969 + 3 ^ 40 * 869784 * 2
def baseEnd_869784 : Nat := 99248279464517822177765

theorem tailTrace_869784 : CollatzResearch.WordTrace tailWord_869784 prefixEnd_869784 99248279464517822177765 := by
  unfold tailWord_869784
  simp only [CollatzResearch.WordTrace]
  refine ⟨15861814340464295062928203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21149085787285726750570937 15861814340464295062928203)
  ·
    refine ⟨23792721510696442594392305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15861814340464295062928203 23792721510696442594392305)
    ·
      refine ⟨17844541133022331945794229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23792721510696442594392305 17844541133022331945794229)
      ·
        refine ⟨1672925731220843619918209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17844541133022331945794229 1672925731220843619918209)
        ·
          refine ⟨1254694298415632714938657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1672925731220843619918209 1254694298415632714938657)
          ·
            refine ⟨941020723811724536203993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1254694298415632714938657 941020723811724536203993)
            ·
              refine ⟨705765542858793402152995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 941020723811724536203993 705765542858793402152995)
              ·
                refine ⟨1058648314288190103229493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 705765542858793402152995 1058648314288190103229493)
                ·
                  refine ⟨99248279464517822177765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1058648314288190103229493 99248279464517822177765)
                  ·
                    rfl

theorem cell22_869784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 2, 1, 5].length) (baseStart_869784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_869784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_869784 prefixEnd_869784 := by exact prefixLift 869784
  have htrace : WordTrace (prefixWord ++ tailWord_869784) baseStart_869784 baseEnd_869784 := by
    simpa [prefixWord, tailWord_869784, baseEnd_869784] using wordTrace_append hprefix tailTrace_869784
  have hstable : (prefixWord ++ tailWord_869784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869784).length < 2 ^ (prefixWord ++ tailWord_869784).sum := by decide
  have hdescent : baseEnd_869784 < baseStart_869784 := by decide
  rcases family_descends (prefixWord ++ tailWord_869784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869810 : List Nat := [3, 2, 1, 1, 1, 1, 2, 4, 4, 3]
def baseStart_869810 : Nat := 118140960795 + 869810 * 2 ^ 59
def prefixEnd_869810 : Nat := 4983230072969 + 3 ^ 40 * 869810 * 2
def baseEnd_869810 : Nat := 297753738724898065383215

theorem tailTrace_869810 : CollatzResearch.WordTrace tailWord_869810 prefixEnd_869810 297753738724898065383215 := by
  unfold tailWord_869810
  simp only [CollatzResearch.WordTrace]
  refine ⟨7931144244708599141575721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21149717985889597710868589 7931144244708599141575721)
  ·
    refine ⟨5948358183531449356181791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7931144244708599141575721 5948358183531449356181791)
    ·
      refine ⟨8922537275297174034272687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5948358183531449356181791 8922537275297174034272687)
      ·
        refine ⟨13383805912945761051409031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8922537275297174034272687 13383805912945761051409031)
        ·
          refine ⟨20075708869418641577113547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13383805912945761051409031 20075708869418641577113547)
          ·
            refine ⟨30113563304127962365670321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20075708869418641577113547 30113563304127962365670321)
            ·
              refine ⟨22585172478095971774252741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30113563304127962365670321 22585172478095971774252741)
              ·
                refine ⟨4234719839642994707672389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22585172478095971774252741 4234719839642994707672389)
                ·
                  refine ⟨794009969933061507688573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4234719839642994707672389 794009969933061507688573)
                  ·
                    refine ⟨297753738724898065383215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 794009969933061507688573 297753738724898065383215)
                    ·
                      rfl

theorem cell22_869810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4, 4, 3].length) (baseStart_869810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_869810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_869810 prefixEnd_869810 := by exact prefixLift 869810
  have htrace : WordTrace (prefixWord ++ tailWord_869810) baseStart_869810 baseEnd_869810 := by
    simpa [prefixWord, tailWord_869810, baseEnd_869810] using wordTrace_append hprefix tailTrace_869810
  have hstable : (prefixWord ++ tailWord_869810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869810).length < 2 ^ (prefixWord ++ tailWord_869810).sum := by decide
  have hdescent : baseEnd_869810 < baseStart_869810 := by decide
  rcases family_descends (prefixWord ++ tailWord_869810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869883 : List Nat := [1, 1, 1, 1, 1, 3, 2, 2, 3, 7]
def baseStart_869883 : Nat := 118140960795 + 869883 * 2 ^ 59
def prefixEnd_869883 : Nat := 4983230072969 + 3 ^ 40 * 869883 * 2
def baseEnd_869883 : Nat := 297778728116750208307991

theorem tailTrace_869883 : CollatzResearch.WordTrace tailWord_869883 prefixEnd_869883 297778728116750208307991 := by
  unfold tailWord_869883
  simp only [CollatzResearch.WordTrace]
  refine ⟨31727239507569930033710303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21151493005046620022473535 31727239507569930033710303)
  ·
    refine ⟨47590859261354895050565455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31727239507569930033710303 47590859261354895050565455)
    ·
      refine ⟨71386288892032342575848183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47590859261354895050565455 71386288892032342575848183)
      ·
        refine ⟨107079433338048513863772275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71386288892032342575848183 107079433338048513863772275)
        ·
          refine ⟨160619150007072770795658413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107079433338048513863772275 160619150007072770795658413)
          ·
            refine ⟨60232181252652289048371905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160619150007072770795658413 60232181252652289048371905)
            ·
              refine ⟨45174135939489216786278929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60232181252652289048371905 45174135939489216786278929)
              ·
                refine ⟨33880601954616912589709197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45174135939489216786278929 33880601954616912589709197)
                ·
                  refine ⟨12705225732981342221140949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33880601954616912589709197 12705225732981342221140949)
                  ·
                    refine ⟨297778728116750208307991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12705225732981342221140949 297778728116750208307991)
                    ·
                      rfl

theorem cell22_869883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 7].length) (baseStart_869883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_869883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_869883 prefixEnd_869883 := by exact prefixLift 869883
  have htrace : WordTrace (prefixWord ++ tailWord_869883) baseStart_869883 baseEnd_869883 := by
    simpa [prefixWord, tailWord_869883, baseEnd_869883] using wordTrace_append hprefix tailTrace_869883
  have hstable : (prefixWord ++ tailWord_869883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869883).length < 2 ^ (prefixWord ++ tailWord_869883).sum := by decide
  have hdescent : baseEnd_869883 < baseStart_869883 := by decide
  rcases family_descends (prefixWord ++ tailWord_869883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869885 : List Nat := [1, 4, 1, 1, 1, 5, 1, 1, 7]
def baseStart_869885 : Nat := 118140960795 + 869885 * 2 ^ 59
def prefixEnd_869885 : Nat := 4983230072969 + 3 ^ 40 * 869885 * 2
def baseEnd_869885 : Nat := 99259804252540956585995

theorem tailTrace_869885 : CollatzResearch.WordTrace tailWord_869885 prefixEnd_869885 99259804252540956585995 := by
  unfold tailWord_869885
  simp only [CollatzResearch.WordTrace]
  refine ⟨31727312453562684375283109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21151541635708456250188739 31727312453562684375283109)
  ·
    refine ⟨5948871085043003320365583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31727312453562684375283109 5948871085043003320365583)
    ·
      refine ⟨8923306627564504980548375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5948871085043003320365583 8923306627564504980548375)
      ·
        refine ⟨13384959941346757470822563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8923306627564504980548375 13384959941346757470822563)
        ·
          refine ⟨20077439912020136206233845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13384959941346757470822563 20077439912020136206233845)
          ·
            refine ⟨1882259991751887769334423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20077439912020136206233845 1882259991751887769334423)
            ·
              refine ⟨2823389987627831654001635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1882259991751887769334423 2823389987627831654001635)
              ·
                refine ⟨4235084981441747481002453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2823389987627831654001635 4235084981441747481002453)
                ·
                  refine ⟨99259804252540956585995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4235084981441747481002453 99259804252540956585995)
                  ·
                    rfl

theorem cell22_869885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 1, 7].length) (baseStart_869885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_869885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_869885 prefixEnd_869885 := by exact prefixLift 869885
  have htrace : WordTrace (prefixWord ++ tailWord_869885) baseStart_869885 baseEnd_869885 := by
    simpa [prefixWord, tailWord_869885, baseEnd_869885] using wordTrace_append hprefix tailTrace_869885
  have hstable : (prefixWord ++ tailWord_869885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869885).length < 2 ^ (prefixWord ++ tailWord_869885).sum := by decide
  have hdescent : baseEnd_869885 < baseStart_869885 := by decide
  rcases family_descends (prefixWord ++ tailWord_869885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869889 : List Nat := [1, 2, 4, 1, 4, 1, 2, 1, 3, 3]
def baseStart_869889 : Nat := 118140960795 + 869889 * 2 ^ 59
def prefixEnd_869889 : Nat := 4983230072969 + 3 ^ 40 * 869889 * 2
def baseEnd_869889 : Nat := 297780782039368192657973

theorem tailTrace_869889 : CollatzResearch.WordTrace tailWord_869889 prefixEnd_869889 297780782039368192657973 := by
  unfold tailWord_869889
  simp only [CollatzResearch.WordTrace]
  refine ⟨31727458345548193058428721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21151638897032128705619147 31727458345548193058428721)
  ·
    refine ⟨23795593759161144793821541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31727458345548193058428721 23795593759161144793821541)
    ·
      refine ⟨4461673829842714648841539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23795593759161144793821541 4461673829842714648841539)
      ·
        refine ⟨6692510744764071973262309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4461673829842714648841539 6692510744764071973262309)
        ·
          refine ⟨1254845764643263494986683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6692510744764071973262309 1254845764643263494986683)
          ·
            refine ⟨1882268646964895242480025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1254845764643263494986683 1882268646964895242480025)
            ·
              refine ⟨1411701485223671431860019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1882268646964895242480025 1411701485223671431860019)
              ·
                refine ⟨2117552227835507147790029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1411701485223671431860019 2117552227835507147790029)
                ·
                  refine ⟨794082085438315180421261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2117552227835507147790029 794082085438315180421261)
                  ·
                    refine ⟨297780782039368192657973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 794082085438315180421261 297780782039368192657973)
                    ·
                      rfl

theorem cell22_869889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 1, 3, 3].length) (baseStart_869889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_869889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_869889 prefixEnd_869889 := by exact prefixLift 869889
  have htrace : WordTrace (prefixWord ++ tailWord_869889) baseStart_869889 baseEnd_869889 := by
    simpa [prefixWord, tailWord_869889, baseEnd_869889] using wordTrace_append hprefix tailTrace_869889
  have hstable : (prefixWord ++ tailWord_869889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869889).length < 2 ^ (prefixWord ++ tailWord_869889).sum := by decide
  have hdescent : baseEnd_869889 < baseStart_869889 := by decide
  rcases family_descends (prefixWord ++ tailWord_869889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869923 : List Nat := [1, 1, 1, 4, 6, 1, 1, 3, 1, 3]
def baseStart_869923 : Nat := 118140960795 + 869923 * 2 ^ 59
def prefixEnd_869923 : Nat := 4983230072969 + 3 ^ 40 * 869923 * 2
def baseEnd_869923 : Nat := 297792420934203437307869

theorem tailTrace_869923 : CollatzResearch.WordTrace tailWord_869923 prefixEnd_869923 297792420934203437307869 := by
  unfold tailWord_869923
  simp only [CollatzResearch.WordTrace]
  refine ⟨31728698427425016865166423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21152465618283344576777615 31728698427425016865166423)
  ·
    refine ⟨47593047641137525297749635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31728698427425016865166423 47593047641137525297749635)
    ·
      refine ⟨71389571461706287946624453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47593047641137525297749635 71389571461706287946624453)
      ·
        refine ⟨13385544649069928989992085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71389571461706287946624453 13385544649069928989992085)
        ·
          refine ⟨627447405425152921405879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13385544649069928989992085 627447405425152921405879)
          ·
            refine ⟨941171108137729382108819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 627447405425152921405879 941171108137729382108819)
            ·
              refine ⟨1411756662206594073163229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 941171108137729382108819 1411756662206594073163229)
              ·
                refine ⟨529408748327472777436211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1411756662206594073163229 529408748327472777436211)
                ·
                  refine ⟨794113122491209166154317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 529408748327472777436211 794113122491209166154317)
                  ·
                    refine ⟨297792420934203437307869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 794113122491209166154317 297792420934203437307869)
                    ·
                      rfl

theorem cell22_869923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 3, 1, 3].length) (baseStart_869923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_869923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_869923 prefixEnd_869923 := by exact prefixLift 869923
  have htrace : WordTrace (prefixWord ++ tailWord_869923) baseStart_869923 baseEnd_869923 := by
    simpa [prefixWord, tailWord_869923, baseEnd_869923] using wordTrace_append hprefix tailTrace_869923
  have hstable : (prefixWord ++ tailWord_869923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869923).length < 2 ^ (prefixWord ++ tailWord_869923).sum := by decide
  have hdescent : baseEnd_869923 < baseStart_869923 := by decide
  rcases family_descends (prefixWord ++ tailWord_869923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869975 : List Nat := [1, 1, 3, 2, 2, 3, 2, 8]
def baseStart_869975 : Nat := 118140960795 + 869975 * 2 ^ 59
def prefixEnd_869975 : Nat := 4983230072969 + 3 ^ 40 * 869975 * 2
def baseEnd_869975 : Nat := 33090024621876959445301

theorem tailTrace_869975 : CollatzResearch.WordTrace tailWord_869975 prefixEnd_869975 33090024621876959445301 := by
  unfold tailWord_869975
  simp only [CollatzResearch.WordTrace]
  refine ⟨31730595023236629746059379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21153730015491086497372919 31730595023236629746059379)
  ·
    refine ⟨47595892534854944619089069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31730595023236629746059379 47595892534854944619089069)
    ·
      refine ⟨17848459700570604232158401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47595892534854944619089069 17848459700570604232158401)
      ·
        refine ⟨13386344775427953174118801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17848459700570604232158401 13386344775427953174118801)
        ·
          refine ⟨10039758581570964880589101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13386344775427953174118801 10039758581570964880589101)
          ·
            refine ⟨3764909468089111830220913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10039758581570964880589101 3764909468089111830220913)
            ·
              refine ⟨2823682101066833872665685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3764909468089111830220913 2823682101066833872665685)
              ·
                refine ⟨33090024621876959445301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2823682101066833872665685 33090024621876959445301)
                ·
                  rfl

theorem cell22_869975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 8].length) (baseStart_869975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_869975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_869975 prefixEnd_869975 := by exact prefixLift 869975
  have htrace : WordTrace (prefixWord ++ tailWord_869975) baseStart_869975 baseEnd_869975 := by
    simpa [prefixWord, tailWord_869975, baseEnd_869975] using wordTrace_append hprefix tailTrace_869975
  have hstable : (prefixWord ++ tailWord_869975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869975).length < 2 ^ (prefixWord ++ tailWord_869975).sum := by decide
  have hdescent : baseEnd_869975 < baseStart_869975 := by decide
  rcases family_descends (prefixWord ++ tailWord_869975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869998 : List Nat := [4, 1, 2, 2, 3, 2, 2, 2, 4]
def baseStart_869998 : Nat := 118140960795 + 869998 * 2 ^ 59
def prefixEnd_869998 : Nat := 4983230072969 + 3 ^ 40 * 869998 * 2
def baseEnd_869998 : Nat := 99272698322309413894213

theorem tailTrace_869998 : CollatzResearch.WordTrace tailWord_869998 prefixEnd_869998 99272698322309413894213 := by
  unfold tailWord_869998
  simp only [CollatzResearch.WordTrace]
  refine ⟨3966429237769163084268331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21154289268102203116097765 3966429237769163084268331)
  ·
    refine ⟨5949643856653744626402497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3966429237769163084268331 5949643856653744626402497)
    ·
      refine ⟨4462232892490308469801873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5949643856653744626402497 4462232892490308469801873)
      ·
        refine ⟨3346674669367731352351405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4462232892490308469801873 3346674669367731352351405)
        ·
          refine ⟨1255003001012899257131777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3346674669367731352351405 1255003001012899257131777)
          ·
            refine ⟨941252250759674442848833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1255003001012899257131777 941252250759674442848833)
            ·
              refine ⟨705939188069755832136625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 941252250759674442848833 705939188069755832136625)
              ·
                refine ⟨529454391052316874102469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 705939188069755832136625 529454391052316874102469)
                ·
                  refine ⟨99272698322309413894213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 529454391052316874102469 99272698322309413894213)
                  ·
                    rfl

theorem cell22_869998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 2, 2, 4].length) (baseStart_869998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_869998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_869998 prefixEnd_869998 := by exact prefixLift 869998
  have htrace : WordTrace (prefixWord ++ tailWord_869998) baseStart_869998 baseEnd_869998 := by
    simpa [prefixWord, tailWord_869998, baseEnd_869998] using wordTrace_append hprefix tailTrace_869998
  have hstable : (prefixWord ++ tailWord_869998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869998).length < 2 ^ (prefixWord ++ tailWord_869998).sum := by decide
  have hdescent : baseEnd_869998 < baseStart_869998 := by decide
  rcases family_descends (prefixWord ++ tailWord_869998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870007 : List Nat := [1, 1, 3, 1, 1, 3, 1, 5, 3, 3]
def baseStart_870007 : Nat := 118140960795 + 870007 * 2 ^ 59
def prefixEnd_870007 : Nat := 4983230072969 + 3 ^ 40 * 870007 * 2
def baseEnd_870007 : Nat := 297821175850855218207611

theorem tailTrace_870007 : CollatzResearch.WordTrace tailWord_870007 prefixEnd_870007 297821175850855218207611 := by
  unfold tailWord_870007
  simp only [CollatzResearch.WordTrace]
  refine ⟨31731762159120699211224275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21154508106080466140816183 31731762159120699211224275)
  ·
    refine ⟨47597643238681048816836413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31731762159120699211224275 47597643238681048816836413)
    ·
      refine ⟨17849116214505393306313655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47597643238681048816836413 17849116214505393306313655)
      ·
        refine ⟨26773674321758089959470483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17849116214505393306313655 26773674321758089959470483)
        ·
          refine ⟨40160511482637134939205725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26773674321758089959470483 40160511482637134939205725)
          ·
            refine ⟨15060191805988925602202147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40160511482637134939205725 15060191805988925602202147)
            ·
              refine ⟨22590287708983388403303221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15060191805988925602202147 22590287708983388403303221)
              ·
                refine ⟨2117839472717192662809677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22590287708983388403303221 2117839472717192662809677)
                ·
                  refine ⟨794189802268947248553629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2117839472717192662809677 794189802268947248553629)
                  ·
                    refine ⟨297821175850855218207611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 794189802268947248553629 297821175850855218207611)
                    ·
                      rfl

theorem cell22_870007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 5, 3, 3].length) (baseStart_870007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_870007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_870007 prefixEnd_870007 := by exact prefixLift 870007
  have htrace : WordTrace (prefixWord ++ tailWord_870007) baseStart_870007 baseEnd_870007 := by
    simpa [prefixWord, tailWord_870007, baseEnd_870007] using wordTrace_append hprefix tailTrace_870007
  have hstable : (prefixWord ++ tailWord_870007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870007).length < 2 ^ (prefixWord ++ tailWord_870007).sum := by decide
  have hdescent : baseEnd_870007 < baseStart_870007 := by decide
  rcases family_descends (prefixWord ++ tailWord_870007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870035 : List Nat := [1, 1, 1, 2, 1, 2, 2, 1, 6, 5]
def baseStart_870035 : Nat := 118140960795 + 870035 * 2 ^ 59
def prefixEnd_870035 : Nat := 4983230072969 + 3 ^ 40 * 870035 * 2
def baseEnd_870035 : Nat := 297830760823072478507525

theorem tailTrace_870035 : CollatzResearch.WordTrace tailWord_870035 prefixEnd_870035 297830760823072478507525 := by
  unfold tailWord_870035
  simp only [CollatzResearch.WordTrace]
  refine ⟨31732783403019259993243559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21155188935346173328829039 31732783403019259993243559)
  ·
    refine ⟨47599175104528889989865339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31732783403019259993243559 47599175104528889989865339)
    ·
      refine ⟨71398762656793334984798009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47599175104528889989865339 71398762656793334984798009)
      ·
        refine ⟨53549071992595001238598507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71398762656793334984798009 53549071992595001238598507)
        ·
          refine ⟨80323607988892501857897761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53549071992595001238598507 80323607988892501857897761)
          ·
            refine ⟨60242705991669376393423321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80323607988892501857897761 60242705991669376393423321)
            ·
              refine ⟨45182029493752032295067491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60242705991669376393423321 45182029493752032295067491)
              ·
                refine ⟨67773044240628048442601237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45182029493752032295067491 67773044240628048442601237)
                ·
                  refine ⟨3176861448779439770746933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 67773044240628048442601237 3176861448779439770746933)
                  ·
                    refine ⟨297830760823072478507525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3176861448779439770746933 297830760823072478507525)
                    ·
                      rfl

theorem cell22_870035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 6, 5].length) (baseStart_870035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_870035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_870035 prefixEnd_870035 := by exact prefixLift 870035
  have htrace : WordTrace (prefixWord ++ tailWord_870035) baseStart_870035 baseEnd_870035 := by
    simpa [prefixWord, tailWord_870035, baseEnd_870035] using wordTrace_append hprefix tailTrace_870035
  have hstable : (prefixWord ++ tailWord_870035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870035).length < 2 ^ (prefixWord ++ tailWord_870035).sum := by decide
  have hdescent : baseEnd_870035 < baseStart_870035 := by decide
  rcases family_descends (prefixWord ++ tailWord_870035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870052 : List Nat := [2, 3, 1, 2, 2, 2, 1, 2, 2, 5]
def baseStart_870052 : Nat := 118140960795 + 870052 * 2 ^ 59
def prefixEnd_870052 : Nat := 4983230072969 + 3 ^ 40 * 870052 * 2
def baseEnd_870052 : Nat := 297836580270490100832473

theorem tailTrace_870052 : CollatzResearch.WordTrace tailWord_870052 prefixEnd_870052 297836580270490100832473 := by
  unfold tailWord_870052
  simp only [CollatzResearch.WordTrace]
  refine ⟨15866701721978835948306205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21155602295971781264408273 15866701721978835948306205)
  ·
    refine ⟨5950013145742063480614827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15866701721978835948306205 5950013145742063480614827)
    ·
      refine ⟨8925019718613095220922241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5950013145742063480614827 8925019718613095220922241)
      ·
        refine ⟨6693764788959821415691681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8925019718613095220922241 6693764788959821415691681)
        ·
          refine ⟨5020323591719866061768761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6693764788959821415691681 5020323591719866061768761)
          ·
            refine ⟨3765242693789899546326571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5020323591719866061768761 3765242693789899546326571)
            ·
              refine ⟨5647864040684849319489857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3765242693789899546326571 5647864040684849319489857)
              ·
                refine ⟨4235898030513636989617393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5647864040684849319489857 4235898030513636989617393)
                ·
                  refine ⟨3176923522885227742213045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4235898030513636989617393 3176923522885227742213045)
                  ·
                    refine ⟨297836580270490100832473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3176923522885227742213045 297836580270490100832473)
                    ·
                      rfl

theorem cell22_870052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 2, 2, 5].length) (baseStart_870052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_870052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_870052 prefixEnd_870052 := by exact prefixLift 870052
  have htrace : WordTrace (prefixWord ++ tailWord_870052) baseStart_870052 baseEnd_870052 := by
    simpa [prefixWord, tailWord_870052, baseEnd_870052] using wordTrace_append hprefix tailTrace_870052
  have hstable : (prefixWord ++ tailWord_870052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870052).length < 2 ^ (prefixWord ++ tailWord_870052).sum := by decide
  have hdescent : baseEnd_870052 < baseStart_870052 := by decide
  rcases family_descends (prefixWord ++ tailWord_870052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870112 : List Nat := [2, 1, 1, 3, 1, 2, 3, 1, 4, 4]
def baseStart_870112 : Nat := 118140960795 + 870112 * 2 ^ 59
def prefixEnd_870112 : Nat := 4983230072969 + 3 ^ 40 * 870112 * 2
def baseEnd_870112 : Nat := 297857119496669944332289

theorem tailTrace_870112 : CollatzResearch.WordTrace tailWord_870112 prefixEnd_870112 297857119496669944332289 := by
  unfold tailWord_870112
  simp only [CollatzResearch.WordTrace]
  refine ⟨15867795911870151071898295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21157061215826868095864393 15867795911870151071898295)
  ·
    refine ⟨23801693867805226607847443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15867795911870151071898295 23801693867805226607847443)
    ·
      refine ⟨35702540801707839911771165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23801693867805226607847443 35702540801707839911771165)
      ·
        refine ⟨13388452800640439966914187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35702540801707839911771165 13388452800640439966914187)
        ·
          refine ⟨20082679200960659950371281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13388452800640439966914187 20082679200960659950371281)
          ·
            refine ⟨15062009400720494962778461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20082679200960659950371281 15062009400720494962778461)
            ·
              refine ⟨5648253525270185611041923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15062009400720494962778461 5648253525270185611041923)
              ·
                refine ⟨8472380287905278416562885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5648253525270185611041923 8472380287905278416562885)
                ·
                  refine ⟨1588571303982239703105541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8472380287905278416562885 1588571303982239703105541)
                  ·
                    refine ⟨297857119496669944332289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1588571303982239703105541 297857119496669944332289)
                    ·
                      rfl

theorem cell22_870112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 4, 4].length) (baseStart_870112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_870112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_870112 prefixEnd_870112 := by exact prefixLift 870112
  have htrace : WordTrace (prefixWord ++ tailWord_870112) baseStart_870112 baseEnd_870112 := by
    simpa [prefixWord, tailWord_870112, baseEnd_870112] using wordTrace_append hprefix tailTrace_870112
  have hstable : (prefixWord ++ tailWord_870112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870112).length < 2 ^ (prefixWord ++ tailWord_870112).sum := by decide
  have hdescent : baseEnd_870112 < baseStart_870112 := by decide
  rcases family_descends (prefixWord ++ tailWord_870112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870116 : List Nat := [2, 3, 1, 1, 1, 3, 5, 2, 4]
def baseStart_870116 : Nat := 118140960795 + 870116 * 2 ^ 59
def prefixEnd_870116 : Nat := 4983230072969 + 3 ^ 40 * 870116 * 2
def baseEnd_870116 : Nat := 99286162926138422410759

theorem tailTrace_870116 : CollatzResearch.WordTrace tailWord_870116 prefixEnd_870116 99286162926138422410759 := by
  unfold tailWord_870116
  simp only [CollatzResearch.WordTrace]
  refine ⟨15867868857862905413471101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21157158477150540551294801 15867868857862905413471101)
  ·
    refine ⟨5950450821698589530051663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15867868857862905413471101 5950450821698589530051663)
    ·
      refine ⟨8925676232547884295077495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5950450821698589530051663 8925676232547884295077495)
      ·
        refine ⟨13388514348821826442616243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8925676232547884295077495 13388514348821826442616243)
        ·
          refine ⟨20082771523232739663924365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13388514348821826442616243 20082771523232739663924365)
          ·
            refine ⟨7531039321212277373971637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20082771523232739663924365 7531039321212277373971637)
            ·
              refine ⟨706034936363651003809841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7531039321212277373971637 706034936363651003809841)
              ·
                refine ⟨529526202272738252857381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 706034936363651003809841 529526202272738252857381)
                ·
                  refine ⟨99286162926138422410759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 529526202272738252857381 99286162926138422410759)
                  ·
                    rfl

theorem cell22_870116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 5, 2, 4].length) (baseStart_870116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_870116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_870116 prefixEnd_870116 := by exact prefixLift 870116
  have htrace : WordTrace (prefixWord ++ tailWord_870116) baseStart_870116 baseEnd_870116 := by
    simpa [prefixWord, tailWord_870116, baseEnd_870116] using wordTrace_append hprefix tailTrace_870116
  have hstable : (prefixWord ++ tailWord_870116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870116).length < 2 ^ (prefixWord ++ tailWord_870116).sum := by decide
  have hdescent : baseEnd_870116 < baseStart_870116 := by decide
  rcases family_descends (prefixWord ++ tailWord_870116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870127 : List Nat := [1, 1, 2, 1, 5, 1, 4, 7]
def baseStart_870127 : Nat := 118140960795 + 870127 * 2 ^ 59
def prefixEnd_870127 : Nat := 4983230072969 + 3 ^ 40 * 870127 * 2
def baseEnd_870127 : Nat := 33095806033690545023027

theorem tailTrace_870127 : CollatzResearch.WordTrace tailWord_870127 prefixEnd_870127 33095806033690545023027 := by
  unfold tailWord_870127
  simp only [CollatzResearch.WordTrace]
  refine ⟨31736138918685959705592635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21157425945790639803728423 31736138918685959705592635)
  ·
    refine ⟨47604208378028939558388953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31736138918685959705592635 47604208378028939558388953)
    ·
      refine ⟨35703156283521704668791715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47604208378028939558388953 35703156283521704668791715)
      ·
        refine ⟨53554734425282557003187573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35703156283521704668791715 53554734425282557003187573)
        ·
          refine ⟨5020756352370239719048835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53554734425282557003187573 5020756352370239719048835)
          ·
            refine ⟨7531134528555359578573253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5020756352370239719048835 7531134528555359578573253)
            ·
              refine ⟨1412087724104129920982485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7531134528555359578573253 1412087724104129920982485)
              ·
                refine ⟨33095806033690545023027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1412087724104129920982485 33095806033690545023027)
                ·
                  rfl

theorem cell22_870127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 7].length) (baseStart_870127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_870127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_870127 prefixEnd_870127 := by exact prefixLift 870127
  have htrace : WordTrace (prefixWord ++ tailWord_870127) baseStart_870127 baseEnd_870127 := by
    simpa [prefixWord, tailWord_870127, baseEnd_870127] using wordTrace_append hprefix tailTrace_870127
  have hstable : (prefixWord ++ tailWord_870127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870127).length < 2 ^ (prefixWord ++ tailWord_870127).sum := by decide
  have hdescent : baseEnd_870127 < baseStart_870127 := by decide
  rcases family_descends (prefixWord ++ tailWord_870127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870131 : List Nat := [1, 1, 1, 2, 2, 3, 6, 1, 2, 3]
def baseStart_870131 : Nat := 118140960795 + 870131 * 2 ^ 59
def prefixEnd_870131 : Nat := 4983230072969 + 3 ^ 40 * 870131 * 2
def baseEnd_870131 : Nat := 297863623584960228107231

theorem tailTrace_870131 : CollatzResearch.WordTrace tailWord_870131 prefixEnd_870131 297863623584960228107231 := by
  unfold tailWord_870131
  simp only [CollatzResearch.WordTrace]
  refine ⟨31736284810671468388738247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21157523207114312259158831 31736284810671468388738247)
  ·
    refine ⟨47604427216007202583107371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31736284810671468388738247 47604427216007202583107371)
    ·
      refine ⟨71406640824010803874661057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47604427216007202583107371 71406640824010803874661057)
      ·
        refine ⟨53554980618008102905995793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71406640824010803874661057 53554980618008102905995793)
        ·
          refine ⟨40166235463506077179496845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53554980618008102905995793 40166235463506077179496845)
          ·
            refine ⟨15062338298814778942311317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40166235463506077179496845 15062338298814778942311317)
            ·
              refine ⟨706047107756942762920843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15062338298814778942311317 706047107756942762920843)
              ·
                refine ⟨1059070661635414144381265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 706047107756942762920843 1059070661635414144381265)
                ·
                  refine ⟨794302996226560608285949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1059070661635414144381265 794302996226560608285949)
                  ·
                    refine ⟨297863623584960228107231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 794302996226560608285949 297863623584960228107231)
                    ·
                      rfl

theorem cell22_870131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 6, 1, 2, 3].length) (baseStart_870131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_870131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_870131 prefixEnd_870131 := by exact prefixLift 870131
  have htrace : WordTrace (prefixWord ++ tailWord_870131) baseStart_870131 baseEnd_870131 := by
    simpa [prefixWord, tailWord_870131, baseEnd_870131] using wordTrace_append hprefix tailTrace_870131
  have hstable : (prefixWord ++ tailWord_870131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870131).length < 2 ^ (prefixWord ++ tailWord_870131).sum := by decide
  have hdescent : baseEnd_870131 < baseStart_870131 := by decide
  rcases family_descends (prefixWord ++ tailWord_870131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870146 : List Nat := [3, 4, 1, 1, 1, 1, 4, 1, 2, 4]
def baseStart_870146 : Nat := 118140960795 + 870146 * 2 ^ 59
def prefixEnd_870146 : Nat := 4983230072969 + 3 ^ 40 * 870146 * 2
def baseEnd_870146 : Nat := 297868758391505188982185

theorem tailTrace_870146 : CollatzResearch.WordTrace tailWord_870146 prefixEnd_870146 297868758391505188982185 := by
  unfold tailWord_870146
  simp only [CollatzResearch.WordTrace]
  refine ⟨7934207976404281487633573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21157887937078083967022861 7934207976404281487633573)
  ·
    refine ⟨1487663995575802778931295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7934207976404281487633573 1487663995575802778931295)
    ·
      refine ⟨2231495993363704168396943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1487663995575802778931295 2231495993363704168396943)
      ·
        refine ⟨3347243990045556252595415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2231495993363704168396943 3347243990045556252595415)
        ·
          refine ⟨5020865985068334378893123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3347243990045556252595415 5020865985068334378893123)
          ·
            refine ⟨7531298977602501568339685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5020865985068334378893123 7531298977602501568339685)
            ·
              refine ⟨1412118558300469044063691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7531298977602501568339685 1412118558300469044063691)
              ·
                refine ⟨2118177837450703566095537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1412118558300469044063691 2118177837450703566095537)
                ·
                  refine ⟨1588633378088027674571653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2118177837450703566095537 1588633378088027674571653)
                  ·
                    refine ⟨297868758391505188982185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1588633378088027674571653 297868758391505188982185)
                    ·
                      rfl

theorem cell22_870146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_870146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_870146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_870146 prefixEnd_870146 := by exact prefixLift 870146
  have htrace : WordTrace (prefixWord ++ tailWord_870146) baseStart_870146 baseEnd_870146 := by
    simpa [prefixWord, tailWord_870146, baseEnd_870146] using wordTrace_append hprefix tailTrace_870146
  have hstable : (prefixWord ++ tailWord_870146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870146).length < 2 ^ (prefixWord ++ tailWord_870146).sum := by decide
  have hdescent : baseEnd_870146 < baseStart_870146 := by decide
  rcases family_descends (prefixWord ++ tailWord_870146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870217 : List Nat := [1, 2, 1, 1, 2, 4, 1, 2, 8]
def baseStart_870217 : Nat := 118140960795 + 870217 * 2 ^ 59
def prefixEnd_870217 : Nat := 4983230072969 + 3 ^ 40 * 870217 * 2
def baseEnd_870217 : Nat := 99297687714161556818989

theorem tailTrace_870217 : CollatzResearch.WordTrace tailWord_870217 prefixEnd_870217 99297687714161556818989 := by
  unfold tailWord_870217
  simp only [CollatzResearch.WordTrace]
  refine ⟨31739421488359905076368905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21159614325573270050912603 31739421488359905076368905)
  ·
    refine ⟨23804566116269928807276679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31739421488359905076368905 23804566116269928807276679)
    ·
      refine ⟨35706849174404893210915019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23804566116269928807276679 35706849174404893210915019)
      ·
        refine ⟨53560273761607339816372529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35706849174404893210915019 53560273761607339816372529)
        ·
          refine ⟨40170205321205504862279397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53560273761607339816372529 40170205321205504862279397)
          ·
            refine ⟨7531913497726032161677387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40170205321205504862279397 7531913497726032161677387)
            ·
              refine ⟨11297870246589048242516081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7531913497726032161677387 11297870246589048242516081)
              ·
                refine ⟨8473402684941786181887061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11297870246589048242516081 8473402684941786181887061)
                ·
                  refine ⟨99297687714161556818989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8473402684941786181887061 99297687714161556818989)
                  ·
                    rfl

theorem cell22_870217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 8].length) (baseStart_870217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_870217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_870217 prefixEnd_870217 := by exact prefixLift 870217
  have htrace : WordTrace (prefixWord ++ tailWord_870217) baseStart_870217 baseEnd_870217 := by
    simpa [prefixWord, tailWord_870217, baseEnd_870217] using wordTrace_append hprefix tailTrace_870217
  have hstable : (prefixWord ++ tailWord_870217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870217).length < 2 ^ (prefixWord ++ tailWord_870217).sum := by decide
  have hdescent : baseEnd_870217 < baseStart_870217 := by decide
  rcases family_descends (prefixWord ++ tailWord_870217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870221 : List Nat := [1, 6, 1, 2, 1, 1, 1, 2, 2, 5]
def baseStart_870221 : Nat := 118140960795 + 870221 * 2 ^ 59
def prefixEnd_870221 : Nat := 4983230072969 + 3 ^ 40 * 870221 * 2
def baseEnd_870221 : Nat := 297894432424229993356955

theorem tailTrace_870221 : CollatzResearch.WordTrace tailWord_870221 prefixEnd_870221 297894432424229993356955 := by
  unfold tailWord_870221
  simp only [CollatzResearch.WordTrace]
  refine ⟨31739567380345413759514517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21159711586896942506343011 31739567380345413759514517)
  ·
    refine ⟨1487792220953691269977243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 31739567380345413759514517 1487792220953691269977243)
    ·
      refine ⟨2231688331430536904965865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1487792220953691269977243 2231688331430536904965865)
      ·
        refine ⟨1673766248572902678724399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2231688331430536904965865 1673766248572902678724399)
        ·
          refine ⟨2510649372859354018086599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1673766248572902678724399 2510649372859354018086599)
          ·
            refine ⟨3765974059289031027129899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2510649372859354018086599 3765974059289031027129899)
            ·
              refine ⟨5648961088933546540694849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3765974059289031027129899 5648961088933546540694849)
              ·
                refine ⟨4236720816700159905521137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5648961088933546540694849 4236720816700159905521137)
                ·
                  refine ⟨3177540612525119929140853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4236720816700159905521137 3177540612525119929140853)
                  ·
                    refine ⟨297894432424229993356955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3177540612525119929140853 297894432424229993356955)
                    ·
                      rfl

theorem cell22_870221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_870221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_870221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_870221 prefixEnd_870221 := by exact prefixLift 870221
  have htrace : WordTrace (prefixWord ++ tailWord_870221) baseStart_870221 baseEnd_870221 := by
    simpa [prefixWord, tailWord_870221, baseEnd_870221] using wordTrace_append hprefix tailTrace_870221
  have hstable : (prefixWord ++ tailWord_870221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870221).length < 2 ^ (prefixWord ++ tailWord_870221).sum := by decide
  have hdescent : baseEnd_870221 < baseStart_870221 := by decide
  rcases family_descends (prefixWord ++ tailWord_870221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870232 : List Nat := [2, 1, 2, 2, 1, 1, 1, 1, 2, 9]
def baseStart_870232 : Nat := 118140960795 + 870232 * 2 ^ 59
def prefixEnd_870232 : Nat := 4983230072969 + 3 ^ 40 * 870232 * 2
def baseEnd_870232 : Nat := 297898197949029631331921

theorem tailTrace_870232 : CollatzResearch.WordTrace tailWord_870232 prefixEnd_870232 297898197949029631331921 := by
  unfold tailWord_870232
  simp only [CollatzResearch.WordTrace]
  refine ⟨15869984291652781319082475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21159979055537041758776633 15869984291652781319082475)
  ·
    refine ⟨23804976437479171978623713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15869984291652781319082475 23804976437479171978623713)
    ·
      refine ⟨17853732328109378983967785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23804976437479171978623713 17853732328109378983967785)
      ·
        refine ⟨13390299246082034237975839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17853732328109378983967785 13390299246082034237975839)
        ·
          refine ⟨20085448869123051356963759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13390299246082034237975839 20085448869123051356963759)
          ·
            refine ⟨30128173303684577035445639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20085448869123051356963759 30128173303684577035445639)
            ·
              refine ⟨45192259955526865553168459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30128173303684577035445639 45192259955526865553168459)
              ·
                refine ⟨67788389933290298329752689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45192259955526865553168459 67788389933290298329752689)
                ·
                  refine ⟨50841292449967723747314517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67788389933290298329752689 50841292449967723747314517)
                  ·
                    refine ⟨297898197949029631331921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 50841292449967723747314517 297898197949029631331921)
                    ·
                      rfl

theorem cell22_870232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 2, 9].length) (baseStart_870232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_870232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_870232 prefixEnd_870232 := by exact prefixLift 870232
  have htrace : WordTrace (prefixWord ++ tailWord_870232) baseStart_870232 baseEnd_870232 := by
    simpa [prefixWord, tailWord_870232, baseEnd_870232] using wordTrace_append hprefix tailTrace_870232
  have hstable : (prefixWord ++ tailWord_870232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870232).length < 2 ^ (prefixWord ++ tailWord_870232).sum := by decide
  have hdescent : baseEnd_870232 < baseStart_870232 := by decide
  rcases family_descends (prefixWord ++ tailWord_870232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870234 : List Nat := [3, 1, 1, 2, 1, 3, 4, 1, 6]
def baseStart_870234 : Nat := 118140960795 + 870234 * 2 ^ 59
def prefixEnd_870234 : Nat := 4983230072969 + 3 ^ 40 * 870234 * 2
def baseEnd_870234 : Nat := 99299627529967430927305

theorem tailTrace_870234 : CollatzResearch.WordTrace tailWord_870234 prefixEnd_870234 99299627529967430927305 := by
  unfold tailWord_870234
  simp only [CollatzResearch.WordTrace]
  refine ⟨7935010382324579244934439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21160027686198877986491837 7935010382324579244934439)
  ·
    refine ⟨11902515573486868867401659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7935010382324579244934439 11902515573486868867401659)
    ·
      refine ⟨17853773360230303301102489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11902515573486868867401659 17853773360230303301102489)
      ·
        refine ⟨13390330020172727475826867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17853773360230303301102489 13390330020172727475826867)
        ·
          refine ⟨20085495030259091213740301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13390330020172727475826867 20085495030259091213740301)
          ·
            refine ⟨7532060636347159205152613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20085495030259091213740301 7532060636347159205152613)
            ·
              refine ⟨1412261369315092350966115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7532060636347159205152613 1412261369315092350966115)
              ·
                refine ⟨2118392053972638526449173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1412261369315092350966115 2118392053972638526449173)
                ·
                  refine ⟨99299627529967430927305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2118392053972638526449173 99299627529967430927305)
                  ·
                    rfl

theorem cell22_870234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 1, 6].length) (baseStart_870234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_870234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_870234 prefixEnd_870234 := by exact prefixLift 870234
  have htrace : WordTrace (prefixWord ++ tailWord_870234) baseStart_870234 baseEnd_870234 := by
    simpa [prefixWord, tailWord_870234, baseEnd_870234] using wordTrace_append hprefix tailTrace_870234
  have hstable : (prefixWord ++ tailWord_870234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870234).length < 2 ^ (prefixWord ++ tailWord_870234).sum := by decide
  have hdescent : baseEnd_870234 < baseStart_870234 := by decide
  rcases family_descends (prefixWord ++ tailWord_870234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870300 : List Nat := [2, 2, 3, 3, 1, 1, 4, 1, 2, 3]
def baseStart_870300 : Nat := 118140960795 + 870300 * 2 ^ 59
def prefixEnd_870300 : Nat := 4983230072969 + 3 ^ 40 * 870300 * 2
def baseEnd_870300 : Nat := 297921475738700120631713

theorem tailTrace_870300 : CollatzResearch.WordTrace tailWord_870300 prefixEnd_870300 297921475738700120631713 := by
  unfold tailWord_870300
  simp only [CollatzResearch.WordTrace]
  refine ⟨15871224373529605125820177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21161632498039473501093569 15871224373529605125820177)
  ·
    refine ⟨11903418280147203844365133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15871224373529605125820177 11903418280147203844365133)
    ·
      refine ⟨4463781855055201441636925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11903418280147203844365133 4463781855055201441636925)
      ·
        refine ⟨1673918195645700540613847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4463781855055201441636925 1673918195645700540613847)
        ·
          refine ⟨2510877293468550810920771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1673918195645700540613847 2510877293468550810920771)
          ·
            refine ⟨3766315940202826216381157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2510877293468550810920771 3766315940202826216381157)
            ·
              refine ⟨706184238788029915571467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3766315940202826216381157 706184238788029915571467)
              ·
                refine ⟨1059276358182044873357201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 706184238788029915571467 1059276358182044873357201)
                ·
                  refine ⟨794457268636533655017901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1059276358182044873357201 794457268636533655017901)
                  ·
                    refine ⟨297921475738700120631713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 794457268636533655017901 297921475738700120631713)
                    ·
                      rfl

theorem cell22_870300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 4, 1, 2, 3].length) (baseStart_870300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_870300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_870300 prefixEnd_870300 := by exact prefixLift 870300
  have htrace : WordTrace (prefixWord ++ tailWord_870300) baseStart_870300 baseEnd_870300 := by
    simpa [prefixWord, tailWord_870300, baseEnd_870300] using wordTrace_append hprefix tailTrace_870300
  have hstable : (prefixWord ++ tailWord_870300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870300).length < 2 ^ (prefixWord ++ tailWord_870300).sum := by decide
  have hdescent : baseEnd_870300 < baseStart_870300 := by decide
  rcases family_descends (prefixWord ++ tailWord_870300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870328 : List Nat := [2, 1, 2, 1, 2, 3, 2, 5, 1, 3]
def baseStart_870328 : Nat := 118140960795 + 870328 * 2 ^ 59
def prefixEnd_870328 : Nat := 4983230072969 + 3 ^ 40 * 870328 * 2
def baseEnd_870328 : Nat := 297931060710917380931627

theorem tailTrace_870328 : CollatzResearch.WordTrace tailWord_870328 prefixEnd_870328 297931060710917380931627 := by
  unfold tailWord_870328
  simp only [CollatzResearch.WordTrace]
  refine ⟨15871734995478885516829819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21162313327305180689106425 15871734995478885516829819)
  ·
    refine ⟨23807602493218328275244729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15871734995478885516829819 23807602493218328275244729)
    ·
      refine ⟨17855701869913746206433547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23807602493218328275244729 17855701869913746206433547)
      ·
        refine ⟨26783552804870619309650321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17855701869913746206433547 26783552804870619309650321)
        ·
          refine ⟨20087664603652964482237741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26783552804870619309650321 20087664603652964482237741)
          ·
            refine ⟨7532874226369861680839153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20087664603652964482237741 7532874226369861680839153)
            ·
              refine ⟨5649655669777396260629365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7532874226369861680839153 5649655669777396260629365)
              ·
                refine ⟨529655219041630899434003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5649655669777396260629365 529655219041630899434003)
                ·
                  refine ⟨794482828562446349151005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 529655219041630899434003 794482828562446349151005)
                  ·
                    refine ⟨297931060710917380931627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 794482828562446349151005 297931060710917380931627)
                    ·
                      rfl

theorem cell22_870328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 5, 1, 3].length) (baseStart_870328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_870328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_870328 prefixEnd_870328 := by exact prefixLift 870328
  have htrace : WordTrace (prefixWord ++ tailWord_870328) baseStart_870328 baseEnd_870328 := by
    simpa [prefixWord, tailWord_870328, baseEnd_870328] using wordTrace_append hprefix tailTrace_870328
  have hstable : (prefixWord ++ tailWord_870328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870328).length < 2 ^ (prefixWord ++ tailWord_870328).sum := by decide
  have hdescent : baseEnd_870328 < baseStart_870328 := by decide
  rcases family_descends (prefixWord ++ tailWord_870328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870356 : List Nat := [2, 4, 1, 2, 1, 1, 3, 1, 2, 5]
def baseStart_870356 : Nat := 118140960795 + 870356 * 2 ^ 59
def prefixEnd_870356 : Nat := 4983230072969 + 3 ^ 40 * 870356 * 2
def baseEnd_870356 : Nat := 297940645683134641231541

theorem tailTrace_870356 : CollatzResearch.WordTrace tailWord_870356 prefixEnd_870356 297940645683134641231541 := by
  unfold tailWord_870356
  simp only [CollatzResearch.WordTrace]
  refine ⟨15872245617428165907839461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21162994156570887877119281 15872245617428165907839461)
  ·
    refine ⟨2976046053267781107719899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15872245617428165907839461 2976046053267781107719899)
    ·
      refine ⟨4464069079901671661579849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2976046053267781107719899 4464069079901671661579849)
      ·
        refine ⟨3348051809926253746184887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4464069079901671661579849 3348051809926253746184887)
        ·
          refine ⟨5022077714889380619277331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3348051809926253746184887 5022077714889380619277331)
          ·
            refine ⟨7533116572334070928915997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5022077714889380619277331 7533116572334070928915997)
            ·
              refine ⟨2824918714625276598343499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7533116572334070928915997 2824918714625276598343499)
              ·
                refine ⟨4237378071937914897515249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2824918714625276598343499 4237378071937914897515249)
                ·
                  refine ⟨3178033553953436173136437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4237378071937914897515249 3178033553953436173136437)
                  ·
                    refine ⟨297940645683134641231541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3178033553953436173136437 297940645683134641231541)
                    ·
                      rfl

theorem cell22_870356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_870356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_870356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_870356 prefixEnd_870356 := by exact prefixLift 870356
  have htrace : WordTrace (prefixWord ++ tailWord_870356) baseStart_870356 baseEnd_870356 := by
    simpa [prefixWord, tailWord_870356, baseEnd_870356] using wordTrace_append hprefix tailTrace_870356
  have hstable : (prefixWord ++ tailWord_870356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870356).length < 2 ^ (prefixWord ++ tailWord_870356).sum := by decide
  have hdescent : baseEnd_870356 < baseStart_870356 := by decide
  rcases family_descends (prefixWord ++ tailWord_870356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870369 : List Nat := [1, 2, 3, 1, 2, 1, 3, 1, 8]
def baseStart_870369 : Nat := 118140960795 + 870369 * 2 ^ 59
def prefixEnd_870369 : Nat := 4983230072969 + 3 ^ 40 * 870369 * 2
def baseEnd_870369 : Nat := 99315031949602313552167

theorem tailTrace_870369 : CollatzResearch.WordTrace tailWord_870369 prefixEnd_870369 99315031949602313552167 := by
  unfold tailWord_870369
  simp only [CollatzResearch.WordTrace]
  refine ⟨31744965383809235035902161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21163310255872823357268107 31744965383809235035902161)
  ·
    refine ⟨23808724037856926276926621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31744965383809235035902161 23808724037856926276926621)
    ·
      refine ⟨8928271514196347353847483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23808724037856926276926621 8928271514196347353847483)
      ·
        refine ⟨13392407271294521030771225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8928271514196347353847483 13392407271294521030771225)
        ·
          refine ⟨10044305453470890773078419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13392407271294521030771225 10044305453470890773078419)
          ·
            refine ⟨15066458180206336159617629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10044305453470890773078419 15066458180206336159617629)
            ·
              refine ⟨5649921817577376059856611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15066458180206336159617629 5649921817577376059856611)
              ·
                refine ⟨8474882726366064089784917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5649921817577376059856611 8474882726366064089784917)
                ·
                  refine ⟨99315031949602313552167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8474882726366064089784917 99315031949602313552167)
                  ·
                    rfl

theorem cell22_870369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 8].length) (baseStart_870369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_870369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_870369 prefixEnd_870369 := by exact prefixLift 870369
  have htrace : WordTrace (prefixWord ++ tailWord_870369) baseStart_870369 baseEnd_870369 := by
    simpa [prefixWord, tailWord_870369, baseEnd_870369] using wordTrace_append hprefix tailTrace_870369
  have hstable : (prefixWord ++ tailWord_870369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870369).length < 2 ^ (prefixWord ++ tailWord_870369).sum := by decide
  have hdescent : baseEnd_870369 < baseStart_870369 := by decide
  rcases family_descends (prefixWord ++ tailWord_870369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870371 : List Nat := [1, 1, 1, 6, 1, 2, 2, 1, 3, 4]
def baseStart_870371 : Nat := 118140960795 + 870371 * 2 ^ 59
def prefixEnd_870371 : Nat := 4983230072969 + 3 ^ 40 * 870371 * 2
def baseEnd_870371 : Nat := 297945780489679602106495

theorem tailTrace_870371 : CollatzResearch.WordTrace tailWord_870371 prefixEnd_870371 297945780489679602106495 := by
  unfold tailWord_870371
  simp only [CollatzResearch.WordTrace]
  refine ⟨31745038329801989377474967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21163358886534659584983311 31745038329801989377474967)
  ·
    refine ⟨47617557494702984066212451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31745038329801989377474967 47617557494702984066212451)
    ·
      refine ⟨71426336242054476099318677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47617557494702984066212451 71426336242054476099318677)
      ·
        refine ⟨3348109511346303567155563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 71426336242054476099318677 3348109511346303567155563)
        ·
          refine ⟨5022164267019455350733345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3348109511346303567155563 5022164267019455350733345)
          ·
            refine ⟨3766623200264591513050009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5022164267019455350733345 3766623200264591513050009)
            ·
              refine ⟨2824967400198443634787507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3766623200264591513050009 2824967400198443634787507)
              ·
                refine ⟨4237451100297665452181261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2824967400198443634787507 4237451100297665452181261)
                ·
                  refine ⟨1589044162611624544567973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4237451100297665452181261 1589044162611624544567973)
                  ·
                    refine ⟨297945780489679602106495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1589044162611624544567973 297945780489679602106495)
                    ·
                      rfl

theorem cell22_870371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 1, 3, 4].length) (baseStart_870371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_870371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_870371 prefixEnd_870371 := by exact prefixLift 870371
  have htrace : WordTrace (prefixWord ++ tailWord_870371) baseStart_870371 baseEnd_870371 := by
    simpa [prefixWord, tailWord_870371, baseEnd_870371] using wordTrace_append hprefix tailTrace_870371
  have hstable : (prefixWord ++ tailWord_870371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870371).length < 2 ^ (prefixWord ++ tailWord_870371).sum := by decide
  have hdescent : baseEnd_870371 < baseStart_870371 := by decide
  rcases family_descends (prefixWord ++ tailWord_870371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870461 : List Nat := [1, 4, 1, 3, 1, 1, 2, 1, 2, 6]
def baseStart_870461 : Nat := 118140960795 + 870461 * 2 ^ 59
def prefixEnd_870461 : Nat := 4983230072969 + 3 ^ 40 * 870461 * 2
def baseEnd_870461 : Nat := 297976589328949367356219

theorem tailTrace_870461 : CollatzResearch.WordTrace tailWord_870461 prefixEnd_870461 297976589328949367356219 := by
  unfold tailWord_870461
  simp only [CollatzResearch.WordTrace]
  refine ⟨31748320899475934748251237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21165547266317289832167491 31748320899475934748251237)
  ·
    refine ⟨5952810168651737765297107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31748320899475934748251237 5952810168651737765297107)
    ·
      refine ⟨8929215252977606647945661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5952810168651737765297107 8929215252977606647945661)
      ·
        refine ⟨3348455719866602492979623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8929215252977606647945661 3348455719866602492979623)
        ·
          refine ⟨5022683579799903739469435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3348455719866602492979623 5022683579799903739469435)
          ·
            refine ⟨7534025369699855609204153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5022683579799903739469435 7534025369699855609204153)
            ·
              refine ⟨5650519027274891706903115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7534025369699855609204153 5650519027274891706903115)
              ·
                refine ⟨8475778540912337560354673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5650519027274891706903115 8475778540912337560354673)
                ·
                  refine ⟨6356833905684253170266005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8475778540912337560354673 6356833905684253170266005)
                  ·
                    refine ⟨297976589328949367356219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6356833905684253170266005 297976589328949367356219)
                    ·
                      rfl

theorem cell22_870461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 2, 6].length) (baseStart_870461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_870461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_870461 prefixEnd_870461 := by exact prefixLift 870461
  have htrace : WordTrace (prefixWord ++ tailWord_870461) baseStart_870461 baseEnd_870461 := by
    simpa [prefixWord, tailWord_870461, baseEnd_870461] using wordTrace_append hprefix tailTrace_870461
  have hstable : (prefixWord ++ tailWord_870461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870461).length < 2 ^ (prefixWord ++ tailWord_870461).sum := by decide
  have hdescent : baseEnd_870461 < baseStart_870461 := by decide
  rcases family_descends (prefixWord ++ tailWord_870461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870463 : List Nat := [1, 1, 2, 2, 3, 1, 5, 1, 3, 3]
def baseStart_870463 : Nat := 118140960795 + 870463 * 2 ^ 59
def prefixEnd_870463 : Nat := 4983230072969 + 3 ^ 40 * 870463 * 2
def baseEnd_870463 : Nat := 297977273969822028806213

theorem tailTrace_870463 : CollatzResearch.WordTrace tailWord_870463 prefixEnd_870463 297977273969822028806213 := by
  unfold tailWord_870463
  simp only [CollatzResearch.WordTrace]
  refine ⟨31748393845468689089824043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21165595896979126059882695 31748393845468689089824043)
  ·
    refine ⟨47622590768203033634736065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31748393845468689089824043 47622590768203033634736065)
    ·
      refine ⟨35716943076152275226052049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47622590768203033634736065 35716943076152275226052049)
      ·
        refine ⟨26787707307114206419539037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35716943076152275226052049 26787707307114206419539037)
        ·
          refine ⟨10045390240167827407327139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26787707307114206419539037 10045390240167827407327139)
          ·
            refine ⟨15068085360251741110990709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10045390240167827407327139 15068085360251741110990709)
            ·
              refine ⟨1412633002523600729155379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15068085360251741110990709 1412633002523600729155379)
              ·
                refine ⟨2118949503785401093733069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1412633002523600729155379 2118949503785401093733069)
                ·
                  refine ⟨794606063919525410149901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2118949503785401093733069 794606063919525410149901)
                  ·
                    refine ⟨297977273969822028806213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 794606063919525410149901 297977273969822028806213)
                    ·
                      rfl

theorem cell22_870463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 1, 3, 3].length) (baseStart_870463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_870463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_870463 prefixEnd_870463 := by exact prefixLift 870463
  have htrace : WordTrace (prefixWord ++ tailWord_870463) baseStart_870463 baseEnd_870463 := by
    simpa [prefixWord, tailWord_870463, baseEnd_870463] using wordTrace_append hprefix tailTrace_870463
  have hstable : (prefixWord ++ tailWord_870463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870463).length < 2 ^ (prefixWord ++ tailWord_870463).sum := by decide
  have hdescent : baseEnd_870463 < baseStart_870463 := by decide
  rcases family_descends (prefixWord ++ tailWord_870463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870514 : List Nat := [3, 2, 1, 2, 2, 4, 2, 2, 1, 3]
def baseStart_870514 : Nat := 118140960795 + 870514 * 2 ^ 59
def prefixEnd_870514 : Nat := 4983230072969 + 3 ^ 40 * 870514 * 2
def baseEnd_870514 : Nat := 297994732312074895781057

theorem tailTrace_870514 : CollatzResearch.WordTrace tailWord_870514 prefixEnd_870514 297994732312074895781057 := by
  unfold tailWord_870514
  simp only [CollatzResearch.WordTrace]
  refine ⟨7937563492070981199982649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21166835978855949866620397 7937563492070981199982649)
  ·
    refine ⟨5953172619053235899986987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7937563492070981199982649 5953172619053235899986987)
    ·
      refine ⟨8929758928579853849980481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5953172619053235899986987 8929758928579853849980481)
      ·
        refine ⟨6697319196434890387485361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8929758928579853849980481 6697319196434890387485361)
        ·
          refine ⟨5022989397326167790614021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6697319196434890387485361 5022989397326167790614021)
          ·
            refine ⟨941810511998656460740129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5022989397326167790614021 941810511998656460740129)
            ·
              refine ⟨706357883998992345555097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 941810511998656460740129 706357883998992345555097)
              ·
                refine ⟨529768412999244259166323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 706357883998992345555097 529768412999244259166323)
                ·
                  refine ⟨794652619498866388749485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 529768412999244259166323 794652619498866388749485)
                  ·
                    refine ⟨297994732312074895781057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 794652619498866388749485 297994732312074895781057)
                    ·
                      rfl

theorem cell22_870514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 2, 2, 1, 3].length) (baseStart_870514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_870514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_870514 prefixEnd_870514 := by exact prefixLift 870514
  have htrace : WordTrace (prefixWord ++ tailWord_870514) baseStart_870514 baseEnd_870514 := by
    simpa [prefixWord, tailWord_870514, baseEnd_870514] using wordTrace_append hprefix tailTrace_870514
  have hstable : (prefixWord ++ tailWord_870514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870514).length < 2 ^ (prefixWord ++ tailWord_870514).sum := by decide
  have hdescent : baseEnd_870514 < baseStart_870514 := by decide
  rcases family_descends (prefixWord ++ tailWord_870514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870538 : List Nat := [3, 1, 2, 3, 1, 3, 1, 2, 6]
def baseStart_870538 : Nat := 118140960795 + 870538 * 2 ^ 59
def prefixEnd_870538 : Nat := 4983230072969 + 3 ^ 40 * 870538 * 2
def baseEnd_870538 : Nat := 99334316000848944393661

theorem tailTrace_870538 : CollatzResearch.WordTrace tailWord_870538 prefixEnd_870538 99334316000848944393661 := by
  unfold tailWord_870538
  simp only [CollatzResearch.WordTrace]
  refine ⟨7937782330049244224701067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21167419546797984599202845 7937782330049244224701067)
  ·
    refine ⟨11906673495073866337051601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7937782330049244224701067 11906673495073866337051601)
    ·
      refine ⟨8930005121305399752788701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11906673495073866337051601 8930005121305399752788701)
      ·
        refine ⟨3348751920489524907295763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8930005121305399752788701 3348751920489524907295763)
        ·
          refine ⟨5023127880734287360943645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3348751920489524907295763 5023127880734287360943645)
          ·
            refine ⟨1883672955275357760353867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5023127880734287360943645 1883672955275357760353867)
            ·
              refine ⟨2825509432913036640530801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1883672955275357760353867 2825509432913036640530801)
              ·
                refine ⟨2119132074684777480398101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2825509432913036640530801 2119132074684777480398101)
                ·
                  refine ⟨99334316000848944393661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2119132074684777480398101 99334316000848944393661)
                  ·
                    rfl

theorem cell22_870538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 2, 6].length) (baseStart_870538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_870538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_870538 prefixEnd_870538 := by exact prefixLift 870538
  have htrace : WordTrace (prefixWord ++ tailWord_870538) baseStart_870538 baseEnd_870538 := by
    simpa [prefixWord, tailWord_870538, baseEnd_870538] using wordTrace_append hprefix tailTrace_870538
  have hstable : (prefixWord ++ tailWord_870538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870538).length < 2 ^ (prefixWord ++ tailWord_870538).sum := by decide
  have hdescent : baseEnd_870538 < baseStart_870538 := by decide
  rcases family_descends (prefixWord ++ tailWord_870538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870557 : List Nat := [1, 4, 2, 1, 1, 5, 2, 1, 1, 4]
def baseStart_870557 : Nat := 118140960795 + 870557 * 2 ^ 59
def prefixEnd_870557 : Nat := 4983230072969 + 3 ^ 40 * 870557 * 2
def baseEnd_870557 : Nat := 298009452090837116955925

theorem tailTrace_870557 : CollatzResearch.WordTrace tailWord_870557 prefixEnd_870557 298009452090837116955925 := by
  unfold tailWord_870557
  simp only [CollatzResearch.WordTrace]
  refine ⟨31751822307128143143745925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21167881538085428762497283 31751822307128143143745925)
  ·
    refine ⟨5953466682586526839452361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31751822307128143143745925 5953466682586526839452361)
    ·
      refine ⟨4465100011939895129589271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5953466682586526839452361 4465100011939895129589271)
      ·
        refine ⟨6697650017909842694383907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4465100011939895129589271 6697650017909842694383907)
        ·
          refine ⟨10046475026864764041575861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6697650017909842694383907 10046475026864764041575861)
          ·
            refine ⟨941857033768571628897737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10046475026864764041575861 941857033768571628897737)
            ·
              refine ⟨706392775326428721673303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 941857033768571628897737 706392775326428721673303)
              ·
                refine ⟨1059589162989643082509955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 706392775326428721673303 1059589162989643082509955)
                ·
                  refine ⟨1589383744484464623764933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1059589162989643082509955 1589383744484464623764933)
                  ·
                    refine ⟨298009452090837116955925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1589383744484464623764933 298009452090837116955925)
                    ·
                      rfl

theorem cell22_870557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 2, 1, 1, 4].length) (baseStart_870557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_870557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_870557 prefixEnd_870557 := by exact prefixLift 870557
  have htrace : WordTrace (prefixWord ++ tailWord_870557) baseStart_870557 baseEnd_870557 := by
    simpa [prefixWord, tailWord_870557, baseEnd_870557] using wordTrace_append hprefix tailTrace_870557
  have hstable : (prefixWord ++ tailWord_870557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870557).length < 2 ^ (prefixWord ++ tailWord_870557).sum := by decide
  have hdescent : baseEnd_870557 < baseStart_870557 := by decide
  rcases family_descends (prefixWord ++ tailWord_870557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870628 : List Nat := [2, 3, 1, 1, 1, 2, 1, 6, 5]
def baseStart_870628 : Nat := 118140960795 + 870628 * 2 ^ 59
def prefixEnd_870628 : Nat := 4983230072969 + 3 ^ 40 * 870628 * 2
def baseEnd_870628 : Nat := 99344585613938866143569

theorem tailTrace_870628 : CollatzResearch.WordTrace tailWord_870628 prefixEnd_870628 99344585613938866143569 := by
  unfold tailWord_870628
  simp only [CollatzResearch.WordTrace]
  refine ⟨15877205944935461134790269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21169607926580614846387025 15877205944935461134790269)
  ·
    refine ⟨5953952229350797925546351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15877205944935461134790269 5953952229350797925546351)
    ·
      refine ⟨8930928344026196888319527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5953952229350797925546351 8930928344026196888319527)
      ·
        refine ⟨13396392516039295332479291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8930928344026196888319527 13396392516039295332479291)
        ·
          refine ⟨20094588774058942998718937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13396392516039295332479291 20094588774058942998718937)
          ·
            refine ⟨15070941580544207249039203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20094588774058942998718937 15070941580544207249039203)
            ·
              refine ⟨22606412370816310873558805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15070941580544207249039203 22606412370816310873558805)
              ·
                refine ⟨1059675579882014572198069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22606412370816310873558805 1059675579882014572198069)
                ·
                  refine ⟨99344585613938866143569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1059675579882014572198069 99344585613938866143569)
                  ·
                    rfl

theorem cell22_870628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 6, 5].length) (baseStart_870628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_870628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_870628 prefixEnd_870628 := by exact prefixLift 870628
  have htrace : WordTrace (prefixWord ++ tailWord_870628) baseStart_870628 baseEnd_870628 := by
    simpa [prefixWord, tailWord_870628, baseEnd_870628] using wordTrace_append hprefix tailTrace_870628
  have hstable : (prefixWord ++ tailWord_870628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870628).length < 2 ^ (prefixWord ++ tailWord_870628).sum := by decide
  have hdescent : baseEnd_870628 < baseStart_870628 := by decide
  rcases family_descends (prefixWord ++ tailWord_870628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870632 : List Nat := [2, 1, 4, 1, 2, 4, 1, 1, 3, 3]
def baseStart_870632 : Nat := 118140960795 + 870632 * 2 ^ 59
def prefixEnd_870632 : Nat := 4983230072969 + 3 ^ 40 * 870632 * 2
def baseEnd_870632 : Nat := 298035126123561921330695

theorem tailTrace_870632 : CollatzResearch.WordTrace tailWord_870632 prefixEnd_870632 298035126123561921330695 := by
  unfold tailWord_870632
  simp only [CollatzResearch.WordTrace]
  refine ⟨15877278890928215476363075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21169705187904287301817433 15877278890928215476363075)
  ·
    refine ⟨23815918336392323214544613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15877278890928215476363075 23815918336392323214544613)
    ·
      refine ⟨4465484688073560602727115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23815918336392323214544613 4465484688073560602727115)
      ·
        refine ⟨6698227032110340904090673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4465484688073560602727115 6698227032110340904090673)
        ·
          refine ⟨5023670274082755678068005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6698227032110340904090673 5023670274082755678068005)
          ·
            refine ⟨941938176390516689637751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5023670274082755678068005 941938176390516689637751)
            ·
              refine ⟨1412907264585775034456627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 941938176390516689637751 1412907264585775034456627)
              ·
                refine ⟨2119360896878662551684941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1412907264585775034456627 2119360896878662551684941)
                ·
                  refine ⟨794760336329498456881853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2119360896878662551684941 794760336329498456881853)
                  ·
                    refine ⟨298035126123561921330695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 794760336329498456881853 298035126123561921330695)
                    ·
                      rfl

theorem cell22_870632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 1, 3, 3].length) (baseStart_870632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_870632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_870632 prefixEnd_870632 := by exact prefixLift 870632
  have htrace : WordTrace (prefixWord ++ tailWord_870632) baseStart_870632 baseEnd_870632 := by
    simpa [prefixWord, tailWord_870632, baseEnd_870632] using wordTrace_append hprefix tailTrace_870632
  have hstable : (prefixWord ++ tailWord_870632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870632).length < 2 ^ (prefixWord ++ tailWord_870632).sum := by decide
  have hdescent : baseEnd_870632 < baseStart_870632 := by decide
  rcases family_descends (prefixWord ++ tailWord_870632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870703 : List Nat := [1, 1, 2, 1, 2, 1, 4, 2, 4, 4]
def baseStart_870703 : Nat := 118140960795 + 870703 * 2 ^ 59
def prefixEnd_870703 : Nat := 4983230072969 + 3 ^ 40 * 870703 * 2
def baseEnd_870703 : Nat := 298059430874541402805477

theorem tailTrace_870703 : CollatzResearch.WordTrace tailWord_870703 prefixEnd_870703 298059430874541402805477 := by
  unfold tailWord_870703
  simp only [CollatzResearch.WordTrace]
  refine ⟨31757147364599210078560763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21171431576399473385707175 31757147364599210078560763)
  ·
    refine ⟨47635721046898815117841145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31757147364599210078560763 47635721046898815117841145)
    ·
      refine ⟨35726790785174111338380859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47635721046898815117841145 35726790785174111338380859)
      ·
        refine ⟨53590186177761167007571289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35726790785174111338380859 53590186177761167007571289)
        ·
          refine ⟨40192639633320875255678467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53590186177761167007571289 40192639633320875255678467)
          ·
            refine ⟨60288959449981312883517701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40192639633320875255678467 60288959449981312883517701)
            ·
              refine ⟨11304179896871496165659569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60288959449981312883517701 11304179896871496165659569)
              ·
                refine ⟨8478134922653622124244677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11304179896871496165659569 8478134922653622124244677)
                ·
                  refine ⟨1589650297997554148295877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8478134922653622124244677 1589650297997554148295877)
                  ·
                    refine ⟨298059430874541402805477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1589650297997554148295877 298059430874541402805477)
                    ·
                      rfl

theorem cell22_870703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 4, 4].length) (baseStart_870703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_870703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_870703 prefixEnd_870703 := by exact prefixLift 870703
  have htrace : WordTrace (prefixWord ++ tailWord_870703) baseStart_870703 baseEnd_870703 := by
    simpa [prefixWord, tailWord_870703, baseEnd_870703] using wordTrace_append hprefix tailTrace_870703
  have hstable : (prefixWord ++ tailWord_870703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870703).length < 2 ^ (prefixWord ++ tailWord_870703).sum := by decide
  have hdescent : baseEnd_870703 < baseStart_870703 := by decide
  rcases family_descends (prefixWord ++ tailWord_870703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870814 : List Nat := [4, 3, 1, 2, 1, 2, 1, 3, 5]
def baseStart_870814 : Nat := 118140960795 + 870814 * 2 ^ 59
def prefixEnd_870814 : Nat := 4983230072969 + 3 ^ 40 * 870814 * 2
def baseEnd_870814 : Nat := 99365809480991371093379

theorem tailTrace_870814 : CollatzResearch.WordTrace tailWord_870814 prefixEnd_870814 99365809480991371093379 := by
  unfold tailWord_870814
  simp only [CollatzResearch.WordTrace]
  refine ⟨3970149483399634504481437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21174130578131384023900997 3970149483399634504481437)
  ·
    refine ⟨1488806056274862939180539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3970149483399634504481437 1488806056274862939180539)
    ·
      refine ⟨2233209084412294408770809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1488806056274862939180539 2233209084412294408770809)
      ·
        refine ⟨1674906813309220806578107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2233209084412294408770809 1674906813309220806578107)
        ·
          refine ⟨2512360219963831209867161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1674906813309220806578107 2512360219963831209867161)
          ·
            refine ⟨1884270164972873407400371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2512360219963831209867161 1884270164972873407400371)
            ·
              refine ⟨2826405247459310111100557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1884270164972873407400371 2826405247459310111100557)
              ·
                refine ⟨1059901967797241291662709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2826405247459310111100557 1059901967797241291662709)
                ·
                  refine ⟨99365809480991371093379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1059901967797241291662709 99365809480991371093379)
                  ·
                    rfl

theorem cell22_870814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_870814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_870814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_870814 prefixEnd_870814 := by exact prefixLift 870814
  have htrace : WordTrace (prefixWord ++ tailWord_870814) baseStart_870814 baseEnd_870814 := by
    simpa [prefixWord, tailWord_870814, baseEnd_870814] using wordTrace_append hprefix tailTrace_870814
  have hstable : (prefixWord ++ tailWord_870814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870814).length < 2 ^ (prefixWord ++ tailWord_870814).sum := by decide
  have hdescent : baseEnd_870814 < baseStart_870814 := by decide
  rcases family_descends (prefixWord ++ tailWord_870814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870857 : List Nat := [1, 2, 1, 1, 2, 1, 5, 4, 2, 3]
def baseStart_870857 : Nat := 118140960795 + 870857 * 2 ^ 59
def prefixEnd_870857 : Nat := 4983230072969 + 3 ^ 40 * 870857 * 2
def baseEnd_870857 : Nat := 298112148221736334455005

theorem tailTrace_870857 : CollatzResearch.WordTrace tailWord_870857 prefixEnd_870857 298112148221736334455005 := by
  unfold tailWord_870857
  simp only [CollatzResearch.WordTrace]
  refine ⟨31762764206041294379666825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21175176137360862919777883 31762764206041294379666825)
  ·
    refine ⟨23822073154530970784750119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31762764206041294379666825 23822073154530970784750119)
    ·
      refine ⟨35733109731796456177125179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23822073154530970784750119 35733109731796456177125179)
      ·
        refine ⟨53599664597694684265687769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35733109731796456177125179 53599664597694684265687769)
        ·
          refine ⟨40199748448271013199265827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53599664597694684265687769 40199748448271013199265827)
          ·
            refine ⟨60299622672406519798898741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40199748448271013199265827 60299622672406519798898741)
            ·
              refine ⟨5653089625538111231146757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60299622672406519798898741 5653089625538111231146757)
              ·
                refine ⟨1059954304788395855840017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5653089625538111231146757 1059954304788395855840017)
                ·
                  refine ⟨794965728591296891880013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1059954304788395855840017 794965728591296891880013)
                  ·
                    refine ⟨298112148221736334455005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 794965728591296891880013 298112148221736334455005)
                    ·
                      rfl

theorem cell22_870857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 4, 2, 3].length) (baseStart_870857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_870857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_870857 prefixEnd_870857 := by exact prefixLift 870857
  have htrace : WordTrace (prefixWord ++ tailWord_870857) baseStart_870857 baseEnd_870857 := by
    simpa [prefixWord, tailWord_870857, baseEnd_870857] using wordTrace_append hprefix tailTrace_870857
  have hstable : (prefixWord ++ tailWord_870857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870857).length < 2 ^ (prefixWord ++ tailWord_870857).sum := by decide
  have hdescent : baseEnd_870857 < baseStart_870857 := by decide
  rcases family_descends (prefixWord ++ tailWord_870857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870887 : List Nat := [1, 1, 5, 2, 1, 1, 5, 6]
def baseStart_870887 : Nat := 118140960795 + 870887 * 2 ^ 59
def prefixEnd_870887 : Nat := 4983230072969 + 3 ^ 40 * 870887 * 2
def baseEnd_870887 : Nat := 33124713092758472911657

theorem tailTrace_870887 : CollatzResearch.WordTrace tailWord_870887 prefixEnd_870887 33124713092758472911657 := by
  unfold tailWord_870887
  simp only [CollatzResearch.WordTrace]
  refine ⟨31763858395932609503258915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21175905597288406335505943 31763858395932609503258915)
  ·
    refine ⟨47645787593898914254888373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31763858395932609503258915 47645787593898914254888373)
    ·
      refine ⟨4466792586928023211395785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47645787593898914254888373 4466792586928023211395785)
      ·
        refine ⟨3350094440196017408546839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4466792586928023211395785 3350094440196017408546839)
        ·
          refine ⟨5025141660294026112820259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3350094440196017408546839 5025141660294026112820259)
          ·
            refine ⟨7537712490441039169230389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5025141660294026112820259 7537712490441039169230389)
            ·
              refine ⟨706660545978847422115349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7537712490441039169230389 706660545978847422115349)
              ·
                refine ⟨33124713092758472911657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 706660545978847422115349 33124713092758472911657)
                ·
                  rfl

theorem cell22_870887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 5, 6].length) (baseStart_870887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_870887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_870887 prefixEnd_870887 := by exact prefixLift 870887
  have htrace : WordTrace (prefixWord ++ tailWord_870887) baseStart_870887 baseEnd_870887 := by
    simpa [prefixWord, tailWord_870887, baseEnd_870887] using wordTrace_append hprefix tailTrace_870887
  have hstable : (prefixWord ++ tailWord_870887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870887).length < 2 ^ (prefixWord ++ tailWord_870887).sum := by decide
  have hdescent : baseEnd_870887 < baseStart_870887 := by decide
  rcases family_descends (prefixWord ++ tailWord_870887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870915 : List Nat := [1, 1, 1, 3, 2, 1, 5, 1, 7]
def baseStart_870915 : Nat := 118140960795 + 870915 * 2 ^ 59
def prefixEnd_870915 : Nat := 4983230072969 + 3 ^ 40 * 870915 * 2
def baseEnd_870915 : Nat := 99377334269014505501609

theorem tailTrace_870915 : CollatzResearch.WordTrace tailWord_870915 prefixEnd_870915 99377334269014505501609 := by
  unfold tailWord_870915
  simp only [CollatzResearch.WordTrace]
  refine ⟨31764879639831170285278199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21176586426554113523518799 31764879639831170285278199)
  ·
    refine ⟨47647319459746755427917299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31764879639831170285278199 47647319459746755427917299)
    ·
      refine ⟨71470979189620133141875949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47647319459746755427917299 71470979189620133141875949)
      ·
        refine ⟨26801617196107549928203481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71470979189620133141875949 26801617196107549928203481)
        ·
          refine ⟨20101212897080662446152611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26801617196107549928203481 20101212897080662446152611)
          ·
            refine ⟨30151819345620993669228917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20101212897080662446152611 30151819345620993669228917)
            ·
              refine ⟨2826733063651968156490211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30151819345620993669228917 2826733063651968156490211)
              ·
                refine ⟨4240099595477952234735317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2826733063651968156490211 4240099595477952234735317)
                ·
                  refine ⟨99377334269014505501609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4240099595477952234735317 99377334269014505501609)
                  ·
                    rfl

theorem cell22_870915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 1, 7].length) (baseStart_870915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_870915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_870915 prefixEnd_870915 := by exact prefixLift 870915
  have htrace : WordTrace (prefixWord ++ tailWord_870915) baseStart_870915 baseEnd_870915 := by
    simpa [prefixWord, tailWord_870915, baseEnd_870915] using wordTrace_append hprefix tailTrace_870915
  have hstable : (prefixWord ++ tailWord_870915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870915).length < 2 ^ (prefixWord ++ tailWord_870915).sum := by decide
  have hdescent : baseEnd_870915 < baseStart_870915 := by decide
  rcases family_descends (prefixWord ++ tailWord_870915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870925 : List Nat := [1, 7, 1, 1, 1, 2, 3, 1, 2, 3]
def baseStart_870925 : Nat := 118140960795 + 870925 * 2 ^ 59
def prefixEnd_870925 : Nat := 4983230072969 + 3 ^ 40 * 870925 * 2
def baseEnd_870925 : Nat := 298135426011406823754797

theorem tailTrace_870925 : CollatzResearch.WordTrace tailWord_870925 prefixEnd_870925 298135426011406823754797 := by
  unfold tailWord_870925
  simp only [CollatzResearch.WordTrace]
  refine ⟨31765244369794941993142229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21176829579863294662094819 31765244369794941993142229)
  ·
    refine ⟨744497914917068952964271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 31765244369794941993142229 744497914917068952964271)
    ·
      refine ⟨1116746872375603429446407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 744497914917068952964271 1116746872375603429446407)
      ·
        refine ⟨1675120308563405144169611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1116746872375603429446407 1675120308563405144169611)
        ·
          refine ⟨2512680462845107716254417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1675120308563405144169611 2512680462845107716254417)
          ·
            refine ⟨1884510347133830787190813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2512680462845107716254417 1884510347133830787190813)
            ·
              refine ⟨706691380175186545196555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1884510347133830787190813 706691380175186545196555)
              ·
                refine ⟨1060037070262779817794833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 706691380175186545196555 1060037070262779817794833)
                ·
                  refine ⟨795027802697084863346125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1060037070262779817794833 795027802697084863346125)
                  ·
                    refine ⟨298135426011406823754797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 795027802697084863346125 298135426011406823754797)
                    ·
                      rfl

theorem cell22_870925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_870925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_870925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_870925 prefixEnd_870925 := by exact prefixLift 870925
  have htrace : WordTrace (prefixWord ++ tailWord_870925) baseStart_870925 baseEnd_870925 := by
    simpa [prefixWord, tailWord_870925, baseEnd_870925] using wordTrace_append hprefix tailTrace_870925
  have hstable : (prefixWord ++ tailWord_870925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870925).length < 2 ^ (prefixWord ++ tailWord_870925).sum := by decide
  have hdescent : baseEnd_870925 < baseStart_870925 := by decide
  rcases family_descends (prefixWord ++ tailWord_870925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870960 : List Nat := [2, 1, 1, 1, 2, 3, 2, 2, 8]
def baseStart_870960 : Nat := 118140960795 + 870960 * 2 ^ 59
def prefixEnd_870960 : Nat := 4983230072969 + 3 ^ 40 * 870960 * 2
def baseEnd_870960 : Nat := 99382469075559466376563

theorem tailTrace_870960 : CollatzResearch.WordTrace tailWord_870960 prefixEnd_870960 99382469075559466376563 := by
  unfold tailWord_870960
  simp only [CollatzResearch.WordTrace]
  refine ⟨15883260462334071485333167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21177680616445428647110889 15883260462334071485333167)
  ·
    refine ⟨23824890693501107227999751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15883260462334071485333167 23824890693501107227999751)
    ·
      refine ⟨35737336040251660841999627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23824890693501107227999751 35737336040251660841999627)
      ·
        refine ⟨53606004060377491262999441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35737336040251660841999627 53606004060377491262999441)
        ·
          refine ⟨40204503045283118447249581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53606004060377491262999441 40204503045283118447249581)
          ·
            refine ⟨15076688641981169417718593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40204503045283118447249581 15076688641981169417718593)
            ·
              refine ⟨11307516481485877063288945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15076688641981169417718593 11307516481485877063288945)
              ·
                refine ⟨8480637361114407797466709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11307516481485877063288945 8480637361114407797466709)
                ·
                  refine ⟨99382469075559466376563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8480637361114407797466709 99382469075559466376563)
                  ·
                    rfl

theorem cell22_870960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 8].length) (baseStart_870960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_870960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_870960 prefixEnd_870960 := by exact prefixLift 870960
  have htrace : WordTrace (prefixWord ++ tailWord_870960) baseStart_870960 baseEnd_870960 := by
    simpa [prefixWord, tailWord_870960, baseEnd_870960] using wordTrace_append hprefix tailTrace_870960
  have hstable : (prefixWord ++ tailWord_870960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870960).length < 2 ^ (prefixWord ++ tailWord_870960).sum := by decide
  have hdescent : baseEnd_870960 < baseStart_870960 := by decide
  rcases family_descends (prefixWord ++ tailWord_870960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870992 : List Nat := [2, 1, 1, 1, 1, 3, 2, 2, 6, 3]
def baseStart_870992 : Nat := 118140960795 + 870992 * 2 ^ 59
def prefixEnd_870992 : Nat := 4983230072969 + 3 ^ 40 * 870992 * 2
def baseEnd_870992 : Nat := 298158361480640982329591

theorem tailTrace_870992 : CollatzResearch.WordTrace tailWord_870992 prefixEnd_870992 298158361480640982329591 := by
  unfold tailWord_870992
  simp only [CollatzResearch.WordTrace]
  refine ⟨15883844030276106217915615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21178458707034808290554153 15883844030276106217915615)
  ·
    refine ⟨23825766045414159326873423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15883844030276106217915615 23825766045414159326873423)
    ·
      refine ⟨35738649068121238990310135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23825766045414159326873423 35738649068121238990310135)
      ·
        refine ⟨53607973602181858485465203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35738649068121238990310135 53607973602181858485465203)
        ·
          refine ⟨80411960403272787728197805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53607973602181858485465203 80411960403272787728197805)
          ·
            refine ⟨30154485151227295398074177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80411960403272787728197805 30154485151227295398074177)
            ·
              refine ⟨22615863863420471548555633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30154485151227295398074177 22615863863420471548555633)
              ·
                refine ⟨16961897897565353661416725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22615863863420471548555633 16961897897565353661416725)
                ·
                  refine ⟨795088963948375952878909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 16961897897565353661416725 795088963948375952878909)
                  ·
                    refine ⟨298158361480640982329591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 795088963948375952878909 298158361480640982329591)
                    ·
                      rfl

theorem cell22_870992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 6, 3].length) (baseStart_870992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_870992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_870992 prefixEnd_870992 := by exact prefixLift 870992
  have htrace : WordTrace (prefixWord ++ tailWord_870992) baseStart_870992 baseEnd_870992 := by
    simpa [prefixWord, tailWord_870992, baseEnd_870992] using wordTrace_append hprefix tailTrace_870992
  have hstable : (prefixWord ++ tailWord_870992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870992).length < 2 ^ (prefixWord ++ tailWord_870992).sum := by decide
  have hdescent : baseEnd_870992 < baseStart_870992 := by decide
  rcases family_descends (prefixWord ++ tailWord_870992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870996 : List Nat := [2, 4, 1, 1, 1, 5, 1, 2, 1, 4]
def baseStart_870996 : Nat := 118140960795 + 870996 * 2 ^ 59
def prefixEnd_870996 : Nat := 4983230072969 + 3 ^ 40 * 870996 * 2
def baseEnd_870996 : Nat := 298159730762386305229579

theorem tailTrace_870996 : CollatzResearch.WordTrace tailWord_870996 prefixEnd_870996 298159730762386305229579 := by
  unfold tailWord_870996
  simp only [CollatzResearch.WordTrace]
  refine ⟨15883916976268860559488421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21178555968358480745984561 15883916976268860559488421)
  ·
    refine ⟨2978234433050411354904079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15883916976268860559488421 2978234433050411354904079)
    ·
      refine ⟨4467351649575617032356119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2978234433050411354904079 4467351649575617032356119)
      ·
        refine ⟨6701027474363425548534179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4467351649575617032356119 6701027474363425548534179)
        ·
          refine ⟨10051541211545138322801269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6701027474363425548534179 10051541211545138322801269)
          ·
            refine ⟨942331988582356717762619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10051541211545138322801269 942331988582356717762619)
            ·
              refine ⟨1413497982873535076643929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 942331988582356717762619 1413497982873535076643929)
              ·
                refine ⟨1060123487155151307482947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1413497982873535076643929 1060123487155151307482947)
                ·
                  refine ⟨1590185230732726961224421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1060123487155151307482947 1590185230732726961224421)
                  ·
                    refine ⟨298159730762386305229579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1590185230732726961224421 298159730762386305229579)
                    ·
                      rfl

theorem cell22_870996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 2, 1, 4].length) (baseStart_870996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_870996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_870996 prefixEnd_870996 := by exact prefixLift 870996
  have htrace : WordTrace (prefixWord ++ tailWord_870996) baseStart_870996 baseEnd_870996 := by
    simpa [prefixWord, tailWord_870996, baseEnd_870996] using wordTrace_append hprefix tailTrace_870996
  have hstable : (prefixWord ++ tailWord_870996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870996).length < 2 ^ (prefixWord ++ tailWord_870996).sum := by decide
  have hdescent : baseEnd_870996 < baseStart_870996 := by decide
  rcases family_descends (prefixWord ++ tailWord_870996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871022 : List Nat := [4, 1, 2, 2, 2, 11]
def baseStart_871022 : Nat := 118140960795 + 871022 * 2 ^ 59
def prefixEnd_871022 : Nat := 4983230072969 + 3 ^ 40 * 871022 * 2
def baseEnd_871022 : Nat := 3681094211033714865179

theorem tailTrace_871022 : CollatzResearch.WordTrace tailWord_871022 prefixEnd_871022 3681094211033714865179 := by
  unfold tailWord_871022
  simp only [CollatzResearch.WordTrace]
  refine ⟨3971097781305440944927915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21179188166962351706282213 3971097781305440944927915)
  ·
    refine ⟨5956646671958161417391873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3971097781305440944927915 5956646671958161417391873)
    ·
      refine ⟨4467485003968621063043905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5956646671958161417391873 4467485003968621063043905)
      ·
        refine ⟨3350613752976465797282929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4467485003968621063043905 3350613752976465797282929)
        ·
          refine ⟨2512960314732349347962197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3350613752976465797282929 2512960314732349347962197)
          ·
            refine ⟨3681094211033714865179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 2512960314732349347962197 3681094211033714865179)
            ·
              rfl

theorem cell22_871022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 11].length) (baseStart_871022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_871022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_871022 prefixEnd_871022 := by exact prefixLift 871022
  have htrace : WordTrace (prefixWord ++ tailWord_871022) baseStart_871022 baseEnd_871022 := by
    simpa [prefixWord, tailWord_871022, baseEnd_871022] using wordTrace_append hprefix tailTrace_871022
  have hstable : (prefixWord ++ tailWord_871022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871022).length < 2 ^ (prefixWord ++ tailWord_871022).sum := by decide
  have hdescent : baseEnd_871022 < baseStart_871022 := by decide
  rcases family_descends (prefixWord ++ tailWord_871022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871101 : List Nat := [1, 4, 1, 2, 1, 4, 3, 1, 5]
def baseStart_871101 : Nat := 118140960795 + 871101 * 2 ^ 59
def prefixEnd_871101 : Nat := 4983230072969 + 3 ^ 40 * 871101 * 2
def baseEnd_871101 : Nat := 99398558136067010451419

theorem tailTrace_871101 : CollatzResearch.WordTrace tailWord_871101 prefixEnd_871101 99398558136067010451419 := by
  unfold tailWord_871101
  simp only [CollatzResearch.WordTrace]
  refine ⟨31771663617157324051549157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21181109078104882701032771 31771663617157324051549157)
  ·
    refine ⟨5957186928216998259665467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31771663617157324051549157 5957186928216998259665467)
    ·
      refine ⟨8935780392325497389498201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5957186928216998259665467 8935780392325497389498201)
      ·
        refine ⟨6701835294244123042123651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8935780392325497389498201 6701835294244123042123651)
        ·
          refine ⟨10052752941366184563185477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6701835294244123042123651 10052752941366184563185477)
          ·
            refine ⟨1884891176506159605597277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10052752941366184563185477 1884891176506159605597277)
            ·
              refine ⟨706834191189809852098979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1884891176506159605597277 706834191189809852098979)
              ·
                refine ⟨1060251286784714778148469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 706834191189809852098979 1060251286784714778148469)
                ·
                  refine ⟨99398558136067010451419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1060251286784714778148469 99398558136067010451419)
                  ·
                    rfl

theorem cell22_871101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 3, 1, 5].length) (baseStart_871101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_871101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_871101 prefixEnd_871101 := by exact prefixLift 871101
  have htrace : WordTrace (prefixWord ++ tailWord_871101) baseStart_871101 baseEnd_871101 := by
    simpa [prefixWord, tailWord_871101, baseEnd_871101] using wordTrace_append hprefix tailTrace_871101
  have hstable : (prefixWord ++ tailWord_871101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871101).length < 2 ^ (prefixWord ++ tailWord_871101).sum := by decide
  have hdescent : baseEnd_871101 < baseStart_871101 := by decide
  rcases family_descends (prefixWord ++ tailWord_871101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871122 : List Nat := [3, 2, 2, 2, 4, 1, 1, 3, 1, 3]
def baseStart_871122 : Nat := 118140960795 + 871122 * 2 ^ 59
def prefixEnd_871122 : Nat := 4983230072969 + 3 ^ 40 * 871122 * 2
def baseEnd_871122 : Nat := 298202863137363976579193

theorem tailTrace_871122 : CollatzResearch.WordTrace tailWord_871122 prefixEnd_871122 298202863137363976579193 := by
  unfold tailWord_871122
  simp only [CollatzResearch.WordTrace]
  refine ⟨7943107387520311159515905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21181619700054163092042413 7943107387520311159515905)
  ·
    refine ⟨5957330540640233369636929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7943107387520311159515905 5957330540640233369636929)
    ·
      refine ⟨4467997905480175027227697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5957330540640233369636929 4467997905480175027227697)
      ·
        refine ⟨3350998429110131270420773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4467997905480175027227697 3350998429110131270420773)
        ·
          refine ⟨628312205458149613203895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3350998429110131270420773 628312205458149613203895)
          ·
            refine ⟨942468308187224419805843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 628312205458149613203895 942468308187224419805843)
            ·
              refine ⟨1413702462280836629708765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 942468308187224419805843 1413702462280836629708765)
              ·
                refine ⟨530138423355313736140787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1413702462280836629708765 530138423355313736140787)
                ·
                  refine ⟨795207635032970604211181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 530138423355313736140787 795207635032970604211181)
                  ·
                    refine ⟨298202863137363976579193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 795207635032970604211181 298202863137363976579193)
                    ·
                      rfl

theorem cell22_871122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 3, 1, 3].length) (baseStart_871122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_871122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_871122 prefixEnd_871122 := by exact prefixLift 871122
  have htrace : WordTrace (prefixWord ++ tailWord_871122) baseStart_871122 baseEnd_871122 := by
    simpa [prefixWord, tailWord_871122, baseEnd_871122] using wordTrace_append hprefix tailTrace_871122
  have hstable : (prefixWord ++ tailWord_871122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871122).length < 2 ^ (prefixWord ++ tailWord_871122).sum := by decide
  have hdescent : baseEnd_871122 < baseStart_871122 := by decide
  rcases family_descends (prefixWord ++ tailWord_871122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871176 : List Nat := [2, 1, 3, 2, 2, 3, 2, 1, 2, 4]
def baseStart_871176 : Nat := 118140960795 + 871176 * 2 ^ 59
def prefixEnd_871176 : Nat := 4983230072969 + 3 ^ 40 * 871176 * 2
def baseEnd_871176 : Nat := 298221348440925835729027

theorem tailTrace_871176 : CollatzResearch.WordTrace tailWord_871176 prefixEnd_871176 298221348440925835729027 := by
  unfold tailWord_871176
  simp only [CollatzResearch.WordTrace]
  refine ⟨15887199545942805930264691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21182932727923741240352921 15887199545942805930264691)
  ·
    refine ⟨23830799318914208895397037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15887199545942805930264691 23830799318914208895397037)
    ·
      refine ⟨8936549744592828335773889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23830799318914208895397037 8936549744592828335773889)
      ·
        refine ⟨6702412308444621251830417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8936549744592828335773889 6702412308444621251830417)
        ·
          refine ⟨5026809231333465938872813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6702412308444621251830417 5026809231333465938872813)
          ·
            refine ⟨1885053461750049727077305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5026809231333465938872813 1885053461750049727077305)
            ·
              refine ⟨1413790096312537295307979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1885053461750049727077305 1413790096312537295307979)
              ·
                refine ⟨2120685144468805942961969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1413790096312537295307979 2120685144468805942961969)
                ·
                  refine ⟨1590513858351604457221477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2120685144468805942961969 1590513858351604457221477)
                  ·
                    refine ⟨298221348440925835729027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1590513858351604457221477 298221348440925835729027)
                    ·
                      rfl

theorem cell22_871176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 1, 2, 4].length) (baseStart_871176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_871176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_871176 prefixEnd_871176 := by exact prefixLift 871176
  have htrace : WordTrace (prefixWord ++ tailWord_871176) baseStart_871176 baseEnd_871176 := by
    simpa [prefixWord, tailWord_871176, baseEnd_871176] using wordTrace_append hprefix tailTrace_871176
  have hstable : (prefixWord ++ tailWord_871176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871176).length < 2 ^ (prefixWord ++ tailWord_871176).sum := by decide
  have hdescent : baseEnd_871176 < baseStart_871176 := by decide
  rcases family_descends (prefixWord ++ tailWord_871176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871197 : List Nat := [1, 4, 2, 4, 1, 2, 2, 2, 4]
def baseStart_871197 : Nat := 118140960795 + 871197 * 2 ^ 59
def prefixEnd_871197 : Nat := 4983230072969 + 3 ^ 40 * 871197 * 2
def baseEnd_871197 : Nat := 99409512390029593651321

theorem tailTrace_871197 : CollatzResearch.WordTrace tailWord_871197 prefixEnd_871197 99409512390029593651321 := by
  unfold tailWord_871197
  simp only [CollatzResearch.WordTrace]
  refine ⟨31775165024809532447043845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21183443349873021631362563 31775165024809532447043845)
  ·
    refine ⟨5957843442151787333820721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31775165024809532447043845 5957843442151787333820721)
    ·
      refine ⟨4468382581613840500365541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5957843442151787333820721 4468382581613840500365541)
      ·
        refine ⟨837821734052595093818539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4468382581613840500365541 837821734052595093818539)
        ·
          refine ⟨1256732601078892640727809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 837821734052595093818539 1256732601078892640727809)
          ·
            refine ⟨942549450809169480545857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1256732601078892640727809 942549450809169480545857)
            ·
              refine ⟨706912088106877110409393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 942549450809169480545857 706912088106877110409393)
              ·
                refine ⟨530184066080157832807045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 706912088106877110409393 530184066080157832807045)
                ·
                  refine ⟨99409512390029593651321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 530184066080157832807045 99409512390029593651321)
                  ·
                    rfl

theorem cell22_871197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 2, 2, 4].length) (baseStart_871197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_871197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_871197 prefixEnd_871197 := by exact prefixLift 871197
  have htrace : WordTrace (prefixWord ++ tailWord_871197) baseStart_871197 baseEnd_871197 := by
    simpa [prefixWord, tailWord_871197, baseEnd_871197] using wordTrace_append hprefix tailTrace_871197
  have hstable : (prefixWord ++ tailWord_871197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871197).length < 2 ^ (prefixWord ++ tailWord_871197).sum := by decide
  have hdescent : baseEnd_871197 < baseStart_871197 := by decide
  rcases family_descends (prefixWord ++ tailWord_871197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871330 : List Nat := [3, 3, 1, 2, 2, 2, 1, 3, 2, 3]
def baseStart_871330 : Nat := 118140960795 + 871330 * 2 ^ 59
def prefixEnd_871330 : Nat := 4983230072969 + 3 ^ 40 * 871330 * 2
def baseEnd_871330 : Nat := 298274065788120767378555

theorem tailTrace_871330 : CollatzResearch.WordTrace tailWord_871330 prefixEnd_871330 298274065788120767378555 := by
  unfold tailWord_871330
  simp only [CollatzResearch.WordTrace]
  refine ⟨7945003983331924040408861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21186677288885130774423629 7945003983331924040408861)
  ·
    refine ⟨2979376493749471515153323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7945003983331924040408861 2979376493749471515153323)
    ·
      refine ⟨4469064740624207272729985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2979376493749471515153323 4469064740624207272729985)
      ·
        refine ⟨3351798555468155454547489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4469064740624207272729985 3351798555468155454547489)
        ·
          refine ⟨2513848916601116590910617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3351798555468155454547489 2513848916601116590910617)
          ·
            refine ⟨1885386687450837443182963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2513848916601116590910617 1885386687450837443182963)
            ·
              refine ⟨2828080031176256164774445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1885386687450837443182963 2828080031176256164774445)
              ·
                refine ⟨1060530011691096061790417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2828080031176256164774445 1060530011691096061790417)
                ·
                  refine ⟨795397508768322046342813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1060530011691096061790417 795397508768322046342813)
                  ·
                    refine ⟨298274065788120767378555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 795397508768322046342813 298274065788120767378555)
                    ·
                      rfl

theorem cell22_871330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 3, 2, 3].length) (baseStart_871330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_871330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_871330 prefixEnd_871330 := by exact prefixLift 871330
  have htrace : WordTrace (prefixWord ++ tailWord_871330) baseStart_871330 baseEnd_871330 := by
    simpa [prefixWord, tailWord_871330, baseEnd_871330] using wordTrace_append hprefix tailTrace_871330
  have hstable : (prefixWord ++ tailWord_871330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871330).length < 2 ^ (prefixWord ++ tailWord_871330).sum := by decide
  have hdescent : baseEnd_871330 < baseStart_871330 := by decide
  rcases family_descends (prefixWord ++ tailWord_871330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871339 : List Nat := [1, 1, 1, 1, 2, 1, 1, 6, 2, 6]
def baseStart_871339 : Nat := 118140960795 + 871339 * 2 ^ 59
def prefixEnd_871339 : Nat := 4983230072969 + 3 ^ 40 * 871339 * 2
def baseEnd_871339 : Nat := 298277146672047743903527

theorem tailTrace_871339 : CollatzResearch.WordTrace tailWord_871339 prefixEnd_871339 298277146672047743903527 := by
  unfold tailWord_871339
  simp only [CollatzResearch.WordTrace]
  refine ⟨31780344190295090698713071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21186896126863393799142047 31780344190295090698713071)
  ·
    refine ⟨47670516285442636048069607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31780344190295090698713071 47670516285442636048069607)
    ·
      refine ⟨71505774428163954072104411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47670516285442636048069607 71505774428163954072104411)
      ·
        refine ⟨107258661642245931108156617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71505774428163954072104411 107258661642245931108156617)
        ·
          refine ⟨80443996231684448331117463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107258661642245931108156617 80443996231684448331117463)
          ·
            refine ⟨120665994347526672496676195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80443996231684448331117463 120665994347526672496676195)
            ·
              refine ⟨180998991521290008745014293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120665994347526672496676195 180998991521290008745014293)
              ·
                refine ⟨8484327727560469159922545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 180998991521290008745014293 8484327727560469159922545)
                ·
                  refine ⟨6363245795670351869941909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8484327727560469159922545 6363245795670351869941909)
                  ·
                    refine ⟨298277146672047743903527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6363245795670351869941909 298277146672047743903527)
                    ·
                      rfl

theorem cell22_871339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2, 6].length) (baseStart_871339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_871339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_871339 prefixEnd_871339 := by exact prefixLift 871339
  have htrace : WordTrace (prefixWord ++ tailWord_871339) baseStart_871339 baseEnd_871339 := by
    simpa [prefixWord, tailWord_871339, baseEnd_871339] using wordTrace_append hprefix tailTrace_871339
  have hstable : (prefixWord ++ tailWord_871339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871339).length < 2 ^ (prefixWord ++ tailWord_871339).sum := by decide
  have hdescent : baseEnd_871339 < baseStart_871339 := by decide
  rcases family_descends (prefixWord ++ tailWord_871339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871366 : List Nat := [6, 1, 3, 1, 1, 1, 1, 4, 4]
def baseStart_871366 : Nat := 118140960795 + 871366 * 2 ^ 59
def prefixEnd_871366 : Nat := 4983230072969 + 3 ^ 40 * 871366 * 2
def baseEnd_871366 : Nat := 99428796441276224492815

theorem tailTrace_871366 : CollatzResearch.WordTrace tailWord_871366 prefixEnd_871366 99428796441276224492815 := by
  unfold tailWord_871366
  simp only [CollatzResearch.WordTrace]
  refine ⟨993166530037414822185811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 21187552640798182873297301 993166530037414822185811)
  ·
    refine ⟨1489749795056122233278717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 993166530037414822185811 1489749795056122233278717)
    ·
      refine ⟨558656173146045837479519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1489749795056122233278717 558656173146045837479519)
      ·
        refine ⟨837984259719068756219279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 558656173146045837479519 837984259719068756219279)
        ·
          refine ⟨1256976389578603134328919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 837984259719068756219279 1256976389578603134328919)
          ·
            refine ⟨1885464584367904701493379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1256976389578603134328919 1885464584367904701493379)
            ·
              refine ⟨2828196876551857052240069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1885464584367904701493379 2828196876551857052240069)
              ·
                refine ⟨530286914353473197295013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2828196876551857052240069 530286914353473197295013)
                ·
                  refine ⟨99428796441276224492815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 530286914353473197295013 99428796441276224492815)
                  ·
                    rfl

theorem cell22_871366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_871366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_871366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_871366 prefixEnd_871366 := by exact prefixLift 871366
  have htrace : WordTrace (prefixWord ++ tailWord_871366) baseStart_871366 baseEnd_871366 := by
    simpa [prefixWord, tailWord_871366, baseEnd_871366] using wordTrace_append hprefix tailTrace_871366
  have hstable : (prefixWord ++ tailWord_871366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871366).length < 2 ^ (prefixWord ++ tailWord_871366).sum := by decide
  have hdescent : baseEnd_871366 < baseStart_871366 := by decide
  rcases family_descends (prefixWord ++ tailWord_871366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871371 : List Nat := [1, 1, 1, 1, 3, 5, 1, 4, 5]
def baseStart_871371 : Nat := 118140960795 + 871371 * 2 ^ 59
def prefixEnd_871371 : Nat := 4983230072969 + 3 ^ 40 * 871371 * 2
def baseEnd_871371 : Nat := 99429366975336775701143

theorem tailTrace_871371 : CollatzResearch.WordTrace tailWord_871371 prefixEnd_871371 99429366975336775701143 := by
  unfold tailWord_871371
  simp only [CollatzResearch.WordTrace]
  refine ⟨31781511326179160163877967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21187674217452773442585311 31781511326179160163877967)
  ·
    refine ⟨47672266989268740245816951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31781511326179160163877967 47672266989268740245816951)
    ·
      refine ⟨71508400483903110368725427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47672266989268740245816951 71508400483903110368725427)
      ·
        refine ⟨107262600725854665553088141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71508400483903110368725427 107262600725854665553088141)
        ·
          refine ⟨40223475272195499582408053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107262600725854665553088141 40223475272195499582408053)
          ·
            refine ⟨3770950806768328085850755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40223475272195499582408053 3770950806768328085850755)
            ·
              refine ⟨5656426210152492128776133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3770950806768328085850755 5656426210152492128776133)
              ·
                refine ⟨1060579914403592274145525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5656426210152492128776133 1060579914403592274145525)
                ·
                  refine ⟨99429366975336775701143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1060579914403592274145525 99429366975336775701143)
                  ·
                    rfl

theorem cell22_871371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 4, 5].length) (baseStart_871371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_871371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_871371 prefixEnd_871371 := by exact prefixLift 871371
  have htrace : WordTrace (prefixWord ++ tailWord_871371) baseStart_871371 baseEnd_871371 := by
    simpa [prefixWord, tailWord_871371, baseEnd_871371] using wordTrace_append hprefix tailTrace_871371
  have hstable : (prefixWord ++ tailWord_871371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871371).length < 2 ^ (prefixWord ++ tailWord_871371).sum := by decide
  have hdescent : baseEnd_871371 < baseStart_871371 := by decide
  rcases family_descends (prefixWord ++ tailWord_871371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871375 : List Nat := [1, 1, 2, 1, 1, 7, 1, 4, 1, 3]
def baseStart_871375 : Nat := 118140960795 + 871375 * 2 ^ 59
def prefixEnd_871375 : Nat := 4983230072969 + 3 ^ 40 * 871375 * 2
def baseEnd_871375 : Nat := 298289470207755650003417

theorem tailTrace_871375 : CollatzResearch.WordTrace tailWord_871375 prefixEnd_871375 298289470207755650003417 := by
  unfold tailWord_871375
  simp only [CollatzResearch.WordTrace]
  refine ⟨31781657218164668847023579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21187771478776445898015719 31781657218164668847023579)
  ·
    refine ⟨47672485827247003270535369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31781657218164668847023579 47672485827247003270535369)
    ·
      refine ⟨35754364370435252452901527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47672485827247003270535369 35754364370435252452901527)
      ·
        refine ⟨53631546555652878679352291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35754364370435252452901527 53631546555652878679352291)
        ·
          refine ⟨80447319833479318019028437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53631546555652878679352291 80447319833479318019028437)
          ·
            refine ⟨1885484058597171516070979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 80447319833479318019028437 1885484058597171516070979)
            ·
              refine ⟨2828226087895757274106469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1885484058597171516070979 2828226087895757274106469)
              ·
                refine ⟨530292391480454488894963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2828226087895757274106469 530292391480454488894963)
                ·
                  refine ⟨795438587220681733342445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 530292391480454488894963 795438587220681733342445)
                  ·
                    refine ⟨298289470207755650003417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 795438587220681733342445 298289470207755650003417)
                    ·
                      rfl

theorem cell22_871375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 4, 1, 3].length) (baseStart_871375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_871375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_871375 prefixEnd_871375 := by exact prefixLift 871375
  have htrace : WordTrace (prefixWord ++ tailWord_871375) baseStart_871375 baseEnd_871375 := by
    simpa [prefixWord, tailWord_871375, baseEnd_871375] using wordTrace_append hprefix tailTrace_871375
  have hstable : (prefixWord ++ tailWord_871375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871375).length < 2 ^ (prefixWord ++ tailWord_871375).sum := by decide
  have hdescent : baseEnd_871375 < baseStart_871375 := by decide
  rcases family_descends (prefixWord ++ tailWord_871375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871386 : List Nat := [3, 1, 1, 2, 4, 1, 1, 1, 1, 7]
def baseStart_871386 : Nat := 118140960795 + 871386 * 2 ^ 59
def prefixEnd_871386 : Nat := 4983230072969 + 3 ^ 40 * 871386 * 2
def baseEnd_871386 : Nat := 298293235732555287978383

theorem tailTrace_871386 : CollatzResearch.WordTrace tailWord_871386 prefixEnd_871386 298293235732555287978383 := by
  unfold tailWord_871386
  simp only [CollatzResearch.WordTrace]
  refine ⟨7945514605281204431418503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21188038947416545150449341 7945514605281204431418503)
  ·
    refine ⟨11918271907921806647127755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7945514605281204431418503 11918271907921806647127755)
    ·
      refine ⟨17877407861882709970691633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11918271907921806647127755 17877407861882709970691633)
      ·
        refine ⟨13408055896412032478018725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17877407861882709970691633 13408055896412032478018725)
        ·
          refine ⟨2514010480577256089628511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13408055896412032478018725 2514010480577256089628511)
          ·
            refine ⟨3771015720865884134442767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2514010480577256089628511 3771015720865884134442767)
            ·
              refine ⟨5656523581298826201664151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3771015720865884134442767 5656523581298826201664151)
              ·
                refine ⟨8484785371948239302496227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5656523581298826201664151 8484785371948239302496227)
                ·
                  refine ⟨12727178057922358953744341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8484785371948239302496227 12727178057922358953744341)
                  ·
                    refine ⟨298293235732555287978383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12727178057922358953744341 298293235732555287978383)
                    ·
                      rfl

theorem cell22_871386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 1, 7].length) (baseStart_871386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_871386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_871386 prefixEnd_871386 := by exact prefixLift 871386
  have htrace : WordTrace (prefixWord ++ tailWord_871386) baseStart_871386 baseEnd_871386 := by
    simpa [prefixWord, tailWord_871386, baseEnd_871386] using wordTrace_append hprefix tailTrace_871386
  have hstable : (prefixWord ++ tailWord_871386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871386).length < 2 ^ (prefixWord ++ tailWord_871386).sum := by decide
  have hdescent : baseEnd_871386 < baseStart_871386 := by decide
  rcases family_descends (prefixWord ++ tailWord_871386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871422 : List Nat := [4, 2, 2, 2, 2, 2, 1, 2, 5]
def baseStart_871422 : Nat := 118140960795 + 871422 * 2 ^ 59
def prefixEnd_871422 : Nat := 4983230072969 + 3 ^ 40 * 871422 * 2
def baseEnd_871422 : Nat := 99435186422754398026091

theorem tailTrace_871422 : CollatzResearch.WordTrace tailWord_871422 prefixEnd_871422 99435186422754398026091 := by
  unfold tailWord_871422
  simp only [CollatzResearch.WordTrace]
  refine ⟨3972921431124299484248065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21188914299329597249323013 3972921431124299484248065)
  ·
    refine ⟨2979691073343224613186049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3972921431124299484248065 2979691073343224613186049)
    ·
      refine ⟨2234768305007418459889537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2979691073343224613186049 2234768305007418459889537)
      ·
        refine ⟨1676076228755563844917153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2234768305007418459889537 1676076228755563844917153)
        ·
          refine ⟨1257057171566672883687865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1676076228755563844917153 1257057171566672883687865)
          ·
            refine ⟨942792878675004662765899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1257057171566672883687865 942792878675004662765899)
            ·
              refine ⟨1414189318012506994148849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 942792878675004662765899 1414189318012506994148849)
              ·
                refine ⟨1060641988509380245611637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1414189318012506994148849 1060641988509380245611637)
                ·
                  refine ⟨99435186422754398026091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1060641988509380245611637 99435186422754398026091)
                  ·
                    rfl

theorem cell22_871422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 2, 5].length) (baseStart_871422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_871422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_871422 prefixEnd_871422 := by exact prefixLift 871422
  have htrace : WordTrace (prefixWord ++ tailWord_871422) baseStart_871422 baseEnd_871422 := by
    simpa [prefixWord, tailWord_871422, baseEnd_871422] using wordTrace_append hprefix tailTrace_871422
  have hstable : (prefixWord ++ tailWord_871422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871422).length < 2 ^ (prefixWord ++ tailWord_871422).sum := by decide
  have hdescent : baseEnd_871422 < baseStart_871422 := by decide
  rcases family_descends (prefixWord ++ tailWord_871422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871448 : List Nat := [2, 1, 2, 3, 2, 2, 3, 1, 1, 5]
def baseStart_871448 : Nat := 118140960795 + 871448 * 2 ^ 59
def prefixEnd_871448 : Nat := 4983230072969 + 3 ^ 40 * 871448 * 2
def baseEnd_871448 : Nat := 298314459599607792928193

theorem tailTrace_871448 : CollatzResearch.WordTrace tailWord_871448 prefixEnd_871448 298314459599607792928193 := by
  unfold tailWord_871448
  simp only [CollatzResearch.WordTrace]
  refine ⟨15892159873450101157215499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21189546497933468209620665 15892159873450101157215499)
  ·
    refine ⟨23838239810175151735823249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15892159873450101157215499 23838239810175151735823249)
    ·
      refine ⟨17878679857631363801867437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23838239810175151735823249 17878679857631363801867437)
      ·
        refine ⟨6704504946611761425700289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17878679857631363801867437 6704504946611761425700289)
        ·
          refine ⟨5028378709958821069275217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6704504946611761425700289 5028378709958821069275217)
          ·
            refine ⟨3771284032469115801956413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5028378709958821069275217 3771284032469115801956413)
            ·
              refine ⟨1414231512175918425733655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3771284032469115801956413 1414231512175918425733655)
              ·
                refine ⟨2121347268263877638600483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1414231512175918425733655 2121347268263877638600483)
                ·
                  refine ⟨3182020902395816457900725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2121347268263877638600483 3182020902395816457900725)
                  ·
                    refine ⟨298314459599607792928193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3182020902395816457900725 298314459599607792928193)
                    ·
                      rfl

theorem cell22_871448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 1, 1, 5].length) (baseStart_871448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_871448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_871448 prefixEnd_871448 := by exact prefixLift 871448
  have htrace : WordTrace (prefixWord ++ tailWord_871448) baseStart_871448 baseEnd_871448 := by
    simpa [prefixWord, tailWord_871448, baseEnd_871448] using wordTrace_append hprefix tailTrace_871448
  have hstable : (prefixWord ++ tailWord_871448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871448).length < 2 ^ (prefixWord ++ tailWord_871448).sum := by decide
  have hdescent : baseEnd_871448 < baseStart_871448 := by decide
  rcases family_descends (prefixWord ++ tailWord_871448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871461 : List Nat := [1, 3, 1, 2, 2, 2, 3, 8]
def baseStart_871461 : Nat := 118140960795 + 871461 * 2 ^ 59
def prefixEnd_871461 : Nat := 4983230072969 + 3 ^ 40 * 871461 * 2
def baseEnd_871461 : Nat := 33146545529475565817017

theorem tailTrace_871461 : CollatzResearch.WordTrace tailWord_871461 prefixEnd_871461 33146545529475565817017 := by
  unfold tailWord_871461
  simp only [CollatzResearch.WordTrace]
  refine ⟨31784793895853105534654237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21189862597235403689769491 31784793895853105534654237)
  ·
    refine ⟨11919297710944914575495339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31784793895853105534654237 11919297710944914575495339)
    ·
      refine ⟨17878946566417371863243009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11919297710944914575495339 17878946566417371863243009)
      ·
        refine ⟨13409209924813028897432257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17878946566417371863243009 13409209924813028897432257)
        ·
          refine ⟨10056907443609771673074193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13409209924813028897432257 10056907443609771673074193)
          ·
            refine ⟨7542680582707328754805645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10056907443609771673074193 7542680582707328754805645)
            ·
              refine ⟨2828505218515248283052117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7542680582707328754805645 2828505218515248283052117)
              ·
                refine ⟨33146545529475565817017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2828505218515248283052117 33146545529475565817017)
                ·
                  rfl

theorem cell22_871461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 8].length) (baseStart_871461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_871461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_871461 prefixEnd_871461 := by exact prefixLift 871461
  have htrace : WordTrace (prefixWord ++ tailWord_871461) baseStart_871461 baseEnd_871461 := by
    simpa [prefixWord, tailWord_871461, baseEnd_871461] using wordTrace_append hprefix tailTrace_871461
  have hstable : (prefixWord ++ tailWord_871461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871461).length < 2 ^ (prefixWord ++ tailWord_871461).sum := by decide
  have hdescent : baseEnd_871461 < baseStart_871461 := by decide
  rcases family_descends (prefixWord ++ tailWord_871461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871478 : List Nat := [5, 1, 2, 1, 1, 2, 10]
def baseStart_871478 : Nat := 118140960795 + 871478 * 2 ^ 59
def prefixEnd_871478 : Nat := 4983230072969 + 3 ^ 40 * 871478 * 2
def baseEnd_871478 : Nat := 11049064044914730173263

theorem tailTrace_871478 : CollatzResearch.WordTrace tailWord_871478 prefixEnd_871478 11049064044914730173263 := by
  unfold tailWord_871478
  simp only [CollatzResearch.WordTrace]
  refine ⟨1986588371049469839876443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21190275957861011625348725 1986588371049469839876443)
  ·
    refine ⟨2979882556574204759814665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1986588371049469839876443 2979882556574204759814665)
    ·
      refine ⟨2234911917430653569860999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2979882556574204759814665 2234911917430653569860999)
      ·
        refine ⟨3352367876145980354791499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2234911917430653569860999 3352367876145980354791499)
        ·
          refine ⟨5028551814218970532187249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3352367876145980354791499 5028551814218970532187249)
          ·
            refine ⟨3771413860664227899140437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5028551814218970532187249 3771413860664227899140437)
            ·
              refine ⟨11049064044914730173263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3771413860664227899140437 11049064044914730173263)
              ·
                rfl

theorem cell22_871478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 10].length) (baseStart_871478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_871478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_871478 prefixEnd_871478 := by exact prefixLift 871478
  have htrace : WordTrace (prefixWord ++ tailWord_871478) baseStart_871478 baseEnd_871478 := by
    simpa [prefixWord, tailWord_871478, baseEnd_871478] using wordTrace_append hprefix tailTrace_871478
  have hstable : (prefixWord ++ tailWord_871478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871478).length < 2 ^ (prefixWord ++ tailWord_871478).sum := by decide
  have hdescent : baseEnd_871478 < baseStart_871478 := by decide
  rcases family_descends (prefixWord ++ tailWord_871478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871491 : List Nat := [1, 1, 1, 3, 1, 2, 4, 1, 2, 6]
def baseStart_871491 : Nat := 118140960795 + 871491 * 2 ^ 59
def prefixEnd_871491 : Nat := 4983230072969 + 3 ^ 40 * 871491 * 2
def baseEnd_871491 : Nat := 298329179378370014103061

theorem tailTrace_871491 : CollatzResearch.WordTrace tailWord_871491 prefixEnd_871491 298329179378370014103061 := by
  unfold tailWord_871491
  simp only [CollatzResearch.WordTrace]
  refine ⟨31785888085744420658246327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21190592057162947105497551 31785888085744420658246327)
  ·
    refine ⟨47678832128616630987369491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31785888085744420658246327 47678832128616630987369491)
    ·
      refine ⟨71518248192924946481054237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47678832128616630987369491 71518248192924946481054237)
      ·
        refine ⟨26819343072346854930395339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71518248192924946481054237 26819343072346854930395339)
        ·
          refine ⟨40229014608520282395593009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26819343072346854930395339 40229014608520282395593009)
          ·
            refine ⟨30171760956390211796694757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40229014608520282395593009 30171760956390211796694757)
            ·
              refine ⟨5657205179323164711880267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30171760956390211796694757 5657205179323164711880267)
              ·
                refine ⟨8485807768984747067820401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5657205179323164711880267 8485807768984747067820401)
                ·
                  refine ⟨6364355826738560300865301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8485807768984747067820401 6364355826738560300865301)
                  ·
                    refine ⟨298329179378370014103061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6364355826738560300865301 298329179378370014103061)
                    ·
                      rfl

theorem cell22_871491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 2, 6].length) (baseStart_871491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_871491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_871491 prefixEnd_871491 := by exact prefixLift 871491
  have htrace : WordTrace (prefixWord ++ tailWord_871491) baseStart_871491 baseEnd_871491 := by
    simpa [prefixWord, tailWord_871491, baseEnd_871491] using wordTrace_append hprefix tailTrace_871491
  have hstable : (prefixWord ++ tailWord_871491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871491).length < 2 ^ (prefixWord ++ tailWord_871491).sum := by decide
  have hdescent : baseEnd_871491 < baseStart_871491 := by decide
  rcases family_descends (prefixWord ++ tailWord_871491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871538 : List Nat := [3, 2, 1, 2, 2, 1, 2, 2, 2, 5]
def baseStart_871538 : Nat := 118140960795 + 871538 * 2 ^ 59
def prefixEnd_871538 : Nat := 4983230072969 + 3 ^ 40 * 871538 * 2
def baseEnd_871538 : Nat := 298345268438877558177917

theorem tailTrace_871538 : CollatzResearch.WordTrace tailWord_871538 prefixEnd_871538 298345268438877558177917 := by
  unfold tailWord_871538
  simp only [CollatzResearch.WordTrace]
  refine ⟨7946900579143536921301817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21191734877716098456804845 7946900579143536921301817)
  ·
    refine ⟨5960175434357652690976363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7946900579143536921301817 5960175434357652690976363)
    ·
      refine ⟨8940263151536479036464545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5960175434357652690976363 8940263151536479036464545)
      ·
        refine ⟨6705197363652359277348409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8940263151536479036464545 6705197363652359277348409)
        ·
          refine ⟨5028898022739269458011307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6705197363652359277348409 5028898022739269458011307)
          ·
            refine ⟨7543347034108904187016961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5028898022739269458011307 7543347034108904187016961)
            ·
              refine ⟨5657510275581678140262721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7543347034108904187016961 5657510275581678140262721)
              ·
                refine ⟨4243132706686258605197041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5657510275581678140262721 4243132706686258605197041)
                ·
                  refine ⟨3182349530014693953897781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4243132706686258605197041 3182349530014693953897781)
                  ·
                    refine ⟨298345268438877558177917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3182349530014693953897781 298345268438877558177917)
                    ·
                      rfl

theorem cell22_871538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2, 2, 5].length) (baseStart_871538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_871538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_871538 prefixEnd_871538 := by exact prefixLift 871538
  have htrace : WordTrace (prefixWord ++ tailWord_871538) baseStart_871538 baseEnd_871538 := by
    simpa [prefixWord, tailWord_871538, baseEnd_871538] using wordTrace_append hprefix tailTrace_871538
  have hstable : (prefixWord ++ tailWord_871538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871538).length < 2 ^ (prefixWord ++ tailWord_871538).sum := by decide
  have hdescent : baseEnd_871538 < baseStart_871538 := by decide
  rcases family_descends (prefixWord ++ tailWord_871538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871551 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 12]
def baseStart_871551 : Nat := 118140960795 + 871551 * 2 ^ 59
def prefixEnd_871551 : Nat := 4983230072969 + 3 ^ 40 * 871551 * 2
def baseEnd_871551 : Nat := 99449906201516619200959

theorem tailTrace_871551 : CollatzResearch.WordTrace tailWord_871551 prefixEnd_871551 99449906201516619200959 := by
  unfold tailWord_871551
  simp only [CollatzResearch.WordTrace]
  refine ⟨31788076465527050905430507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21192050977018033936953671 31788076465527050905430507)
  ·
    refine ⟨47682114698290576358145761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31788076465527050905430507 47682114698290576358145761)
    ·
      refine ⟨35761586023717932268609321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47682114698290576358145761 35761586023717932268609321)
      ·
        refine ⟨26821189517788449201456991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35761586023717932268609321 26821189517788449201456991)
        ·
          refine ⟨40231784276682673802185487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26821189517788449201456991 40231784276682673802185487)
          ·
            refine ⟨60347676415024010703278231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40231784276682673802185487 60347676415024010703278231)
            ·
              refine ⟨90521514622536016054917347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60347676415024010703278231 90521514622536016054917347)
              ·
                refine ⟨135782271933804024082376021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90521514622536016054917347 135782271933804024082376021)
                ·
                  refine ⟨99449906201516619200959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 135782271933804024082376021 99449906201516619200959)
                  ·
                    rfl

theorem cell22_871551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 12].length) (baseStart_871551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_871551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_871551 prefixEnd_871551 := by exact prefixLift 871551
  have htrace : WordTrace (prefixWord ++ tailWord_871551) baseStart_871551 baseEnd_871551 := by
    simpa [prefixWord, tailWord_871551, baseEnd_871551] using wordTrace_append hprefix tailTrace_871551
  have hstable : (prefixWord ++ tailWord_871551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871551).length < 2 ^ (prefixWord ++ tailWord_871551).sum := by decide
  have hdescent : baseEnd_871551 < baseStart_871551 := by decide
  rcases family_descends (prefixWord ++ tailWord_871551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871570 : List Nat := [3, 2, 3, 1, 1, 2, 2, 1, 3, 4]
def baseStart_871570 : Nat := 118140960795 + 871570 * 2 ^ 59
def prefixEnd_871570 : Nat := 4983230072969 + 3 ^ 40 * 871570 * 2
def baseEnd_871570 : Nat := 298356222692840141377819

theorem tailTrace_871570 : CollatzResearch.WordTrace tailWord_871570 prefixEnd_871570 298356222692840141377819 := by
  unfold tailWord_871570
  simp only [CollatzResearch.WordTrace]
  refine ⟨7947192363114554287593041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21192512968305478100248109 7947192363114554287593041)
  ·
    refine ⟨5960394272335915715694781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7947192363114554287593041 5960394272335915715694781)
    ·
      refine ⟨2235147852125968393385543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5960394272335915715694781 2235147852125968393385543)
      ·
        refine ⟨3352721778188952590078315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2235147852125968393385543 3352721778188952590078315)
        ·
          refine ⟨5029082667283428885117473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3352721778188952590078315 5029082667283428885117473)
          ·
            refine ⟨3771812000462571663838105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5029082667283428885117473 3771812000462571663838105)
            ·
              refine ⟨2828859000346928747878579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3771812000462571663838105 2828859000346928747878579)
              ·
                refine ⟨4243288500520393121817869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2828859000346928747878579 4243288500520393121817869)
                ·
                  refine ⟨1591233187695147420681701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4243288500520393121817869 1591233187695147420681701)
                  ·
                    refine ⟨298356222692840141377819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1591233187695147420681701 298356222692840141377819)
                    ·
                      rfl

theorem cell22_871570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_871570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_871570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_871570 prefixEnd_871570 := by exact prefixLift 871570
  have htrace : WordTrace (prefixWord ++ tailWord_871570) baseStart_871570 baseEnd_871570 := by
    simpa [prefixWord, tailWord_871570, baseEnd_871570] using wordTrace_append hprefix tailTrace_871570
  have hstable : (prefixWord ++ tailWord_871570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871570).length < 2 ^ (prefixWord ++ tailWord_871570).sum := by decide
  have hdescent : baseEnd_871570 < baseStart_871570 := by decide
  rcases family_descends (prefixWord ++ tailWord_871570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871617 : List Nat := [1, 2, 6, 1, 1, 1, 3, 1, 1, 5]
def baseStart_871617 : Nat := 118140960795 + 871617 * 2 ^ 59
def prefixEnd_871617 : Nat := 4983230072969 + 3 ^ 40 * 871617 * 2
def baseEnd_871617 : Nat := 298372311753347685452675

theorem tailTrace_871617 : CollatzResearch.WordTrace tailWord_871617 prefixEnd_871617 298372311753347685452675 := by
  unfold tailWord_871617
  simp only [CollatzResearch.WordTrace]
  refine ⟨31790483683287944177333105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21193655788858629451555403 31790483683287944177333105)
  ·
    refine ⟨23842862762465958132999829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31790483683287944177333105 23842862762465958132999829)
    ·
      refine ⟨1117634191990591787484367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 23842862762465958132999829 1117634191990591787484367)
      ·
        refine ⟨1676451287985887681226551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1117634191990591787484367 1676451287985887681226551)
        ·
          refine ⟨2514676931978831521839827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1676451287985887681226551 2514676931978831521839827)
          ·
            refine ⟨3772015397968247282759741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2514676931978831521839827 3772015397968247282759741)
            ·
              refine ⟨1414505774238092731034903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3772015397968247282759741 1414505774238092731034903)
              ·
                refine ⟨2121758661357139096552355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1414505774238092731034903 2121758661357139096552355)
                ·
                  refine ⟨3182637992035708644828533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2121758661357139096552355 3182637992035708644828533)
                  ·
                    refine ⟨298372311753347685452675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3182637992035708644828533 298372311753347685452675)
                    ·
                      rfl

theorem cell22_871617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_871617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_871617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_871617 prefixEnd_871617 := by exact prefixLift 871617
  have htrace : WordTrace (prefixWord ++ tailWord_871617) baseStart_871617 baseEnd_871617 := by
    simpa [prefixWord, tailWord_871617, baseEnd_871617] using wordTrace_append hprefix tailTrace_871617
  have hstable : (prefixWord ++ tailWord_871617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871617).length < 2 ^ (prefixWord ++ tailWord_871617).sum := by decide
  have hdescent : baseEnd_871617 < baseStart_871617 := by decide
  rcases family_descends (prefixWord ++ tailWord_871617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871630 : List Nat := [4, 1, 1, 1, 5, 1, 1, 8]
def baseStart_871630 : Nat := 118140960795 + 871630 * 2 ^ 59
def prefixEnd_871630 : Nat := 4983230072969 + 3 ^ 40 * 871630 * 2
def baseEnd_871630 : Nat := 33152973546557776097515

theorem tailTrace_871630 : CollatzResearch.WordTrace tailWord_871630 prefixEnd_871630 33152973546557776097515 := by
  unfold tailWord_871630
  simp only [CollatzResearch.WordTrace]
  refine ⟨3973869729030105924694543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21193971888160564931704229 3973869729030105924694543)
  ·
    refine ⟨5960804593545158887041815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3973869729030105924694543 5960804593545158887041815)
    ·
      refine ⟨8941206890317738330562723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5960804593545158887041815 8941206890317738330562723)
      ·
        refine ⟨13411810335476607495844085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8941206890317738330562723 13411810335476607495844085)
        ·
          refine ⟨1257357218950931952735383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13411810335476607495844085 1257357218950931952735383)
          ·
            refine ⟨1886035828426397929103075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1257357218950931952735383 1886035828426397929103075)
            ·
              refine ⟨2829053742639596893654613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1886035828426397929103075 2829053742639596893654613)
              ·
                refine ⟨33152973546557776097515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2829053742639596893654613 33152973546557776097515)
                ·
                  rfl

theorem cell22_871630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 8].length) (baseStart_871630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_871630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_871630 prefixEnd_871630 := by exact prefixLift 871630
  have htrace : WordTrace (prefixWord ++ tailWord_871630) baseStart_871630 baseEnd_871630 := by
    simpa [prefixWord, tailWord_871630, baseEnd_871630] using wordTrace_append hprefix tailTrace_871630
  have hstable : (prefixWord ++ tailWord_871630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871630).length < 2 ^ (prefixWord ++ tailWord_871630).sum := by decide
  have hdescent : baseEnd_871630 < baseStart_871630 := by decide
  rcases family_descends (prefixWord ++ tailWord_871630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871636 : List Nat := [2, 4, 1, 4, 1, 2, 1, 3, 4]
def baseStart_871636 : Nat := 118140960795 + 871636 * 2 ^ 59
def prefixEnd_871636 : Nat := 4983230072969 + 3 ^ 40 * 871636 * 2
def baseEnd_871636 : Nat := 99459605280545989742539

theorem tailTrace_871636 : CollatzResearch.WordTrace tailWord_871636 prefixEnd_871636 99459605280545989742539 := by
  unfold tailWord_871636
  simp only [CollatzResearch.WordTrace]
  refine ⟨15895588335109555211137381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21194117780146073614849841 15895588335109555211137381)
  ·
    refine ⟨2980422812833041602088259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15895588335109555211137381 2980422812833041602088259)
    ·
      refine ⟨4470634219249562403132389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2980422812833041602088259 4470634219249562403132389)
      ·
        refine ⟨838243916109292950587323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4470634219249562403132389 838243916109292950587323)
        ·
          refine ⟨1257365874163939425880985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 838243916109292950587323 1257365874163939425880985)
          ·
            refine ⟨943024405622954569410739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1257365874163939425880985 943024405622954569410739)
            ·
              refine ⟨1414536608434431854116109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 943024405622954569410739 1414536608434431854116109)
              ·
                refine ⟨530451228162911945293541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1414536608434431854116109 530451228162911945293541)
                ·
                  refine ⟨99459605280545989742539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 530451228162911945293541 99459605280545989742539)
                  ·
                    rfl

theorem cell22_871636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 3, 4].length) (baseStart_871636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_871636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_871636 prefixEnd_871636 := by exact prefixLift 871636
  have htrace : WordTrace (prefixWord ++ tailWord_871636) baseStart_871636 baseEnd_871636 := by
    simpa [prefixWord, tailWord_871636, baseEnd_871636] using wordTrace_append hprefix tailTrace_871636
  have hstable : (prefixWord ++ tailWord_871636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871636).length < 2 ^ (prefixWord ++ tailWord_871636).sum := by decide
  have hdescent : baseEnd_871636 < baseStart_871636 := by decide
  rcases family_descends (prefixWord ++ tailWord_871636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871662 : List Nat := [4, 1, 2, 1, 1, 1, 5, 1, 3, 3]
def baseStart_871662 : Nat := 118140960795 + 871662 * 2 ^ 59
def prefixEnd_871662 : Nat := 4983230072969 + 3 ^ 40 * 871662 * 2
def baseEnd_871662 : Nat := 298387716172982568077537

theorem tailTrace_871662 : CollatzResearch.WordTrace tailWord_871662 prefixEnd_871662 298387716172982568077537 := by
  unfold tailWord_871662
  simp only [CollatzResearch.WordTrace]
  refine ⟨3974015621015614607840155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21194749978749944575147493 3974015621015614607840155)
  ·
    refine ⟨5961023431523421911760233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3974015621015614607840155 5961023431523421911760233)
    ·
      refine ⟨4470767573642566433820175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5961023431523421911760233 4470767573642566433820175)
      ·
        refine ⟨6706151360463849650730263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4470767573642566433820175 6706151360463849650730263)
        ·
          refine ⟨10059227040695774476095395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6706151360463849650730263 10059227040695774476095395)
          ·
            refine ⟨15088840561043661714143093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10059227040695774476095395 15088840561043661714143093)
            ·
              refine ⟨1414578802597843285700915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15088840561043661714143093 1414578802597843285700915)
              ·
                refine ⟨2121868203896764928551373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1414578802597843285700915 2121868203896764928551373)
                ·
                  refine ⟨795700576461286848206765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2121868203896764928551373 795700576461286848206765)
                  ·
                    refine ⟨298387716172982568077537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 795700576461286848206765 298387716172982568077537)
                    ·
                      rfl

theorem cell22_871662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 1, 3, 3].length) (baseStart_871662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_871662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_871662 prefixEnd_871662 := by exact prefixLift 871662
  have htrace : WordTrace (prefixWord ++ tailWord_871662) baseStart_871662 baseEnd_871662 := by
    simpa [prefixWord, tailWord_871662, baseEnd_871662] using wordTrace_append hprefix tailTrace_871662
  have hstable : (prefixWord ++ tailWord_871662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871662).length < 2 ^ (prefixWord ++ tailWord_871662).sum := by decide
  have hdescent : baseEnd_871662 < baseStart_871662 := by decide
  rcases family_descends (prefixWord ++ tailWord_871662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871668 : List Nat := [2, 6, 1, 2, 1, 1, 1, 3, 2, 3]
def baseStart_871668 : Nat := 118140960795 + 871668 * 2 ^ 59
def prefixEnd_871668 : Nat := 4983230072969 + 3 ^ 40 * 871668 * 2
def baseEnd_871668 : Nat := 298389770095600552427519

theorem tailTrace_871668 : CollatzResearch.WordTrace tailWord_871668 prefixEnd_871668 298389770095600552427519 := by
  unfold tailWord_871668
  simp only [CollatzResearch.WordTrace]
  refine ⟨15896171903051589943719829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21194895870735453258293105 15896171903051589943719829)
  ·
    refine ⟨745133057955543278611867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 15896171903051589943719829 745133057955543278611867)
    ·
      refine ⟨1117699586933314917917801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 745133057955543278611867 1117699586933314917917801)
      ·
        refine ⟨838274690199986188438351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1117699586933314917917801 838274690199986188438351)
        ·
          refine ⟨1257412035299979282657527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 838274690199986188438351 1257412035299979282657527)
          ·
            refine ⟨1886118052949968923986291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1257412035299979282657527 1886118052949968923986291)
            ·
              refine ⟨2829177079424953385979437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1886118052949968923986291 2829177079424953385979437)
              ·
                refine ⟨1060941404784357519742289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2829177079424953385979437 1060941404784357519742289)
                ·
                  refine ⟨795706053588268139806717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1060941404784357519742289 795706053588268139806717)
                  ·
                    refine ⟨298389770095600552427519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 795706053588268139806717 298389770095600552427519)
                    ·
                      rfl

theorem cell22_871668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_871668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_871668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_871668 prefixEnd_871668 := by exact prefixLift 871668
  have htrace : WordTrace (prefixWord ++ tailWord_871668) baseStart_871668 baseEnd_871668 := by
    simpa [prefixWord, tailWord_871668, baseEnd_871668] using wordTrace_append hprefix tailTrace_871668
  have hstable : (prefixWord ++ tailWord_871668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871668).length < 2 ^ (prefixWord ++ tailWord_871668).sum := by decide
  have hdescent : baseEnd_871668 < baseStart_871668 := by decide
  rcases family_descends (prefixWord ++ tailWord_871668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871673 : List Nat := [1, 2, 1, 3, 1, 1, 4, 1, 1, 7]
def baseStart_871673 : Nat := 118140960795 + 871673 * 2 ^ 59
def prefixEnd_871673 : Nat := 4983230072969 + 3 ^ 40 * 871673 * 2
def baseEnd_871673 : Nat := 298391481697782206052503

theorem tailTrace_871673 : CollatzResearch.WordTrace tailWord_871673 prefixEnd_871673 298391481697782206052503 := by
  unfold tailWord_871673
  simp only [CollatzResearch.WordTrace]
  refine ⟨31792526171085065741371673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21195017447390043827581115 31792526171085065741371673)
  ·
    refine ⟨23844394628313799306028755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31792526171085065741371673 23844394628313799306028755)
    ·
      refine ⟨35766591942470698959043133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23844394628313799306028755 35766591942470698959043133)
      ·
        refine ⟨13412471978426512109641175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35766591942470698959043133 13412471978426512109641175)
        ·
          refine ⟨20118707967639768164461763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13412471978426512109641175 20118707967639768164461763)
          ·
            refine ⟨30178061951459652246692645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20118707967639768164461763 30178061951459652246692645)
            ·
              refine ⟨5658386615898684796254871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30178061951459652246692645 5658386615898684796254871)
              ·
                refine ⟨8487579923848027194382307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5658386615898684796254871 8487579923848027194382307)
                ·
                  refine ⟨12731369885772040791573461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8487579923848027194382307 12731369885772040791573461)
                  ·
                    refine ⟨298391481697782206052503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12731369885772040791573461 298391481697782206052503)
                    ·
                      rfl

theorem cell22_871673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 7].length) (baseStart_871673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_871673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_871673 prefixEnd_871673 := by exact prefixLift 871673
  have htrace : WordTrace (prefixWord ++ tailWord_871673) baseStart_871673 baseEnd_871673 := by
    simpa [prefixWord, tailWord_871673, baseEnd_871673] using wordTrace_append hprefix tailTrace_871673
  have hstable : (prefixWord ++ tailWord_871673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871673).length < 2 ^ (prefixWord ++ tailWord_871673).sum := by decide
  have hdescent : baseEnd_871673 < baseStart_871673 := by decide
  rcases family_descends (prefixWord ++ tailWord_871673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871722 : List Nat := [3, 1, 4, 2, 1, 1, 1, 2, 3, 4]
def baseStart_871722 : Nat := 118140960795 + 871722 * 2 ^ 59
def prefixEnd_871722 : Nat := 4983230072969 + 3 ^ 40 * 871722 * 2
def baseEnd_871722 : Nat := 298408255399162411577353

theorem tailTrace_871722 : CollatzResearch.WordTrace tailWord_871722 prefixEnd_871722 298408255399162411577353 := by
  unfold tailWord_871722
  simp only [CollatzResearch.WordTrace]
  refine ⟨7948578336976886777476355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21196208898605031406603613 7948578336976886777476355)
  ·
    refine ⟨11922867505465330166214533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7948578336976886777476355 11922867505465330166214533)
    ·
      refine ⟨2235537657274749406165225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11922867505465330166214533 2235537657274749406165225)
      ·
        refine ⟨1676653242956062054623919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2235537657274749406165225 1676653242956062054623919)
        ·
          refine ⟨2514979864434093081935879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1676653242956062054623919 2514979864434093081935879)
          ·
            refine ⟨3772469796651139622903819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2514979864434093081935879 3772469796651139622903819)
            ·
              refine ⟨5658704694976709434355729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3772469796651139622903819 5658704694976709434355729)
              ·
                refine ⟨4244028521232532075766797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5658704694976709434355729 4244028521232532075766797)
                ·
                  refine ⟨1591510695462199528412549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4244028521232532075766797 1591510695462199528412549)
                  ·
                    refine ⟨298408255399162411577353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1591510695462199528412549 298408255399162411577353)
                    ·
                      rfl

theorem cell22_871722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_871722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_871722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_871722 prefixEnd_871722 := by exact prefixLift 871722
  have htrace : WordTrace (prefixWord ++ tailWord_871722) baseStart_871722 baseEnd_871722 := by
    simpa [prefixWord, tailWord_871722, baseEnd_871722] using wordTrace_append hprefix tailTrace_871722
  have hstable : (prefixWord ++ tailWord_871722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871722).length < 2 ^ (prefixWord ++ tailWord_871722).sum := by decide
  have hdescent : baseEnd_871722 < baseStart_871722 := by decide
  rcases family_descends (prefixWord ++ tailWord_871722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871735 : List Nat := [1, 1, 3, 1, 2, 1, 1, 1, 8, 3]
def baseStart_871735 : Nat := 118140960795 + 871735 * 2 ^ 59
def prefixEnd_871735 : Nat := 4983230072969 + 3 ^ 40 * 871735 * 2
def baseEnd_871735 : Nat := 298412705564834711002313

theorem tailTrace_871735 : CollatzResearch.WordTrace tailWord_871735 prefixEnd_871735 298412705564834711002313 := by
  unfold tailWord_871735
  simp only [CollatzResearch.WordTrace]
  refine ⟨31794787496860450330128659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21196524997906966886752439 31794787496860450330128659)
  ·
    refine ⟨47692181245290675495192989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31794787496860450330128659 47692181245290675495192989)
    ·
      refine ⟨17884567966984003310697371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47692181245290675495192989 17884567966984003310697371)
      ·
        refine ⟨26826851950476004966046057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17884567966984003310697371 26826851950476004966046057)
        ·
          refine ⟨20120138962857003724534543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26826851950476004966046057 20120138962857003724534543)
          ·
            refine ⟨30180208444285505586801815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20120138962857003724534543 30180208444285505586801815)
            ·
              refine ⟨45270312666428258380202723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30180208444285505586801815 45270312666428258380202723)
              ·
                refine ⟨67905468999642387570304085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45270312666428258380202723 67905468999642387570304085)
                ·
                  refine ⟨795767214839559229339501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 67905468999642387570304085 795767214839559229339501)
                  ·
                    refine ⟨298412705564834711002313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 795767214839559229339501 298412705564834711002313)
                    ·
                      rfl

theorem cell22_871735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 8, 3].length) (baseStart_871735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_871735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_871735 prefixEnd_871735 := by exact prefixLift 871735
  have htrace : WordTrace (prefixWord ++ tailWord_871735) baseStart_871735 baseEnd_871735 := by
    simpa [prefixWord, tailWord_871735, baseEnd_871735] using wordTrace_append hprefix tailTrace_871735
  have hstable : (prefixWord ++ tailWord_871735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871735).length < 2 ^ (prefixWord ++ tailWord_871735).sum := by decide
  have hdescent : baseEnd_871735 < baseStart_871735 := by decide
  rcases family_descends (prefixWord ++ tailWord_871735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871737 : List Nat := [1, 2, 1, 6, 2, 1, 1, 2, 6]
def baseStart_871737 : Nat := 118140960795 + 871737 * 2 ^ 59
def prefixEnd_871737 : Nat := 4983230072969 + 3 ^ 40 * 871737 * 2
def baseEnd_871737 : Nat := 99471130068569124150769

theorem tailTrace_871737 : CollatzResearch.WordTrace tailWord_871737 prefixEnd_871737 99471130068569124150769 := by
  unfold tailWord_871737
  simp only [CollatzResearch.WordTrace]
  refine ⟨31794860442853204671701465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21196573628568803114467643 31794860442853204671701465)
  ·
    refine ⟨23846145332139903503776099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31794860442853204671701465 23846145332139903503776099)
    ·
      refine ⟨35769217998209855255664149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23846145332139903503776099 35769217998209855255664149)
      ·
        refine ⟨1676682093666086965109257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 35769217998209855255664149 1676682093666086965109257)
        ·
          refine ⟨1257511570249565223831943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1676682093666086965109257 1257511570249565223831943)
          ·
            refine ⟨1886267355374347835747915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1257511570249565223831943 1886267355374347835747915)
            ·
              refine ⟨2829401033061521753621873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1886267355374347835747915 2829401033061521753621873)
              ·
                refine ⟨2122050774796141315216405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2829401033061521753621873 2122050774796141315216405)
                ·
                  refine ⟨99471130068569124150769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2122050774796141315216405 99471130068569124150769)
                  ·
                    rfl

theorem cell22_871737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 2, 6].length) (baseStart_871737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_871737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_871737 prefixEnd_871737 := by exact prefixLift 871737
  have htrace : WordTrace (prefixWord ++ tailWord_871737) baseStart_871737 baseEnd_871737 := by
    simpa [prefixWord, tailWord_871737, baseEnd_871737] using wordTrace_append hprefix tailTrace_871737
  have hstable : (prefixWord ++ tailWord_871737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871737).length < 2 ^ (prefixWord ++ tailWord_871737).sum := by decide
  have hdescent : baseEnd_871737 < baseStart_871737 := by decide
  rcases family_descends (prefixWord ++ tailWord_871737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871765 : List Nat := [1, 3, 2, 2, 3, 2, 9]
def baseStart_871765 : Nat := 118140960795 + 871765 * 2 ^ 59
def prefixEnd_871765 : Nat := 4983230072969 + 3 ^ 40 * 871765 * 2
def baseEnd_871765 : Nat := 11052702784367578990823

theorem tailTrace_871765 : CollatzResearch.WordTrace tailWord_871765 prefixEnd_871765 11052702784367578990823 := by
  unfold tailWord_871765
  simp only [CollatzResearch.WordTrace]
  refine ⟨31795881686751765453720749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21197254457834510302480499 31795881686751765453720749)
  ·
    refine ⟨11923455632531912045145281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31795881686751765453720749 11923455632531912045145281)
    ·
      refine ⟨8942591724398934033858961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11923455632531912045145281 8942591724398934033858961)
      ·
        refine ⟨6706943793299200525394221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8942591724398934033858961 6706943793299200525394221)
        ·
          refine ⟨2515103922487200197022833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6706943793299200525394221 2515103922487200197022833)
          ·
            refine ⟨1886327941865400147767125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2515103922487200197022833 1886327941865400147767125)
            ·
              refine ⟨11052702784367578990823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1886327941865400147767125 11052702784367578990823)
              ·
                rfl

theorem cell22_871765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 9].length) (baseStart_871765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_871765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_871765 prefixEnd_871765 := by exact prefixLift 871765
  have htrace : WordTrace (prefixWord ++ tailWord_871765) baseStart_871765 baseEnd_871765 := by
    simpa [prefixWord, tailWord_871765, baseEnd_871765] using wordTrace_append hprefix tailTrace_871765
  have hstable : (prefixWord ++ tailWord_871765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871765).length < 2 ^ (prefixWord ++ tailWord_871765).sum := by decide
  have hdescent : baseEnd_871765 < baseStart_871765 := by decide
  rcases family_descends (prefixWord ++ tailWord_871765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871786 : List Nat := [3, 1, 3, 3, 3, 1, 1, 1, 1, 5]
def baseStart_871786 : Nat := 118140960795 + 871786 * 2 ^ 59
def prefixEnd_871786 : Nat := 4983230072969 + 3 ^ 40 * 871786 * 2
def baseEnd_871786 : Nat := 298430163907087577977157

theorem tailTrace_871786 : CollatzResearch.WordTrace tailWord_871786 prefixEnd_871786 298430163907087577977157 := by
  unfold tailWord_871786
  simp only [CollatzResearch.WordTrace]
  refine ⟨7949161904918921510058803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21197765079783790693490141 7949161904918921510058803)
  ·
    refine ⟨11923742857378382265088205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7949161904918921510058803 11923742857378382265088205)
    ·
      refine ⟨4471403571516893349408077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11923742857378382265088205 4471403571516893349408077)
      ·
        refine ⟨1676776339318835006028029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4471403571516893349408077 1676776339318835006028029)
        ·
          refine ⟨628791127244563127260511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1676776339318835006028029 628791127244563127260511)
          ·
            refine ⟨943186690866844690890767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 628791127244563127260511 943186690866844690890767)
            ·
              refine ⟨1414780036300267036336151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 943186690866844690890767 1414780036300267036336151)
              ·
                refine ⟨2122170054450400554504227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1414780036300267036336151 2122170054450400554504227)
                ·
                  refine ⟨3183255081675600831756341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2122170054450400554504227 3183255081675600831756341)
                  ·
                    refine ⟨298430163907087577977157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3183255081675600831756341 298430163907087577977157)
                    ·
                      rfl

theorem cell22_871786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 1, 1, 5].length) (baseStart_871786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_871786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_871786 prefixEnd_871786 := by exact prefixLift 871786
  have htrace : WordTrace (prefixWord ++ tailWord_871786) baseStart_871786 baseEnd_871786 := by
    simpa [prefixWord, tailWord_871786, baseEnd_871786] using wordTrace_append hprefix tailTrace_871786
  have hstable : (prefixWord ++ tailWord_871786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871786).length < 2 ^ (prefixWord ++ tailWord_871786).sum := by decide
  have hdescent : baseEnd_871786 < baseStart_871786 := by decide
  rcases family_descends (prefixWord ++ tailWord_871786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871855 : List Nat := [1, 1, 2, 1, 2, 2, 1, 6, 6]
def baseStart_871855 : Nat := 118140960795 + 871855 * 2 ^ 59
def prefixEnd_871855 : Nat := 4983230072969 + 3 ^ 40 * 871855 * 2
def baseEnd_871855 : Nat := 99484594672398132667315

theorem tailTrace_871855 : CollatzResearch.WordTrace tailWord_871855 prefixEnd_871855 99484594672398132667315 := by
  unfold tailWord_871855
  simp only [CollatzResearch.WordTrace]
  refine ⟨31799164256425710824497019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21199442837617140549664679 31799164256425710824497019)
  ·
    refine ⟨47698746384638566236745529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31799164256425710824497019 47698746384638566236745529)
    ·
      refine ⟨35774059788478924677559147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47698746384638566236745529 35774059788478924677559147)
      ·
        refine ⟨53661089682718387016338721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35774059788478924677559147 53661089682718387016338721)
        ·
          refine ⟨40245817262038790262254041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53661089682718387016338721 40245817262038790262254041)
          ·
            refine ⟨30184362946529092696690531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40245817262038790262254041 30184362946529092696690531)
            ·
              refine ⟨45276544419793639045035797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30184362946529092696690531 45276544419793639045035797)
              ·
                refine ⟨2122338019677826830236053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 45276544419793639045035797 2122338019677826830236053)
                ·
                  refine ⟨99484594672398132667315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2122338019677826830236053 99484594672398132667315)
                  ·
                    rfl

theorem cell22_871855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 6, 6].length) (baseStart_871855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_871855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_871855 prefixEnd_871855 := by exact prefixLift 871855
  have htrace : WordTrace (prefixWord ++ tailWord_871855) baseStart_871855 baseEnd_871855 := by
    simpa [prefixWord, tailWord_871855, baseEnd_871855] using wordTrace_append hprefix tailTrace_871855
  have hstable : (prefixWord ++ tailWord_871855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871855).length < 2 ^ (prefixWord ++ tailWord_871855).sum := by decide
  have hdescent : baseEnd_871855 < baseStart_871855 := by decide
  rcases family_descends (prefixWord ++ tailWord_871855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871857 : List Nat := [1, 2, 2, 4, 1, 1, 3, 1, 3, 4]
def baseStart_871857 : Nat := 118140960795 + 871857 * 2 ^ 59
def prefixEnd_871857 : Nat := 4983230072969 + 3 ^ 40 * 871857 * 2
def baseEnd_871857 : Nat := 298454468658067059451939

theorem tailTrace_871857 : CollatzResearch.WordTrace tailWord_871857 prefixEnd_871857 298454468658067059451939 := by
  unfold tailWord_871857
  simp only [CollatzResearch.WordTrace]
  refine ⟨31799237202418465166069825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21199491468278976777379883 31799237202418465166069825)
  ·
    refine ⟨23849427901813848874552369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31799237202418465166069825 23849427901813848874552369)
    ·
      refine ⟨17887070926360386655914277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23849427901813848874552369 17887070926360386655914277)
      ·
        refine ⟨3353825798692572497983927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17887070926360386655914277 3353825798692572497983927)
        ·
          refine ⟨5030738698038858746975891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3353825798692572497983927 5030738698038858746975891)
          ·
            refine ⟨7546108047058288120463837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5030738698038858746975891 7546108047058288120463837)
            ·
              refine ⟨2829790517646858045173939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7546108047058288120463837 2829790517646858045173939)
              ·
                refine ⟨4244685776470287067760909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2829790517646858045173939 4244685776470287067760909)
                ·
                  refine ⟨1591757166176357650410341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4244685776470287067760909 1591757166176357650410341)
                  ·
                    refine ⟨298454468658067059451939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1591757166176357650410341 298454468658067059451939)
                    ·
                      rfl

theorem cell22_871857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 1, 3, 4].length) (baseStart_871857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_871857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_871857 prefixEnd_871857 := by exact prefixLift 871857
  have htrace : WordTrace (prefixWord ++ tailWord_871857) baseStart_871857 baseEnd_871857 := by
    simpa [prefixWord, tailWord_871857, baseEnd_871857] using wordTrace_append hprefix tailTrace_871857
  have hstable : (prefixWord ++ tailWord_871857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871857).length < 2 ^ (prefixWord ++ tailWord_871857).sum := by decide
  have hdescent : baseEnd_871857 < baseStart_871857 := by decide
  rcases family_descends (prefixWord ++ tailWord_871857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871887 : List Nat := [1, 1, 2, 1, 1, 4, 2, 3, 4, 3]
def baseStart_871887 : Nat := 118140960795 + 871887 * 2 ^ 59
def prefixEnd_871887 : Nat := 4983230072969 + 3 ^ 40 * 871887 * 2
def baseEnd_871887 : Nat := 298464738271156981201847

theorem tailTrace_871887 : CollatzResearch.WordTrace tailWord_871887 prefixEnd_871887 298464738271156981201847 := by
  unfold tailWord_871887
  simp only [CollatzResearch.WordTrace]
  refine ⟨31800331392309780289661915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21200220928206520193107943 31800331392309780289661915)
  ·
    refine ⟨47700497088464670434492873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31800331392309780289661915 47700497088464670434492873)
    ·
      refine ⟨35775372816348502825869655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47700497088464670434492873 35775372816348502825869655)
      ·
        refine ⟨53663059224522754238804483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35775372816348502825869655 53663059224522754238804483)
        ·
          refine ⟨80494588836784131358206725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53663059224522754238804483 80494588836784131358206725)
          ·
            refine ⟨15092735406897024629663761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80494588836784131358206725 15092735406897024629663761)
            ·
              refine ⟨11319551555172768472247821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15092735406897024629663761 11319551555172768472247821)
              ·
                refine ⟨4244831833189788177092933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11319551555172768472247821 4244831833189788177092933)
                ·
                  refine ⟨795905968723085283204925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4244831833189788177092933 795905968723085283204925)
                  ·
                    refine ⟨298464738271156981201847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 795905968723085283204925 298464738271156981201847)
                    ·
                      rfl

theorem cell22_871887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3, 4, 3].length) (baseStart_871887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_871887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_871887 prefixEnd_871887 := by exact prefixLift 871887
  have htrace : WordTrace (prefixWord ++ tailWord_871887) baseStart_871887 baseEnd_871887 := by
    simpa [prefixWord, tailWord_871887, baseEnd_871887] using wordTrace_append hprefix tailTrace_871887
  have hstable : (prefixWord ++ tailWord_871887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871887).length < 2 ^ (prefixWord ++ tailWord_871887).sum := by decide
  have hdescent : baseEnd_871887 < baseStart_871887 := by decide
  rcases family_descends (prefixWord ++ tailWord_871887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871915 : List Nat := [1, 1, 1, 1, 2, 3, 2, 1, 1, 9]
def baseStart_871915 : Nat := 118140960795 + 871915 * 2 ^ 59
def prefixEnd_871915 : Nat := 4983230072969 + 3 ^ 40 * 871915 * 2
def baseEnd_871915 : Nat := 298474323243374241501761

theorem tailTrace_871915 : CollatzResearch.WordTrace tailWord_871915 prefixEnd_871915 298474323243374241501761 := by
  unfold tailWord_871915
  simp only [CollatzResearch.WordTrace]
  refine ⟨31801352636208341071681199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21200901757472227381120799 31801352636208341071681199)
  ·
    refine ⟨47702028954312511607521799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31801352636208341071681199 47702028954312511607521799)
    ·
      refine ⟨71553043431468767411282699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47702028954312511607521799 71553043431468767411282699)
      ·
        refine ⟨107329565147203151116924049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71553043431468767411282699 107329565147203151116924049)
        ·
          refine ⟨80497173860402363337693037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107329565147203151116924049 80497173860402363337693037)
          ·
            refine ⟨30186440197650886251634889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80497173860402363337693037 30186440197650886251634889)
            ·
              refine ⟨22639830148238164688726167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30186440197650886251634889 22639830148238164688726167)
              ·
                refine ⟨33959745222357247033089251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22639830148238164688726167 33959745222357247033089251)
                ·
                  refine ⟨50939617833535870549633877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33959745222357247033089251 50939617833535870549633877)
                  ·
                    refine ⟨298474323243374241501761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 50939617833535870549633877 298474323243374241501761)
                    ·
                      rfl

theorem cell22_871915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 9].length) (baseStart_871915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_871915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_871915 prefixEnd_871915 := by exact prefixLift 871915
  have htrace : WordTrace (prefixWord ++ tailWord_871915) baseStart_871915 baseEnd_871915 := by
    simpa [prefixWord, tailWord_871915, baseEnd_871915] using wordTrace_append hprefix tailTrace_871915
  have hstable : (prefixWord ++ tailWord_871915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871915).length < 2 ^ (prefixWord ++ tailWord_871915).sum := by decide
  have hdescent : baseEnd_871915 < baseStart_871915 := by decide
  rcases family_descends (prefixWord ++ tailWord_871915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871938 : List Nat := [3, 4, 1, 2, 1, 1, 3, 2, 2, 3]
def baseStart_871938 : Nat := 118140960795 + 871938 * 2 ^ 59
def prefixEnd_871938 : Nat := 4983230072969 + 3 ^ 40 * 871938 * 2
def baseEnd_871938 : Nat := 298482196613409848176691

theorem tailTrace_871938 : CollatzResearch.WordTrace tailWord_871938 prefixEnd_871938 298482196613409848176691 := by
  unfold tailWord_871938
  simp only [CollatzResearch.WordTrace]
  refine ⟨7950547878781253999942117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21201461010083343999845645 7950547878781253999942117)
  ·
    refine ⟨1490727727271485124989147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7950547878781253999942117 1490727727271485124989147)
    ·
      refine ⟨2236091590907227687483721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1490727727271485124989147 2236091590907227687483721)
      ·
        refine ⟨1677068693180420765612791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2236091590907227687483721 1677068693180420765612791)
        ·
          refine ⟨2515603039770631148419187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1677068693180420765612791 2515603039770631148419187)
          ·
            refine ⟨3773404559655946722628781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2515603039770631148419187 3773404559655946722628781)
            ·
              refine ⟨1415026709870980020985793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3773404559655946722628781 1415026709870980020985793)
              ·
                refine ⟨1061270032403235015739345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1415026709870980020985793 1061270032403235015739345)
                ·
                  refine ⟨795952524302426261804509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1061270032403235015739345 795952524302426261804509)
                  ·
                    refine ⟨298482196613409848176691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 795952524302426261804509 298482196613409848176691)
                    ·
                      rfl

theorem cell22_871938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_871938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_871938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_871938 prefixEnd_871938 := by exact prefixLift 871938
  have htrace : WordTrace (prefixWord ++ tailWord_871938) baseStart_871938 baseEnd_871938 := by
    simpa [prefixWord, tailWord_871938, baseEnd_871938] using wordTrace_append hprefix tailTrace_871938
  have hstable : (prefixWord ++ tailWord_871938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871938).length < 2 ^ (prefixWord ++ tailWord_871938).sum := by decide
  have hdescent : baseEnd_871938 < baseStart_871938 := by decide
  rcases family_descends (prefixWord ++ tailWord_871938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872039 : List Nat := [1, 1, 5, 1, 1, 1, 2, 1, 6, 3]
def baseStart_872039 : Nat := 118140960795 + 872039 * 2 ^ 59
def prefixEnd_872039 : Nat := 4983230072969 + 3 ^ 40 * 872039 * 2
def baseEnd_872039 : Nat := 298516770977479251401381

theorem tailTrace_872039 : CollatzResearch.WordTrace tailWord_872039 prefixEnd_872039 298516770977479251401381 := by
  unfold tailWord_872039
  simp only [CollatzResearch.WordTrace]
  refine ⟨31805875287759110249195171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21203916858506073499463447 31805875287759110249195171)
  ·
    refine ⟨47708812931638665373792757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31805875287759110249195171 47708812931638665373792757)
    ·
      refine ⟨4472701212341124878793071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47708812931638665373792757 4472701212341124878793071)
      ·
        refine ⟨6709051818511687318189607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4472701212341124878793071 6709051818511687318189607)
        ·
          refine ⟨10063577727767530977284411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6709051818511687318189607 10063577727767530977284411)
          ·
            refine ⟨15095366591651296465926617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10063577727767530977284411 15095366591651296465926617)
            ·
              refine ⟨11321524943738472349444963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15095366591651296465926617 11321524943738472349444963)
              ·
                refine ⟨16982287415607708524167445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11321524943738472349444963 16982287415607708524167445)
                ·
                  refine ⟨796044722606611337070349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 16982287415607708524167445 796044722606611337070349)
                  ·
                    refine ⟨298516770977479251401381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 796044722606611337070349 298516770977479251401381)
                    ·
                      rfl

theorem cell22_872039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 6, 3].length) (baseStart_872039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_872039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_872039 prefixEnd_872039 := by exact prefixLift 872039
  have htrace : WordTrace (prefixWord ++ tailWord_872039) baseStart_872039 baseEnd_872039 := by
    simpa [prefixWord, tailWord_872039, baseEnd_872039] using wordTrace_append hprefix tailTrace_872039
  have hstable : (prefixWord ++ tailWord_872039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872039).length < 2 ^ (prefixWord ++ tailWord_872039).sum := by decide
  have hdescent : baseEnd_872039 < baseStart_872039 := by decide
  rcases family_descends (prefixWord ++ tailWord_872039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872067 : List Nat := [1, 1, 1, 3, 3, 1, 1, 2, 2, 7]
def baseStart_872067 : Nat := 118140960795 + 872067 * 2 ^ 59
def prefixEnd_872067 : Nat := 4983230072969 + 3 ^ 40 * 872067 * 2
def baseEnd_872067 : Nat := 298526355949696511701295

theorem tailTrace_872067 : CollatzResearch.WordTrace tailWord_872067 prefixEnd_872067 298526355949696511701295 := by
  unfold tailWord_872067
  simp only [CollatzResearch.WordTrace]
  refine ⟨31806896531657671031214455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21204597687771780687476303 31806896531657671031214455)
  ·
    refine ⟨47710344797486506546821683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31806896531657671031214455 47710344797486506546821683)
    ·
      refine ⟨71565517196229759820232525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47710344797486506546821683 71565517196229759820232525)
      ·
        refine ⟨26837068948586159932587197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71565517196229759820232525 26837068948586159932587197)
        ·
          refine ⟨10063900855719809974720199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26837068948586159932587197 10063900855719809974720199)
          ·
            refine ⟨15095851283579714962080299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10063900855719809974720199 15095851283579714962080299)
            ·
              refine ⟨22643776925369572443120449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15095851283579714962080299 22643776925369572443120449)
              ·
                refine ⟨16982832694027179332340337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22643776925369572443120449 16982832694027179332340337)
                ·
                  refine ⟨12737124520520384499255253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16982832694027179332340337 12737124520520384499255253)
                  ·
                    refine ⟨298526355949696511701295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12737124520520384499255253 298526355949696511701295)
                    ·
                      rfl

theorem cell22_872067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 7].length) (baseStart_872067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_872067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_872067 prefixEnd_872067 := by exact prefixLift 872067
  have htrace : WordTrace (prefixWord ++ tailWord_872067) baseStart_872067 baseEnd_872067 := by
    simpa [prefixWord, tailWord_872067, baseEnd_872067] using wordTrace_append hprefix tailTrace_872067
  have hstable : (prefixWord ++ tailWord_872067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872067).length < 2 ^ (prefixWord ++ tailWord_872067).sum := by decide
  have hdescent : baseEnd_872067 < baseStart_872067 := by decide
  rcases family_descends (prefixWord ++ tailWord_872067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872189 : List Nat := [1, 4, 1, 1, 1, 1, 2, 4, 1, 6]
def baseStart_872189 : Nat := 118140960795 + 872189 * 2 ^ 59
def prefixEnd_872189 : Nat := 4983230072969 + 3 ^ 40 * 872189 * 2
def baseEnd_872189 : Nat := 298568119042928860150921

theorem tailTrace_872189 : CollatzResearch.WordTrace tailWord_872189 prefixEnd_872189 298568119042928860150921 := by
  unfold tailWord_872189
  simp only [CollatzResearch.WordTrace]
  refine ⟨31811346237215685867155621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21207564158143790578103747 31811346237215685867155621)
  ·
    refine ⟨5964627419477941100091679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31811346237215685867155621 5964627419477941100091679)
    ·
      refine ⟨8946941129216911650137519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5964627419477941100091679 8946941129216911650137519)
      ·
        refine ⟨13420411693825367475206279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8946941129216911650137519 13420411693825367475206279)
        ·
          refine ⟨20130617540738051212809419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13420411693825367475206279 20130617540738051212809419)
          ·
            refine ⟨30195926311107076819214129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20130617540738051212809419 30195926311107076819214129)
            ·
              refine ⟨22646944733330307614410597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30195926311107076819214129 22646944733330307614410597)
              ·
                refine ⟨4246302137499432677701987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22646944733330307614410597 4246302137499432677701987)
                ·
                  refine ⟨6369453206249149016552981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4246302137499432677701987 6369453206249149016552981)
                  ·
                    refine ⟨298568119042928860150921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6369453206249149016552981 298568119042928860150921)
                    ·
                      rfl

theorem cell22_872189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4, 1, 6].length) (baseStart_872189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_872189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_872189 prefixEnd_872189 := by exact prefixLift 872189
  have htrace : WordTrace (prefixWord ++ tailWord_872189) baseStart_872189 baseEnd_872189 := by
    simpa [prefixWord, tailWord_872189, baseEnd_872189] using wordTrace_append hprefix tailTrace_872189
  have hstable : (prefixWord ++ tailWord_872189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872189).length < 2 ^ (prefixWord ++ tailWord_872189).sum := by decide
  have hdescent : baseEnd_872189 < baseStart_872189 := by decide
  rcases family_descends (prefixWord ++ tailWord_872189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872204 : List Nat := [2, 2, 1, 2, 2, 1, 4, 8]
def baseStart_872204 : Nat := 118140960795 + 872204 * 2 ^ 59
def prefixEnd_872204 : Nat := 4983230072969 + 3 ^ 40 * 872204 * 2
def baseEnd_872204 : Nat := 33174805983274869002875

theorem tailTrace_872204 : CollatzResearch.WordTrace tailWord_872204 prefixEnd_872204 33174805983274869002875 := by
  unfold tailWord_872204
  simp only [CollatzResearch.WordTrace]
  refine ⟨15905946666080671714475833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21207928888107562285967777 15905946666080671714475833)
  ·
    refine ⟨11929459999560503785856875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15905946666080671714475833 11929459999560503785856875)
    ·
      refine ⟨17894189999340755678785313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11929459999560503785856875 17894189999340755678785313)
      ·
        refine ⟨13420642499505566759088985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17894189999340755678785313 13420642499505566759088985)
        ·
          refine ⟨10065481874629175069316739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13420642499505566759088985 10065481874629175069316739)
          ·
            refine ⟨15098222811943762603975109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10065481874629175069316739 15098222811943762603975109)
            ·
              refine ⟨2830916777239455488245333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15098222811943762603975109 2830916777239455488245333)
              ·
                refine ⟨33174805983274869002875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2830916777239455488245333 33174805983274869002875)
                ·
                  rfl

theorem cell22_872204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 8].length) (baseStart_872204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_872204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_872204 prefixEnd_872204 := by exact prefixLift 872204
  have htrace : WordTrace (prefixWord ++ tailWord_872204) baseStart_872204 baseEnd_872204 := by
    simpa [prefixWord, tailWord_872204, baseEnd_872204] using wordTrace_append hprefix tailTrace_872204
  have hstable : (prefixWord ++ tailWord_872204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872204).length < 2 ^ (prefixWord ++ tailWord_872204).sum := by decide
  have hdescent : baseEnd_872204 < baseStart_872204 := by decide
  rcases family_descends (prefixWord ++ tailWord_872204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872206 : List Nat := [4, 1, 1, 2, 1, 1, 3, 3, 2, 4]
def baseStart_872206 : Nat := 118140960795 + 872206 * 2 ^ 59
def prefixEnd_872206 : Nat := 4983230072969 + 3 ^ 40 * 872206 * 2
def baseEnd_872206 : Nat := 298573938490346482475869

theorem tailTrace_872206 : CollatzResearch.WordTrace tailWord_872206 prefixEnd_872206 298573938490346482475869 := by
  unfold tailWord_872206
  simp only [CollatzResearch.WordTrace]
  refine ⟨3976495784769262221315559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21207977518769398513682981 3976495784769262221315559)
  ·
    refine ⟨5964743677153893331973339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3976495784769262221315559 5964743677153893331973339)
    ·
      refine ⟨8947115515730839997960009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5964743677153893331973339 8947115515730839997960009)
      ·
        refine ⟨6710336636798129998470007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8947115515730839997960009 6710336636798129998470007)
        ·
          refine ⟨10065504955197194997705011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6710336636798129998470007 10065504955197194997705011)
          ·
            refine ⟨15098257432795792496557517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10065504955197194997705011 15098257432795792496557517)
            ·
              refine ⟨5661846537298422186209069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15098257432795792496557517 5661846537298422186209069)
              ·
                refine ⟨2123192451486908319828401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5661846537298422186209069 2123192451486908319828401)
                ·
                  refine ⟨1592394338615181239871301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2123192451486908319828401 1592394338615181239871301)
                  ·
                    refine ⟨298573938490346482475869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1592394338615181239871301 298573938490346482475869)
                    ·
                      rfl

theorem cell22_872206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 3, 2, 4].length) (baseStart_872206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_872206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_872206 prefixEnd_872206 := by exact prefixLift 872206
  have htrace : WordTrace (prefixWord ++ tailWord_872206) baseStart_872206 baseEnd_872206 := by
    simpa [prefixWord, tailWord_872206, baseEnd_872206] using wordTrace_append hprefix tailTrace_872206
  have hstable : (prefixWord ++ tailWord_872206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872206).length < 2 ^ (prefixWord ++ tailWord_872206).sum := by decide
  have hdescent : baseEnd_872206 < baseStart_872206 := by decide
  rcases family_descends (prefixWord ++ tailWord_872206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872253 : List Nat := [1, 4, 1, 4, 1, 1, 1, 1, 5, 3]
def baseStart_872253 : Nat := 118140960795 + 872253 * 2 ^ 59
def prefixEnd_872253 : Nat := 4983230072969 + 3 ^ 40 * 872253 * 2
def baseEnd_872253 : Nat := 298590027550854026550725

theorem tailTrace_872253 : CollatzResearch.WordTrace tailWord_872253 prefixEnd_872253 298590027550854026550725 := by
  unfold tailWord_872253
  simp only [CollatzResearch.WordTrace]
  refine ⟨31813680508983824797485413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21209120339322549864990275 31813680508983824797485413)
  ·
    refine ⟨5965065095434467149528515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31813680508983824797485413 5965065095434467149528515)
    ·
      refine ⟨8947597643151700724292773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5965065095434467149528515 8947597643151700724292773)
      ·
        refine ⟨1677674558090943885804895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8947597643151700724292773 1677674558090943885804895)
        ·
          refine ⟨2516511837136415828707343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1677674558090943885804895 2516511837136415828707343)
          ·
            refine ⟨3774767755704623743061015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2516511837136415828707343 3774767755704623743061015)
            ·
              refine ⟨5662151633556935614591523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3774767755704623743061015 5662151633556935614591523)
              ·
                refine ⟨8493227450335403421887285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5662151633556935614591523 8493227450335403421887285)
                ·
                  refine ⟨796240073468944070801933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8493227450335403421887285 796240073468944070801933)
                  ·
                    refine ⟨298590027550854026550725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 796240073468944070801933 298590027550854026550725)
                    ·
                      rfl

theorem cell22_872253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 5, 3].length) (baseStart_872253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_872253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_872253 prefixEnd_872253 := by exact prefixLift 872253
  have htrace : WordTrace (prefixWord ++ tailWord_872253) baseStart_872253 baseEnd_872253 := by
    simpa [prefixWord, tailWord_872253, baseEnd_872253] using wordTrace_append hprefix tailTrace_872253
  have hstable : (prefixWord ++ tailWord_872253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872253).length < 2 ^ (prefixWord ++ tailWord_872253).sum := by decide
  have hdescent : baseEnd_872253 < baseStart_872253 := by decide
  rcases family_descends (prefixWord ++ tailWord_872253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872313 : List Nat := [1, 2, 1, 3, 2, 2, 4, 2, 1, 4]
def baseStart_872313 : Nat := 118140960795 + 872313 * 2 ^ 59
def prefixEnd_872313 : Nat := 4983230072969 + 3 ^ 40 * 872313 * 2
def baseEnd_872313 : Nat := 298610566777033870050541

theorem tailTrace_872313 : CollatzResearch.WordTrace tailWord_872313 prefixEnd_872313 298610566777033870050541 := by
  unfold tailWord_872313
  simp only [CollatzResearch.WordTrace]
  refine ⟨31815868888766455044669593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21210579259177636696446395 31815868888766455044669593)
  ·
    refine ⟨23861901666574841283502195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31815868888766455044669593 23861901666574841283502195)
    ·
      refine ⟨35792852499862261925253293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23861901666574841283502195 35792852499862261925253293)
      ·
        refine ⟨13422319687448348221969985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35792852499862261925253293 13422319687448348221969985)
        ·
          refine ⟨10066739765586261166477489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13422319687448348221969985 10066739765586261166477489)
          ·
            refine ⟨7550054824189695874858117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10066739765586261166477489 7550054824189695874858117)
            ·
              refine ⟨1415635279535567976535897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7550054824189695874858117 1415635279535567976535897)
              ·
                refine ⟨1061726459651675982401923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1415635279535567976535897 1061726459651675982401923)
                ·
                  refine ⟨1592589689477513973602885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1061726459651675982401923 1592589689477513973602885)
                  ·
                    refine ⟨298610566777033870050541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1592589689477513973602885 298610566777033870050541)
                    ·
                      rfl

theorem cell22_872313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 2, 1, 4].length) (baseStart_872313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_872313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_872313 prefixEnd_872313 := by exact prefixLift 872313
  have htrace : WordTrace (prefixWord ++ tailWord_872313) baseStart_872313 baseEnd_872313 := by
    simpa [prefixWord, tailWord_872313, baseEnd_872313] using wordTrace_append hprefix tailTrace_872313
  have hstable : (prefixWord ++ tailWord_872313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872313).length < 2 ^ (prefixWord ++ tailWord_872313).sum := by decide
  have hdescent : baseEnd_872313 < baseStart_872313 := by decide
  rcases family_descends (prefixWord ++ tailWord_872313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872321 : List Nat := [1, 2, 4, 4, 2, 1, 1, 3, 1, 3]
def baseStart_872321 : Nat := 118140960795 + 872321 * 2 ^ 59
def prefixEnd_872321 : Nat := 4983230072969 + 3 ^ 40 * 872321 * 2
def baseEnd_872321 : Nat := 298613305340524515850517

theorem tailTrace_872321 : CollatzResearch.WordTrace tailWord_872321 prefixEnd_872321 298613305340524515850517 := by
  unfold tailWord_872321
  simp only [CollatzResearch.WordTrace]
  refine ⟨31816160672737472410960817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21210773781824981607307211 31816160672737472410960817)
  ·
    refine ⟨23862120504553104308220613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31816160672737472410960817 23862120504553104308220613)
    ·
      refine ⟨4474147594603707057791365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23862120504553104308220613 4474147594603707057791365)
      ·
        refine ⟨838902673988195073335881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4474147594603707057791365 838902673988195073335881)
        ·
          refine ⟨629177005491146305001911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 838902673988195073335881 629177005491146305001911)
          ·
            refine ⟨943765508236719457502867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 629177005491146305001911 943765508236719457502867)
            ·
              refine ⟨1415648262355079186254301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 943765508236719457502867 1415648262355079186254301)
              ·
                refine ⟨530868098383154694845363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1415648262355079186254301 530868098383154694845363)
                ·
                  refine ⟨796302147574732042268045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 530868098383154694845363 796302147574732042268045)
                  ·
                    refine ⟨298613305340524515850517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 796302147574732042268045 298613305340524515850517)
                    ·
                      rfl

theorem cell22_872321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 3, 1, 3].length) (baseStart_872321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_872321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_872321 prefixEnd_872321 := by exact prefixLift 872321
  have htrace : WordTrace (prefixWord ++ tailWord_872321) baseStart_872321 baseEnd_872321 := by
    simpa [prefixWord, tailWord_872321, baseEnd_872321] using wordTrace_append hprefix tailTrace_872321
  have hstable : (prefixWord ++ tailWord_872321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872321).length < 2 ^ (prefixWord ++ tailWord_872321).sum := by decide
  have hdescent : baseEnd_872321 < baseStart_872321 := by decide
  rcases family_descends (prefixWord ++ tailWord_872321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872343 : List Nat := [1, 1, 3, 3, 1, 3, 2, 1, 4, 3]
def baseStart_872343 : Nat := 118140960795 + 872343 * 2 ^ 59
def prefixEnd_872343 : Nat := 4983230072969 + 3 ^ 40 * 872343 * 2
def baseEnd_872343 : Nat := 298620836390123791800449

theorem tailTrace_872343 : CollatzResearch.WordTrace tailWord_872343 prefixEnd_872343 298620836390123791800449 := by
  unfold tailWord_872343
  simp only [CollatzResearch.WordTrace]
  refine ⟨31816963078657770168261683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21211308719105180112174455 31816963078657770168261683)
  ·
    refine ⟨47725444617986655252392525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31816963078657770168261683 47725444617986655252392525)
    ·
      refine ⟨17897041731744995719647197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47725444617986655252392525 17897041731744995719647197)
      ·
        refine ⟨6711390649404373394867699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17897041731744995719647197 6711390649404373394867699)
        ·
          refine ⟨10067085974106560092301549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6711390649404373394867699 10067085974106560092301549)
          ·
            refine ⟨3775157240289960034613081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10067085974106560092301549 3775157240289960034613081)
            ·
              refine ⟨2831367930217470025959811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3775157240289960034613081 2831367930217470025959811)
              ·
                refine ⟨4247051895326205038939717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2831367930217470025959811 4247051895326205038939717)
                ·
                  refine ⟨796322230373663444801197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4247051895326205038939717 796322230373663444801197)
                  ·
                    refine ⟨298620836390123791800449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 796322230373663444801197 298620836390123791800449)
                    ·
                      rfl

theorem cell22_872343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 1, 4, 3].length) (baseStart_872343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_872343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_872343 prefixEnd_872343 := by exact prefixLift 872343
  have htrace : WordTrace (prefixWord ++ tailWord_872343) baseStart_872343 baseEnd_872343 := by
    simpa [prefixWord, tailWord_872343, baseEnd_872343] using wordTrace_append hprefix tailTrace_872343
  have hstable : (prefixWord ++ tailWord_872343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872343).length < 2 ^ (prefixWord ++ tailWord_872343).sum := by decide
  have hdescent : baseEnd_872343 < baseStart_872343 := by decide
  rcases family_descends (prefixWord ++ tailWord_872343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872356 : List Nat := [2, 3, 1, 2, 1, 3, 1, 9]
def baseStart_872356 : Nat := 118140960795 + 872356 * 2 ^ 59
def prefixEnd_872356 : Nat := 4983230072969 + 3 ^ 40 * 872356 * 2
def baseEnd_872356 : Nat := 33180587395088454580601

theorem tailTrace_872356 : CollatzResearch.WordTrace tailWord_872356 prefixEnd_872356 33180587395088454580601 := by
  unfold tailWord_872356
  simp only [CollatzResearch.WordTrace]
  refine ⟨15908718613805336694242461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21211624818407115592323281 15908718613805336694242461)
  ·
    refine ⟨5965769480177001260340923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15908718613805336694242461 5965769480177001260340923)
    ·
      refine ⟨8948654220265501890511385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5965769480177001260340923 8948654220265501890511385)
      ·
        refine ⟨6711490665199126417883539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8948654220265501890511385 6711490665199126417883539)
        ·
          refine ⟨10067235997798689626825309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6711490665199126417883539 10067235997798689626825309)
          ·
            refine ⟨3775213499174508610059491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10067235997798689626825309 3775213499174508610059491)
            ·
              refine ⟨5662820248761762915089237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3775213499174508610059491 5662820248761762915089237)
              ·
                refine ⟨33180587395088454580601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5662820248761762915089237 33180587395088454580601)
                ·
                  rfl

theorem cell22_872356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 9].length) (baseStart_872356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_872356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_872356 prefixEnd_872356 := by exact prefixLift 872356
  have htrace : WordTrace (prefixWord ++ tailWord_872356) baseStart_872356 baseEnd_872356 := by
    simpa [prefixWord, tailWord_872356, baseEnd_872356] using wordTrace_append hprefix tailTrace_872356
  have hstable : (prefixWord ++ tailWord_872356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872356).length < 2 ^ (prefixWord ++ tailWord_872356).sum := by decide
  have hdescent : baseEnd_872356 < baseStart_872356 := by decide
  rcases family_descends (prefixWord ++ tailWord_872356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872390 : List Nat := [6, 1, 3, 12]
def baseStart_872390 : Nat := 118140960795 + 872390 * 2 ^ 59
def prefixEnd_872390 : Nat := 4983230072969 + 3 ^ 40 * 872390 * 2
def baseEnd_872390 : Nat := 409652846983033382545

theorem tailTrace_872390 : CollatzResearch.WordTrace tailWord_872390 prefixEnd_872390 409652846983033382545 := by
  unfold tailWord_872390
  simp only [CollatzResearch.WordTrace]
  refine ⟨994333665921484287350707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 21212451539658331463481749 994333665921484287350707)
  ·
    refine ⟨1491500498882226431026061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 994333665921484287350707 1491500498882226431026061)
    ·
      refine ⟨559312687080834911634773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1491500498882226431026061 559312687080834911634773)
      ·
        refine ⟨409652846983033382545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 559312687080834911634773 409652846983033382545)
        ·
          rfl

theorem cell22_872390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 12].length) (baseStart_872390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_872390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_872390 prefixEnd_872390 := by exact prefixLift 872390
  have htrace : WordTrace (prefixWord ++ tailWord_872390) baseStart_872390 baseEnd_872390 := by
    simpa [prefixWord, tailWord_872390, baseEnd_872390] using wordTrace_append hprefix tailTrace_872390
  have hstable : (prefixWord ++ tailWord_872390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872390).length < 2 ^ (prefixWord ++ tailWord_872390).sum := by decide
  have hdescent : baseEnd_872390 < baseStart_872390 := by decide
  rcases family_descends (prefixWord ++ tailWord_872390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872497 : List Nat := [1, 2, 2, 3, 1, 5, 1, 3, 4]
def baseStart_872497 : Nat := 118140960795 + 872497 * 2 ^ 59
def prefixEnd_872497 : Nat := 4983230072969 + 3 ^ 40 * 872497 * 2
def baseEnd_872497 : Nat := 99557851245772907816659

theorem tailTrace_872497 : CollatzResearch.WordTrace tailWord_872497 prefixEnd_872497 99557851245772907816659 := by
  unfold tailWord_872497
  simp only [CollatzResearch.WordTrace]
  refine ⟨31822579920099854469367745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21215053280066569646245163 31822579920099854469367745)
  ·
    refine ⟨23866934940074890852025809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31822579920099854469367745 23866934940074890852025809)
    ·
      refine ⟨17900201205056168139019357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23866934940074890852025809 17900201205056168139019357)
      ·
        refine ⟨6712575451896063052132259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17900201205056168139019357 6712575451896063052132259)
        ·
          refine ⟨10068863177844094578198389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6712575451896063052132259 10068863177844094578198389)
          ·
            refine ⟨943955922922883866706099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10068863177844094578198389 943955922922883866706099)
            ·
              refine ⟨1415933884384325800059149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 943955922922883866706099 1415933884384325800059149)
              ·
                refine ⟨530975206644122175022181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1415933884384325800059149 530975206644122175022181)
                ·
                  refine ⟨99557851245772907816659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 530975206644122175022181 99557851245772907816659)
                  ·
                    rfl

theorem cell22_872497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 3, 4].length) (baseStart_872497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_872497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_872497 prefixEnd_872497 := by exact prefixLift 872497
  have htrace : WordTrace (prefixWord ++ tailWord_872497) baseStart_872497 baseEnd_872497 := by
    simpa [prefixWord, tailWord_872497, baseEnd_872497] using wordTrace_append hprefix tailTrace_872497
  have hstable : (prefixWord ++ tailWord_872497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872497).length < 2 ^ (prefixWord ++ tailWord_872497).sum := by decide
  have hdescent : baseEnd_872497 < baseStart_872497 := by decide
  rcases family_descends (prefixWord ++ tailWord_872497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872525 : List Nat := [1, 6, 1, 1, 1, 1, 4, 7]
def baseStart_872525 : Nat := 118140960795 + 872525 * 2 ^ 59
def prefixEnd_872525 : Nat := 4983230072969 + 3 ^ 40 * 872525 * 2
def baseEnd_872525 : Nat := 33187015412170664861099

theorem tailTrace_872525 : CollatzResearch.WordTrace tailWord_872525 prefixEnd_872525 33187015412170664861099 := by
  unfold tailWord_872525
  simp only [CollatzResearch.WordTrace]
  refine ⟨31823601163998415251387029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21215734109332276834258019 31823601163998415251387029)
  ·
    refine ⟨1491731304562425714908767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 31823601163998415251387029 1491731304562425714908767)
    ·
      refine ⟨2237596956843638572363151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1491731304562425714908767 2237596956843638572363151)
      ·
        refine ⟨3356395435265457858544727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2237596956843638572363151 3356395435265457858544727)
        ·
          refine ⟨5034593152898186787817091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3356395435265457858544727 5034593152898186787817091)
          ·
            refine ⟨7551889729347280181725637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5034593152898186787817091 7551889729347280181725637)
            ·
              refine ⟨1415979324252615034073557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7551889729347280181725637 1415979324252615034073557)
              ·
                refine ⟨33187015412170664861099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1415979324252615034073557 33187015412170664861099)
                ·
                  rfl

theorem cell22_872525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 7].length) (baseStart_872525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_872525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_872525 prefixEnd_872525 := by exact prefixLift 872525
  have htrace : WordTrace (prefixWord ++ tailWord_872525) baseStart_872525 baseEnd_872525 := by
    simpa [prefixWord, tailWord_872525, baseEnd_872525] using wordTrace_append hprefix tailTrace_872525
  have hstable : (prefixWord ++ tailWord_872525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872525).length < 2 ^ (prefixWord ++ tailWord_872525).sum := by decide
  have hdescent : baseEnd_872525 < baseStart_872525 := by decide
  rcases family_descends (prefixWord ++ tailWord_872525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872568 : List Nat := [2, 1, 2, 1, 1, 1, 3, 4, 2, 5]
def baseStart_872568 : Nat := 118140960795 + 872568 * 2 ^ 59
def prefixEnd_872568 : Nat := 4983230072969 + 3 ^ 40 * 872568 * 2
def baseEnd_872568 : Nat := 298697858488298204924759

theorem tailTrace_872568 : CollatzResearch.WordTrace tailWord_872568 prefixEnd_872568 298697858488298204924759 := by
  unfold tailWord_872568
  simp only [CollatzResearch.WordTrace]
  refine ⟨15912584751421316797601179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21216779668561755730134905 15912584751421316797601179)
  ·
    refine ⟨23868877127131975196401769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15912584751421316797601179 23868877127131975196401769)
    ·
      refine ⟨17901657845348981397301327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23868877127131975196401769 17901657845348981397301327)
      ·
        refine ⟨26852486768023472095951991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17901657845348981397301327 26852486768023472095951991)
        ·
          refine ⟨40278730152035208143927987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26852486768023472095951991 40278730152035208143927987)
          ·
            refine ⟨60418095228052812215891981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40278730152035208143927987 60418095228052812215891981)
            ·
              refine ⟨22656785710519804580959493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60418095228052812215891981 22656785710519804580959493)
              ·
                refine ⟨4248147320722463358929905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22656785710519804580959493 4248147320722463358929905)
                ·
                  refine ⟨3186110490541847519197429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4248147320722463358929905 3186110490541847519197429)
                  ·
                    refine ⟨298697858488298204924759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3186110490541847519197429 298697858488298204924759)
                    ·
                      rfl

theorem cell22_872568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4, 2, 5].length) (baseStart_872568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_872568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_872568 prefixEnd_872568 := by exact prefixLift 872568
  have htrace : WordTrace (prefixWord ++ tailWord_872568) baseStart_872568 baseEnd_872568 := by
    simpa [prefixWord, tailWord_872568, baseEnd_872568] using wordTrace_append hprefix tailTrace_872568
  have hstable : (prefixWord ++ tailWord_872568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872568).length < 2 ^ (prefixWord ++ tailWord_872568).sum := by decide
  have hdescent : baseEnd_872568 < baseStart_872568 := by decide
  rcases family_descends (prefixWord ++ tailWord_872568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872784 : List Nat := [2, 1, 1, 1, 1, 7, 2, 3, 4]
def baseStart_872784 : Nat := 118140960795 + 872784 * 2 ^ 59
def prefixEnd_872784 : Nat := 4983230072969 + 3 ^ 40 * 872784 * 2
def baseEnd_872784 : Nat := 99590599900848547174699

theorem tailTrace_872784 : CollatzResearch.WordTrace tailWord_872784 prefixEnd_872784 99590599900848547174699 := by
  unfold tailWord_872784
  simp only [CollatzResearch.WordTrace]
  refine ⟨15916523835030051242532703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21222031780040068323376937 15916523835030051242532703)
  ·
    refine ⟨23874785752545076863799055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15916523835030051242532703 23874785752545076863799055)
    ·
      refine ⟨35812178628817615295698583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23874785752545076863799055 35812178628817615295698583)
      ·
        refine ⟨53718267943226422943547875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35812178628817615295698583 53718267943226422943547875)
        ·
          refine ⟨80577401914839634415321813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53718267943226422943547875 80577401914839634415321813)
          ·
            refine ⟨1888532857379053931609105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 80577401914839634415321813 1888532857379053931609105)
            ·
              refine ⟨1416399643034290448706829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1888532857379053931609105 1416399643034290448706829)
              ·
                refine ⟨531149866137858918265061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1416399643034290448706829 531149866137858918265061)
                ·
                  refine ⟨99590599900848547174699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 531149866137858918265061 99590599900848547174699)
                  ·
                    rfl

theorem cell22_872784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 3, 4].length) (baseStart_872784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_872784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_872784 prefixEnd_872784 := by exact prefixLift 872784
  have htrace : WordTrace (prefixWord ++ tailWord_872784) baseStart_872784 baseEnd_872784 := by
    simpa [prefixWord, tailWord_872784, baseEnd_872784] using wordTrace_append hprefix tailTrace_872784
  have hstable : (prefixWord ++ tailWord_872784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872784).length < 2 ^ (prefixWord ++ tailWord_872784).sum := by decide
  have hdescent : baseEnd_872784 < baseStart_872784 := by decide
  rcases family_descends (prefixWord ++ tailWord_872784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872799 : List Nat := [1, 1, 2, 3, 1, 2, 5, 2, 2, 3]
def baseStart_872799 : Nat := 118140960795 + 872799 * 2 ^ 59
def prefixEnd_872799 : Nat := 4983230072969 + 3 ^ 40 * 872799 * 2
def baseEnd_872799 : Nat := 298776934509090602399051

theorem tailTrace_872799 : CollatzResearch.WordTrace tailWord_872799 prefixEnd_872799 298776934509090602399051 := by
  unfold tailWord_872799
  simp only [CollatzResearch.WordTrace]
  refine ⟨31833594765005760046861451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21222396510003840031240967 31833594765005760046861451)
  ·
    refine ⟨47750392147508640070292177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31833594765005760046861451 47750392147508640070292177)
    ·
      refine ⟨35812794110631480052719133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47750392147508640070292177 35812794110631480052719133)
      ·
        refine ⟨13429797791486805019769675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35812794110631480052719133 13429797791486805019769675)
        ·
          refine ⟨20144696687230207529654513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13429797791486805019769675 20144696687230207529654513)
          ·
            refine ⟨15108522515422655647240885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20144696687230207529654513 15108522515422655647240885)
            ·
              refine ⟨1416423985820873966928833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15108522515422655647240885 1416423985820873966928833)
              ·
                refine ⟨1062317989365655475196625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1416423985820873966928833 1062317989365655475196625)
                ·
                  refine ⟨796738492024241606397469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1062317989365655475196625 796738492024241606397469)
                  ·
                    refine ⟨298776934509090602399051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 796738492024241606397469 298776934509090602399051)
                    ·
                      rfl

theorem cell22_872799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 2, 2, 3].length) (baseStart_872799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_872799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_872799 prefixEnd_872799 := by exact prefixLift 872799
  have htrace : WordTrace (prefixWord ++ tailWord_872799) baseStart_872799 baseEnd_872799 := by
    simpa [prefixWord, tailWord_872799, baseEnd_872799] using wordTrace_append hprefix tailTrace_872799
  have hstable : (prefixWord ++ tailWord_872799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872799).length < 2 ^ (prefixWord ++ tailWord_872799).sum := by decide
  have hdescent : baseEnd_872799 < baseStart_872799 := by decide
  rcases family_descends (prefixWord ++ tailWord_872799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872816 : List Nat := [2, 1, 1, 1, 4, 4, 3, 1, 2, 3]
def baseStart_872816 : Nat := 118140960795 + 872816 * 2 ^ 59
def prefixEnd_872816 : Nat := 4983230072969 + 3 ^ 40 * 872816 * 2
def baseEnd_872816 : Nat := 298782753956508224723999

theorem tailTrace_872816 : CollatzResearch.WordTrace tailWord_872816 prefixEnd_872816 298782753956508224723999 := by
  unfold tailWord_872816
  simp only [CollatzResearch.WordTrace]
  refine ⟨15917107402972085975115151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21222809870629447966820201 15917107402972085975115151)
  ·
    refine ⟨23875661104458128962672727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15917107402972085975115151 23875661104458128962672727)
    ·
      refine ⟨35813491656687193444009091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23875661104458128962672727 35813491656687193444009091)
      ·
        refine ⟨53720237485030790166013637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35813491656687193444009091 53720237485030790166013637)
        ·
          refine ⟨10072544528443273156127557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53720237485030790166013637 10072544528443273156127557)
          ·
            refine ⟨1888602099083113716773917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10072544528443273156127557 1888602099083113716773917)
            ·
              refine ⟨708225787156167643790219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1888602099083113716773917 708225787156167643790219)
              ·
                refine ⟨1062338680734251465685329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 708225787156167643790219 1062338680734251465685329)
                ·
                  refine ⟨796754010550688599263997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1062338680734251465685329 796754010550688599263997)
                  ·
                    refine ⟨298782753956508224723999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 796754010550688599263997 298782753956508224723999)
                    ·
                      rfl

theorem cell22_872816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 3, 1, 2, 3].length) (baseStart_872816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_872816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_872816 prefixEnd_872816 := by exact prefixLift 872816
  have htrace : WordTrace (prefixWord ++ tailWord_872816) baseStart_872816 baseEnd_872816 := by
    simpa [prefixWord, tailWord_872816, baseEnd_872816] using wordTrace_append hprefix tailTrace_872816
  have hstable : (prefixWord ++ tailWord_872816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872816).length < 2 ^ (prefixWord ++ tailWord_872816).sum := by decide
  have hdescent : baseEnd_872816 < baseStart_872816 := by decide
  rcases family_descends (prefixWord ++ tailWord_872816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872829 : List Nat := [1, 4, 1, 1, 2, 5, 2, 6]
def baseStart_872829 : Nat := 118140960795 + 872829 * 2 ^ 59
def prefixEnd_872829 : Nat := 4983230072969 + 3 ^ 40 * 872829 * 2
def baseEnd_872829 : Nat := 33198578235797836016551

theorem tailTrace_872829 : CollatzResearch.WordTrace tailWord_872829 prefixEnd_872829 33198578235797836016551 := by
  unfold tailWord_872829
  simp only [CollatzResearch.WordTrace]
  refine ⟨31834688954897075170453541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21223125969931383446969027 31834688954897075170453541)
  ·
    refine ⟨5969004179043201594460039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31834688954897075170453541 5969004179043201594460039)
    ·
      refine ⟨8953506268564802391690059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5969004179043201594460039 8953506268564802391690059)
      ·
        refine ⟨13430259402847203587535089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8953506268564802391690059 13430259402847203587535089)
        ·
          refine ⟨10072694552135402690651317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13430259402847203587535089 10072694552135402690651317)
          ·
            refine ⟨944315114262694002248561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10072694552135402690651317 944315114262694002248561)
            ·
              refine ⟨708236335697020501686421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 944315114262694002248561 708236335697020501686421)
              ·
                refine ⟨33198578235797836016551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 708236335697020501686421 33198578235797836016551)
                ·
                  rfl

theorem cell22_872829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 2, 6].length) (baseStart_872829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_872829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_872829 prefixEnd_872829 := by exact prefixLift 872829
  have htrace : WordTrace (prefixWord ++ tailWord_872829) baseStart_872829 baseEnd_872829 := by
    simpa [prefixWord, tailWord_872829, baseEnd_872829] using wordTrace_append hprefix tailTrace_872829
  have hstable : (prefixWord ++ tailWord_872829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872829).length < 2 ^ (prefixWord ++ tailWord_872829).sum := by decide
  have hdescent : baseEnd_872829 < baseStart_872829 := by decide
  rcases family_descends (prefixWord ++ tailWord_872829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872857 : List Nat := [1, 2, 1, 2, 1, 4, 2, 4, 5]
def baseStart_872857 : Nat := 118140960795 + 872857 * 2 ^ 59
def prefixEnd_872857 : Nat := 4983230072969 + 3 ^ 40 * 872857 * 2
def baseEnd_872857 : Nat := 99598929698132594816291

theorem tailTrace_872857 : CollatzResearch.WordTrace tailWord_872857 prefixEnd_872857 99598929698132594816291 := by
  unfold tailWord_872857
  simp only [CollatzResearch.WordTrace]
  refine ⟨31835710198795635952472825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21223806799197090634981883 31835710198795635952472825)
  ·
    refine ⟨23876782649096726964354619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31835710198795635952472825 23876782649096726964354619)
    ·
      refine ⟨35815173973645090446531929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23876782649096726964354619 35815173973645090446531929)
      ·
        refine ⟨26861380480233817834898947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35815173973645090446531929 26861380480233817834898947)
        ·
          refine ⟨40292070720350726752348421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26861380480233817834898947 40292070720350726752348421)
          ·
            refine ⟨7554763260065761266065329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40292070720350726752348421 7554763260065761266065329)
            ·
              refine ⟨5666072445049320949548997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7554763260065761266065329 5666072445049320949548997)
              ·
                refine ⟨1062388583446747678040437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5666072445049320949548997 1062388583446747678040437)
                ·
                  refine ⟨99598929698132594816291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1062388583446747678040437 99598929698132594816291)
                  ·
                    rfl

theorem cell22_872857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 4, 5].length) (baseStart_872857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_872857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_872857 prefixEnd_872857 := by exact prefixLift 872857
  have htrace : WordTrace (prefixWord ++ tailWord_872857) baseStart_872857 baseEnd_872857 := by
    simpa [prefixWord, tailWord_872857, baseEnd_872857] using wordTrace_append hprefix tailTrace_872857
  have hstable : (prefixWord ++ tailWord_872857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872857).length < 2 ^ (prefixWord ++ tailWord_872857).sum := by decide
  have hdescent : baseEnd_872857 < baseStart_872857 := by decide
  rcases family_descends (prefixWord ++ tailWord_872857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872964 : List Nat := [2, 3, 2, 3, 1, 2, 9]
def baseStart_872964 : Nat := 118140960795 + 872964 * 2 ^ 59
def prefixEnd_872964 : Nat := 4983230072969 + 3 ^ 40 * 872964 * 2
def baseEnd_872964 : Nat := 11067904347447598963835

theorem tailTrace_872964 : CollatzResearch.WordTrace tailWord_872964 prefixEnd_872964 11067904347447598963835 := by
  unfold tailWord_872964
  simp only [CollatzResearch.WordTrace]
  refine ⟨15919806404703996613308973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21226408539605328817745297 15919806404703996613308973)
  ·
    refine ⟨5969927401763998729990865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15919806404703996613308973 5969927401763998729990865)
    ·
      refine ⟨4477445551322999047493149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5969927401763998729990865 4477445551322999047493149)
      ·
        refine ⟨1679042081746124642809931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4477445551322999047493149 1679042081746124642809931)
        ·
          refine ⟨2518563122619186964214897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1679042081746124642809931 2518563122619186964214897)
          ·
            refine ⟨1888922341964390223161173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2518563122619186964214897 1888922341964390223161173)
            ·
              refine ⟨11067904347447598963835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1888922341964390223161173 11067904347447598963835)
              ·
                rfl

theorem cell22_872964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 9].length) (baseStart_872964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_872964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_872964 prefixEnd_872964 := by exact prefixLift 872964
  have htrace : WordTrace (prefixWord ++ tailWord_872964) baseStart_872964 baseEnd_872964 := by
    simpa [prefixWord, tailWord_872964, baseEnd_872964] using wordTrace_append hprefix tailTrace_872964
  have hstable : (prefixWord ++ tailWord_872964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872964).length < 2 ^ (prefixWord ++ tailWord_872964).sum := by decide
  have hdescent : baseEnd_872964 < baseStart_872964 := by decide
  rcases family_descends (prefixWord ++ tailWord_872964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872977 : List Nat := [1, 2, 2, 1, 1, 2, 2, 3, 2, 6]
def baseStart_872977 : Nat := 118140960795 + 872977 * 2 ^ 59
def prefixEnd_872977 : Nat := 4983230072969 + 3 ^ 40 * 872977 * 2
def baseEnd_872977 : Nat := 298837867546757471448505

theorem tailTrace_872977 : CollatzResearch.WordTrace tailWord_872977 prefixEnd_872977 298837867546757471448505 := by
  unfold tailWord_872977
  simp only [CollatzResearch.WordTrace]
  refine ⟨31840086958360896446841185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21226724638907264297894123 31840086958360896446841185)
  ·
    refine ⟨23880065218770672335130889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31840086958360896446841185 23880065218770672335130889)
    ·
      refine ⟨17910048914078004251348167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23880065218770672335130889 17910048914078004251348167)
      ·
        refine ⟨26865073371117006377022251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17910048914078004251348167 26865073371117006377022251)
        ·
          refine ⟨40297610056675509565533377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26865073371117006377022251 40297610056675509565533377)
          ·
            refine ⟨30223207542506632174150033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40297610056675509565533377 30223207542506632174150033)
            ·
              refine ⟨22667405656879974130612525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30223207542506632174150033 22667405656879974130612525)
              ·
                refine ⟨8500277121329990298979697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22667405656879974130612525 8500277121329990298979697)
                ·
                  refine ⟨6375207840997492724234773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8500277121329990298979697 6375207840997492724234773)
                  ·
                    refine ⟨298837867546757471448505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6375207840997492724234773 298837867546757471448505)
                    ·
                      rfl

theorem cell22_872977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 6].length) (baseStart_872977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_872977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_872977 prefixEnd_872977 := by exact prefixLift 872977
  have htrace : WordTrace (prefixWord ++ tailWord_872977) baseStart_872977 baseEnd_872977 := by
    simpa [prefixWord, tailWord_872977, baseEnd_872977] using wordTrace_append hprefix tailTrace_872977
  have hstable : (prefixWord ++ tailWord_872977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872977).length < 2 ^ (prefixWord ++ tailWord_872977).sum := by decide
  have hdescent : baseEnd_872977 < baseStart_872977 := by decide
  rcases family_descends (prefixWord ++ tailWord_872977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873030 : List Nat := [6, 1, 1, 1, 2, 1, 3, 1, 3, 3]
def baseStart_873030 : Nat := 118140960795 + 873030 * 2 ^ 59
def prefixEnd_873030 : Nat := 4983230072969 + 3 ^ 40 * 873030 * 2
def baseEnd_873030 : Nat := 298856010529882999873343

theorem tailTrace_873030 : CollatzResearch.WordTrace tailWord_873030 prefixEnd_873030 298856010529882999873343 := by
  unfold tailWord_873030
  simp only [CollatzResearch.WordTrace]
  refine ⟨995063125849027703078767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 21228013351445924332347029 995063125849027703078767)
  ·
    refine ⟨1492594688773541554618151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 995063125849027703078767 1492594688773541554618151)
    ·
      refine ⟨2238892033160312331927227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1492594688773541554618151 2238892033160312331927227)
      ·
        refine ⟨3358338049740468497890841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2238892033160312331927227 3358338049740468497890841)
        ·
          refine ⟨2518753537305351373418131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3358338049740468497890841 2518753537305351373418131)
          ·
            refine ⟨3778130305958027060127197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2518753537305351373418131 3778130305958027060127197)
            ·
              refine ⟨1416798864734260147547699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3778130305958027060127197 1416798864734260147547699)
              ·
                refine ⟨2125198297101390221321549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1416798864734260147547699 2125198297101390221321549)
                ·
                  refine ⟨796949361413021332995581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2125198297101390221321549 796949361413021332995581)
                  ·
                    refine ⟨298856010529882999873343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 796949361413021332995581 298856010529882999873343)
                    ·
                      rfl

theorem cell22_873030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_873030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_873030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_873030 prefixEnd_873030 := by exact prefixLift 873030
  have htrace : WordTrace (prefixWord ++ tailWord_873030) baseStart_873030 baseEnd_873030 := by
    simpa [prefixWord, tailWord_873030, baseEnd_873030] using wordTrace_append hprefix tailTrace_873030
  have hstable : (prefixWord ++ tailWord_873030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873030).length < 2 ^ (prefixWord ++ tailWord_873030).sum := by decide
  have hdescent : baseEnd_873030 < baseStart_873030 := by decide
  rcases family_descends (prefixWord ++ tailWord_873030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873056 : List Nat := [2, 1, 1, 3, 2, 1, 5, 2, 1, 4]
def baseStart_873056 : Nat := 118140960795 + 873056 * 2 ^ 59
def prefixEnd_873056 : Nat := 4983230072969 + 3 ^ 40 * 873056 * 2
def baseEnd_873056 : Nat := 298864910861227598723263

theorem tailTrace_873056 : CollatzResearch.WordTrace tailWord_873056 prefixEnd_873056 298864910861227598723263 := by
  unfold tailWord_873056
  simp only [CollatzResearch.WordTrace]
  refine ⟨15921484162537346469483511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21228645550049795292644681 15921484162537346469483511)
  ·
    refine ⟨23882226243806019704225267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15921484162537346469483511 23882226243806019704225267)
    ·
      refine ⟨35823339365709029556337901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23882226243806019704225267 35823339365709029556337901)
      ·
        refine ⟨13433752262140886083626713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35823339365709029556337901 13433752262140886083626713)
        ·
          refine ⟨10075314196605664562720035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13433752262140886083626713 10075314196605664562720035)
          ·
            refine ⟨15112971294908496844080053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10075314196605664562720035 15112971294908496844080053)
            ·
              refine ⟨1416841058897671579132505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15112971294908496844080053 1416841058897671579132505)
              ·
                refine ⟨1062630794173253684349379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1416841058897671579132505 1062630794173253684349379)
                ·
                  refine ⟨1593946191259880526524069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1062630794173253684349379 1593946191259880526524069)
                  ·
                    refine ⟨298864910861227598723263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1593946191259880526524069 298864910861227598723263)
                    ·
                      rfl

theorem cell22_873056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 2, 1, 4].length) (baseStart_873056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_873056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_873056 prefixEnd_873056 := by exact prefixLift 873056
  have htrace : WordTrace (prefixWord ++ tailWord_873056) baseStart_873056 baseEnd_873056 := by
    simpa [prefixWord, tailWord_873056, baseEnd_873056] using wordTrace_append hprefix tailTrace_873056
  have hstable : (prefixWord ++ tailWord_873056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873056).length < 2 ^ (prefixWord ++ tailWord_873056).sum := by decide
  have hdescent : baseEnd_873056 < baseStart_873056 := by decide
  rcases family_descends (prefixWord ++ tailWord_873056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873088 : List Nat := [2, 1, 1, 2, 1, 5, 4, 2, 4]
def baseStart_873088 : Nat := 118140960795 + 873088 * 2 ^ 59
def prefixEnd_873088 : Nat := 4983230072969 + 3 ^ 40 * 873088 * 2
def baseEnd_873088 : Nat := 99625288371730060641055

theorem tailTrace_873088 : CollatzResearch.WordTrace tailWord_873088 prefixEnd_873088 99625288371730060641055 := by
  unfold tailWord_873088
  simp only [CollatzResearch.WordTrace]
  refine ⟨15922067730479381202065959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21229423640639174936087945 15922067730479381202065959)
  ·
    refine ⟨23883101595719071803098939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15922067730479381202065959 23883101595719071803098939)
    ·
      refine ⟨35824652393578607704648409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23883101595719071803098939 35824652393578607704648409)
      ·
        refine ⟨26868489295183955778486307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35824652393578607704648409 26868489295183955778486307)
        ·
          refine ⟨40302733942775933667729461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26868489295183955778486307 40302733942775933667729461)
          ·
            refine ⟨3778381307135243781349637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40302733942775933667729461 3778381307135243781349637)
            ·
              refine ⟨708446495087858209003057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3778381307135243781349637 708446495087858209003057)
              ·
                refine ⟨531334871315893656752293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 708446495087858209003057 531334871315893656752293)
                ·
                  refine ⟨99625288371730060641055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 531334871315893656752293 99625288371730060641055)
                  ·
                    rfl

theorem cell22_873088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 4, 2, 4].length) (baseStart_873088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_873088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_873088 prefixEnd_873088 := by exact prefixLift 873088
  have htrace : WordTrace (prefixWord ++ tailWord_873088) baseStart_873088 baseEnd_873088 := by
    simpa [prefixWord, tailWord_873088, baseEnd_873088] using wordTrace_append hprefix tailTrace_873088
  have hstable : (prefixWord ++ tailWord_873088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873088).length < 2 ^ (prefixWord ++ tailWord_873088).sum := by decide
  have hdescent : baseEnd_873088 < baseStart_873088 := by decide
  rcases family_descends (prefixWord ++ tailWord_873088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873137 : List Nat := [1, 2, 2, 6, 1, 2, 1, 2, 2, 3]
def baseStart_873137 : Nat := 118140960795 + 873137 * 2 ^ 59
def prefixEnd_873137 : Nat := 4983230072969 + 3 ^ 40 * 873137 * 2
def baseEnd_873137 : Nat := 298892638816570387448015

theorem tailTrace_873137 : CollatzResearch.WordTrace tailWord_873137 prefixEnd_873137 298892638816570387448015 := by
  unfold tailWord_873137
  simp only [CollatzResearch.WordTrace]
  refine ⟨31845922637781243772665665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21230615091854162515110443 31845922637781243772665665)
  ·
    refine ⟨23884441978335932829499249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31845922637781243772665665 23884441978335932829499249)
    ·
      refine ⟨17913331483751949622124437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23884441978335932829499249 17913331483751949622124437)
      ·
        refine ⟨839687413300872638537083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 17913331483751949622124437 839687413300872638537083)
        ·
          refine ⟨1259531119951308957805625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 839687413300872638537083 1259531119951308957805625)
          ·
            refine ⟨944648339963481718354219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1259531119951308957805625 944648339963481718354219)
            ·
              refine ⟨1416972509945222577531329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 944648339963481718354219 1416972509945222577531329)
              ·
                refine ⟨1062729382458916933148497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1416972509945222577531329 1062729382458916933148497)
                ·
                  refine ⟨797047036844187699861373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1062729382458916933148497 797047036844187699861373)
                  ·
                    refine ⟨298892638816570387448015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 797047036844187699861373 298892638816570387448015)
                    ·
                      rfl

theorem cell22_873137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 2, 2, 3].length) (baseStart_873137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_873137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_873137 prefixEnd_873137 := by exact prefixLift 873137
  have htrace : WordTrace (prefixWord ++ tailWord_873137) baseStart_873137 baseEnd_873137 := by
    simpa [prefixWord, tailWord_873137, baseEnd_873137] using wordTrace_append hprefix tailTrace_873137
  have hstable : (prefixWord ++ tailWord_873137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873137).length < 2 ^ (prefixWord ++ tailWord_873137).sum := by decide
  have hdescent : baseEnd_873137 < baseStart_873137 := by decide
  rcases family_descends (prefixWord ++ tailWord_873137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873148 : List Nat := [2, 2, 2, 3, 1, 1, 4, 1, 3, 3]
def baseStart_873148 : Nat := 118140960795 + 873148 * 2 ^ 59
def prefixEnd_873148 : Nat := 4983230072969 + 3 ^ 40 * 873148 * 2
def baseEnd_873148 : Nat := 298896404341370025422981

theorem tailTrace_873148 : CollatzResearch.WordTrace tailWord_873148 prefixEnd_873148 298896404341370025422981 := by
  unfold tailWord_873148
  simp only [CollatzResearch.WordTrace]
  refine ⟨15923161920370696325658049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21230882560494261767544065 15923161920370696325658049)
  ·
    refine ⟨11942371440278022244243537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15923161920370696325658049 11942371440278022244243537)
    ·
      refine ⟨8956778580208516683182653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11942371440278022244243537 8956778580208516683182653)
      ·
        refine ⟨3358791967578193756193495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8956778580208516683182653 3358791967578193756193495)
        ·
          refine ⟨5038187951367290634290243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3358791967578193756193495 5038187951367290634290243)
          ·
            refine ⟨7557281927050935951435365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5038187951367290634290243 7557281927050935951435365)
            ·
              refine ⟨1416990361322050490894131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7557281927050935951435365 1416990361322050490894131)
              ·
                refine ⟨2125485541983075736341197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1416990361322050490894131 2125485541983075736341197)
                ·
                  refine ⟨797057078243653401127949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2125485541983075736341197 797057078243653401127949)
                  ·
                    refine ⟨298896404341370025422981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 797057078243653401127949 298896404341370025422981)
                    ·
                      rfl

theorem cell22_873148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 1, 3, 3].length) (baseStart_873148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_873148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_873148 prefixEnd_873148 := by exact prefixLift 873148
  have htrace : WordTrace (prefixWord ++ tailWord_873148) baseStart_873148 baseEnd_873148 := by
    simpa [prefixWord, tailWord_873148, baseEnd_873148] using wordTrace_append hprefix tailTrace_873148
  have hstable : (prefixWord ++ tailWord_873148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873148).length < 2 ^ (prefixWord ++ tailWord_873148).sum := by decide
  have hdescent : baseEnd_873148 < baseStart_873148 := by decide
  rcases family_descends (prefixWord ++ tailWord_873148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873159 : List Nat := [1, 1, 4, 1, 1, 1, 2, 3, 1, 7]
def baseStart_873159 : Nat := 118140960795 + 873159 * 2 ^ 59
def prefixEnd_873159 : Nat := 4983230072969 + 3 ^ 40 * 873159 * 2
def baseEnd_873159 : Nat := 298900169866169663397947

theorem tailTrace_873159 : CollatzResearch.WordTrace tailWord_873159 prefixEnd_873159 298900169866169663397947 := by
  unfold tailWord_873159
  simp only [CollatzResearch.WordTrace]
  refine ⟨31846725043701541529966531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21231150029134361019977687 31846725043701541529966531)
  ·
    refine ⟨47770087565552312294949797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31846725043701541529966531 47770087565552312294949797)
    ·
      refine ⟨8956891418541058555303087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47770087565552312294949797 8956891418541058555303087)
      ·
        refine ⟨13435337127811587832954631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8956891418541058555303087 13435337127811587832954631)
        ·
          refine ⟨20153005691717381749431947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13435337127811587832954631 20153005691717381749431947)
          ·
            refine ⟨30229508537576072624147921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20153005691717381749431947 30229508537576072624147921)
            ·
              refine ⟨22672131403182054468110941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30229508537576072624147921 22672131403182054468110941)
              ·
                refine ⟨8502049276193270425541603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22672131403182054468110941 8502049276193270425541603)
                ·
                  refine ⟨12753073914289905638312405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8502049276193270425541603 12753073914289905638312405)
                  ·
                    refine ⟨298900169866169663397947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12753073914289905638312405 298900169866169663397947)
                    ·
                      rfl

theorem cell22_873159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 7].length) (baseStart_873159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_873159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_873159 prefixEnd_873159 := by exact prefixLift 873159
  have htrace : WordTrace (prefixWord ++ tailWord_873159) baseStart_873159 baseEnd_873159 := by
    simpa [prefixWord, tailWord_873159, baseEnd_873159] using wordTrace_append hprefix tailTrace_873159
  have hstable : (prefixWord ++ tailWord_873159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873159).length < 2 ^ (prefixWord ++ tailWord_873159).sum := by decide
  have hdescent : baseEnd_873159 < baseStart_873159 := by decide
  rcases family_descends (prefixWord ++ tailWord_873159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873283 : List Nat := [1, 1, 1, 3, 1, 4, 3, 2, 3, 3]
def baseStart_873283 : Nat := 118140960795 + 873283 * 2 ^ 59
def prefixEnd_873283 : Nat := 4983230072969 + 3 ^ 40 * 873283 * 2
def baseEnd_873283 : Nat := 298942617600274673297567

theorem tailTrace_873283 : CollatzResearch.WordTrace tailWord_873283 prefixEnd_873283 298942617600274673297567 := by
  unfold tailWord_873283
  simp only [CollatzResearch.WordTrace]
  refine ⟨31851247695252310707480503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21234165130168207138320335 31851247695252310707480503)
  ·
    refine ⟨47776871542878466061220755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31851247695252310707480503 47776871542878466061220755)
    ·
      refine ⟨71665307314317699091831133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47776871542878466061220755 71665307314317699091831133)
      ·
        refine ⟨26874490242869137159436675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71665307314317699091831133 26874490242869137159436675)
        ·
          refine ⟨40311735364303705739155013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26874490242869137159436675 40311735364303705739155013)
          ·
            refine ⟨7558450380806944826091565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40311735364303705739155013 7558450380806944826091565)
            ·
              refine ⟨2834418892802604309784337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7558450380806944826091565 2834418892802604309784337)
              ·
                refine ⟨2125814169601953232338253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2834418892802604309784337 2125814169601953232338253)
                ·
                  refine ⟨797180313600732462126845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2125814169601953232338253 797180313600732462126845)
                  ·
                    refine ⟨298942617600274673297567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 797180313600732462126845 298942617600274673297567)
                    ·
                      rfl

theorem cell22_873283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 2, 3, 3].length) (baseStart_873283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_873283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_873283 prefixEnd_873283 := by exact prefixLift 873283
  have htrace : WordTrace (prefixWord ++ tailWord_873283) baseStart_873283 baseEnd_873283 := by
    simpa [prefixWord, tailWord_873283, baseEnd_873283] using wordTrace_append hprefix tailTrace_873283
  have hstable : (prefixWord ++ tailWord_873283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873283).length < 2 ^ (prefixWord ++ tailWord_873283).sum := by decide
  have hdescent : baseEnd_873283 < baseStart_873283 := by decide
  rcases family_descends (prefixWord ++ tailWord_873283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873311 : List Nat := [1, 1, 2, 3, 1, 3, 1, 1, 4, 5]
def baseStart_873311 : Nat := 118140960795 + 873311 * 2 ^ 59
def prefixEnd_873311 : Nat := 4983230072969 + 3 ^ 40 * 873311 * 2
def baseEnd_873311 : Nat := 298952202572491933597481

theorem tailTrace_873311 : CollatzResearch.WordTrace tailWord_873311 prefixEnd_873311 298952202572491933597481 := by
  unfold tailWord_873311
  simp only [CollatzResearch.WordTrace]
  refine ⟨31852268939150871489499787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21234845959433914326333191 31852268939150871489499787)
  ·
    refine ⟨47778403408726307234249681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31852268939150871489499787 47778403408726307234249681)
    ·
      refine ⟨35833802556544730425687261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47778403408726307234249681 35833802556544730425687261)
      ·
        refine ⟨13437675958704273909632723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35833802556544730425687261 13437675958704273909632723)
        ·
          refine ⟨20156513938056410864449085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13437675958704273909632723 20156513938056410864449085)
          ·
            refine ⟨7558692726771154074168407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20156513938056410864449085 7558692726771154074168407)
            ·
              refine ⟨11338039090156731111252611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7558692726771154074168407 11338039090156731111252611)
              ·
                refine ⟨17007058635235096666878917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11338039090156731111252611 17007058635235096666878917)
                ·
                  refine ⟨3188823494106580625039797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17007058635235096666878917 3188823494106580625039797)
                  ·
                    refine ⟨298952202572491933597481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3188823494106580625039797 298952202572491933597481)
                    ·
                      rfl

theorem cell22_873311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 4, 5].length) (baseStart_873311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_873311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_873311 prefixEnd_873311 := by exact prefixLift 873311
  have htrace : WordTrace (prefixWord ++ tailWord_873311) baseStart_873311 baseEnd_873311 := by
    simpa [prefixWord, tailWord_873311, baseEnd_873311] using wordTrace_append hprefix tailTrace_873311
  have hstable : (prefixWord ++ tailWord_873311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873311).length < 2 ^ (prefixWord ++ tailWord_873311).sum := by decide
  have hdescent : baseEnd_873311 < baseStart_873311 := by decide
  rcases family_descends (prefixWord ++ tailWord_873311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873343 : List Nat := [1, 1, 2, 2, 1, 1, 5, 4, 1, 4]
def baseStart_873343 : Nat := 118140960795 + 873343 * 2 ^ 59
def prefixEnd_873343 : Nat := 4983230072969 + 3 ^ 40 * 873343 * 2
def baseEnd_873343 : Nat := 298963156826454516797383

theorem tailTrace_873343 : CollatzResearch.WordTrace tailWord_873343 prefixEnd_873343 298963156826454516797383 := by
  unfold tailWord_873343
  simp only [CollatzResearch.WordTrace]
  refine ⟨31853436075034940954664683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21235624050023293969776455 31853436075034940954664683)
  ·
    refine ⟨47780154112552411431997025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31853436075034940954664683 47780154112552411431997025)
    ·
      refine ⟨35835115584414308573997769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47780154112552411431997025 35835115584414308573997769)
      ·
        refine ⟨26876336688310731430498327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35835115584414308573997769 26876336688310731430498327)
        ·
          refine ⟨40314505032466097145747491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26876336688310731430498327 40314505032466097145747491)
          ·
            refine ⟨60471757548699145718621237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40314505032466097145747491 60471757548699145718621237)
            ·
              refine ⟨5669227270190544911120741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60471757548699145718621237 5669227270190544911120741)
              ·
                refine ⟨1062980113160727170835139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5669227270190544911120741 1062980113160727170835139)
                ·
                  refine ⟨1594470169741090756252709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1062980113160727170835139 1594470169741090756252709)
                  ·
                    refine ⟨298963156826454516797383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1594470169741090756252709 298963156826454516797383)
                    ·
                      rfl

theorem cell22_873343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 4, 1, 4].length) (baseStart_873343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_873343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_873343 prefixEnd_873343 := by exact prefixLift 873343
  have htrace : WordTrace (prefixWord ++ tailWord_873343) baseStart_873343 baseEnd_873343 := by
    simpa [prefixWord, tailWord_873343, baseEnd_873343] using wordTrace_append hprefix tailTrace_873343
  have hstable : (prefixWord ++ tailWord_873343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873343).length < 2 ^ (prefixWord ++ tailWord_873343).sum := by decide
  have hdescent : baseEnd_873343 < baseStart_873343 := by decide
  rcases family_descends (prefixWord ++ tailWord_873343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873375 : List Nat := [1, 1, 2, 5, 2, 3, 1, 1, 6]
def baseStart_873375 : Nat := 118140960795 + 873375 * 2 ^ 59
def prefixEnd_873375 : Nat := 4983230072969 + 3 ^ 40 * 873375 * 2
def baseEnd_873375 : Nat := 99658037026805699999095

theorem tailTrace_873375 : CollatzResearch.WordTrace tailWord_873375 prefixEnd_873375 99658037026805699999095 := by
  unfold tailWord_873375
  simp only [CollatzResearch.WordTrace]
  refine ⟨31854603210919010419829579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21236402140612673613219719 31854603210919010419829579)
  ·
    refine ⟨47781904816378515629744369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31854603210919010419829579 47781904816378515629744369)
    ·
      refine ⟨35836428612283886722308277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47781904816378515629744369 35836428612283886722308277)
      ·
        refine ⟨3359665182401614380216401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35836428612283886722308277 3359665182401614380216401)
        ·
          refine ⟨2519748886801210785162301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3359665182401614380216401 2519748886801210785162301)
          ·
            refine ⟨944905832550454044435863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2519748886801210785162301 944905832550454044435863)
            ·
              refine ⟨1417358748825681066653795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 944905832550454044435863 1417358748825681066653795)
              ·
                refine ⟨2126038123238521599980693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1417358748825681066653795 2126038123238521599980693)
                ·
                  refine ⟨99658037026805699999095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2126038123238521599980693 99658037026805699999095)
                  ·
                    rfl

theorem cell22_873375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 1, 6].length) (baseStart_873375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_873375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_873375 prefixEnd_873375 := by exact prefixLift 873375
  have htrace : WordTrace (prefixWord ++ tailWord_873375) baseStart_873375 baseEnd_873375 := by
    simpa [prefixWord, tailWord_873375, baseEnd_873375] using wordTrace_append hprefix tailTrace_873375
  have hstable : (prefixWord ++ tailWord_873375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873375).length < 2 ^ (prefixWord ++ tailWord_873375).sum := by decide
  have hdescent : baseEnd_873375 < baseStart_873375 := by decide
  rcases family_descends (prefixWord ++ tailWord_873375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873433 : List Nat := [1, 2, 1, 2, 5, 1, 1, 1, 2, 6]
def baseStart_873433 : Nat := 118140960795 + 873433 * 2 ^ 59
def prefixEnd_873433 : Nat := 4983230072969 + 3 ^ 40 * 873433 * 2
def baseEnd_873433 : Nat := 298993965665724282047107

theorem tailTrace_873433 : CollatzResearch.WordTrace tailWord_873433 prefixEnd_873433 298993965665724282047107 := by
  unfold tailWord_873433
  simp only [CollatzResearch.WordTrace]
  refine ⟨31856718644708886325440953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21237812429805924216960635 31856718644708886325440953)
  ·
    refine ⟨23892538983531664744080715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31856718644708886325440953 23892538983531664744080715)
    ·
      refine ⟨35838808475297497116121073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23892538983531664744080715 35838808475297497116121073)
      ·
        refine ⟨26879106356473122837090805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35838808475297497116121073 26879106356473122837090805)
        ·
          refine ⟨2519916220919355265977263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26879106356473122837090805 2519916220919355265977263)
          ·
            refine ⟨3779874331379032898965895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2519916220919355265977263 3779874331379032898965895)
            ·
              refine ⟨5669811497068549348448843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3779874331379032898965895 5669811497068549348448843)
              ·
                refine ⟨8504717245602824022673265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5669811497068549348448843 8504717245602824022673265)
                ·
                  refine ⟨6378537934202118017004949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8504717245602824022673265 6378537934202118017004949)
                  ·
                    refine ⟨298993965665724282047107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6378537934202118017004949 298993965665724282047107)
                    ·
                      rfl

theorem cell22_873433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 2, 6].length) (baseStart_873433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_873433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_873433 prefixEnd_873433 := by exact prefixLift 873433
  have htrace : WordTrace (prefixWord ++ tailWord_873433) baseStart_873433 baseEnd_873433 := by
    simpa [prefixWord, tailWord_873433, baseEnd_873433] using wordTrace_append hprefix tailTrace_873433
  have hstable : (prefixWord ++ tailWord_873433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873433).length < 2 ^ (prefixWord ++ tailWord_873433).sum := by decide
  have hdescent : baseEnd_873433 < baseStart_873433 := by decide
  rcases family_descends (prefixWord ++ tailWord_873433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873482 : List Nat := [3, 1, 2, 2, 3, 3, 1, 2, 5]
def baseStart_873482 : Nat := 118140960795 + 873482 * 2 ^ 59
def prefixEnd_873482 : Nat := 4983230072969 + 3 ^ 40 * 873482 * 2
def baseEnd_873482 : Nat := 99670246455701495857319

theorem tailTrace_873482 : CollatzResearch.WordTrace tailWord_873482 prefixEnd_873482 99670246455701495857319 := by
  unfold tailWord_873482
  simp only [CollatzResearch.WordTrace]
  refine ⟨7964626455382841923493675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21239003881020911795983133 7964626455382841923493675)
  ·
    refine ⟨11946939683074262885240513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7964626455382841923493675 11946939683074262885240513)
    ·
      refine ⟨8960204762305697163930385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11946939683074262885240513 8960204762305697163930385)
      ·
        refine ⟨6720153571729272872947789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8960204762305697163930385 6720153571729272872947789)
        ·
          refine ⟨2520057589398477327355421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6720153571729272872947789 2520057589398477327355421)
          ·
            refine ⟨945021596024428997758283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2520057589398477327355421 945021596024428997758283)
            ·
              refine ⟨1417532394036643496637425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 945021596024428997758283 1417532394036643496637425)
              ·
                refine ⟨1063149295527482622478069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1417532394036643496637425 1063149295527482622478069)
                ·
                  refine ⟨99670246455701495857319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1063149295527482622478069 99670246455701495857319)
                  ·
                    rfl

theorem cell22_873482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 2, 5].length) (baseStart_873482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_873482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_873482 prefixEnd_873482 := by exact prefixLift 873482
  have htrace : WordTrace (prefixWord ++ tailWord_873482) baseStart_873482 baseEnd_873482 := by
    simpa [prefixWord, tailWord_873482, baseEnd_873482] using wordTrace_append hprefix tailTrace_873482
  have hstable : (prefixWord ++ tailWord_873482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873482).length < 2 ^ (prefixWord ++ tailWord_873482).sum := by decide
  have hdescent : baseEnd_873482 < baseStart_873482 := by decide
  rcases family_descends (prefixWord ++ tailWord_873482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873600 : List Nat := [2, 1, 1, 2, 1, 3, 3, 4, 5]
def baseStart_873600 : Nat := 118140960795 + 873600 * 2 ^ 59
def prefixEnd_873600 : Nat := 4983230072969 + 3 ^ 40 * 873600 * 2
def baseEnd_873600 : Nat := 99683711059530504373865

theorem tailTrace_873600 : CollatzResearch.WordTrace tailWord_873600 prefixEnd_873600 99683711059530504373865 := by
  unfold tailWord_873600
  simp only [CollatzResearch.WordTrace]
  refine ⟨15931404817551936923385127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21241873090069249231180169 15931404817551936923385127)
  ·
    refine ⟨23897107226327905385077691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15931404817551936923385127 23897107226327905385077691)
    ·
      refine ⟨35845660839491858077616537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23897107226327905385077691 35845660839491858077616537)
      ·
        refine ⟨26884245629618893558212403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35845660839491858077616537 26884245629618893558212403)
        ·
          refine ⟨40326368444428340337318605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26884245629618893558212403 40326368444428340337318605)
          ·
            refine ⟨15122388166660627626494477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40326368444428340337318605 15122388166660627626494477)
            ·
              refine ⟨5670895562497735359935429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15122388166660627626494477 5670895562497735359935429)
              ·
                refine ⟨1063292917968325379987893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5670895562497735359935429 1063292917968325379987893)
                ·
                  refine ⟨99683711059530504373865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1063292917968325379987893 99683711059530504373865)
                  ·
                    rfl

theorem cell22_873600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 4, 5].length) (baseStart_873600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_873600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_873600 prefixEnd_873600 := by exact prefixLift 873600
  have htrace : WordTrace (prefixWord ++ tailWord_873600) baseStart_873600 baseEnd_873600 := by
    simpa [prefixWord, tailWord_873600, baseEnd_873600] using wordTrace_append hprefix tailTrace_873600
  have hstable : (prefixWord ++ tailWord_873600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873600).length < 2 ^ (prefixWord ++ tailWord_873600).sum := by decide
  have hdescent : baseEnd_873600 < baseStart_873600 := by decide
  rcases family_descends (prefixWord ++ tailWord_873600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873662 : List Nat := [4, 2, 1, 1, 3, 1, 1, 3, 6]
def baseStart_873662 : Nat := 118140960795 + 873662 * 2 ^ 59
def prefixEnd_873662 : Nat := 4983230072969 + 3 ^ 40 * 873662 * 2
def baseEnd_873662 : Nat := 99690785681881339357135

theorem tailTrace_873662 : CollatzResearch.WordTrace tailWord_873662 prefixEnd_873662 99690785681881339357135 := by
  unfold tailWord_873662
  simp only [CollatzResearch.WordTrace]
  refine ⟨3983133870109907304440905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21243380640586172290351493 3983133870109907304440905)
  ·
    refine ⟨2987350402582430478330679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3983133870109907304440905 2987350402582430478330679)
    ·
      refine ⟨4481025603873645717496019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2987350402582430478330679 4481025603873645717496019)
      ·
        refine ⟨6721538405810468576244029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4481025603873645717496019 6721538405810468576244029)
        ·
          refine ⟨2520576902178925716091511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6721538405810468576244029 2520576902178925716091511)
          ·
            refine ⟨3780865353268388574137267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2520576902178925716091511 3780865353268388574137267)
            ·
              refine ⟨5671298029902582861205901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3780865353268388574137267 5671298029902582861205901)
              ·
                refine ⟨2126736761213468572952213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5671298029902582861205901 2126736761213468572952213)
                ·
                  refine ⟨99690785681881339357135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2126736761213468572952213 99690785681881339357135)
                  ·
                    rfl

theorem cell22_873662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 3, 6].length) (baseStart_873662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_873662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_873662 prefixEnd_873662 := by exact prefixLift 873662
  have htrace : WordTrace (prefixWord ++ tailWord_873662) baseStart_873662 baseEnd_873662 := by
    simpa [prefixWord, tailWord_873662, baseEnd_873662] using wordTrace_append hprefix tailTrace_873662
  have hstable : (prefixWord ++ tailWord_873662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873662).length < 2 ^ (prefixWord ++ tailWord_873662).sum := by decide
  have hdescent : baseEnd_873662 < baseStart_873662 := by decide
  rcases family_descends (prefixWord ++ tailWord_873662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873675 : List Nat := [1, 1, 1, 1, 3, 2, 2, 1, 6, 4]
def baseStart_873675 : Nat := 118140960795 + 873675 * 2 ^ 59
def prefixEnd_873675 : Nat := 4983230072969 + 3 ^ 40 * 873675 * 2
def baseEnd_873675 : Nat := 299076807211316317496365

theorem tailTrace_873675 : CollatzResearch.WordTrace tailWord_873675 prefixEnd_873675 299076807211316317496365 := by
  unfold tailWord_873675
  simp only [CollatzResearch.WordTrace]
  refine ⟨31865545109832161655750479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21243696739888107770500319 31865545109832161655750479)
  ·
    refine ⟨47798317664748242483625719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31865545109832161655750479 47798317664748242483625719)
    ·
      refine ⟨71697476497122363725438579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47798317664748242483625719 71697476497122363725438579)
      ·
        refine ⟨107546214745683545588157869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71697476497122363725438579 107546214745683545588157869)
        ·
          refine ⟨40329830529631329595559201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107546214745683545588157869 40329830529631329595559201)
          ·
            refine ⟨30247372897223497196669401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40329830529631329595559201 30247372897223497196669401)
            ·
              refine ⟨22685529672917622897502051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30247372897223497196669401 22685529672917622897502051)
              ·
                refine ⟨34028294509376434346253077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22685529672917622897502051 34028294509376434346253077)
                ·
                  refine ⟨1595076305127020359980613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 34028294509376434346253077 1595076305127020359980613)
                  ·
                    refine ⟨299076807211316317496365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1595076305127020359980613 299076807211316317496365)
                    ·
                      rfl

theorem cell22_873675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 6, 4].length) (baseStart_873675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_873675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_873675 prefixEnd_873675 := by exact prefixLift 873675
  have htrace : WordTrace (prefixWord ++ tailWord_873675) baseStart_873675 baseEnd_873675 := by
    simpa [prefixWord, tailWord_873675, baseEnd_873675] using wordTrace_append hprefix tailTrace_873675
  have hstable : (prefixWord ++ tailWord_873675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873675).length < 2 ^ (prefixWord ++ tailWord_873675).sum := by decide
  have hdescent : baseEnd_873675 < baseStart_873675 := by decide
  rcases family_descends (prefixWord ++ tailWord_873675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873709 : List Nat := [1, 5, 1, 2, 2, 2, 1, 2, 2, 4]
def baseStart_873709 : Nat := 118140960795 + 873709 * 2 ^ 59
def prefixEnd_873709 : Nat := 4983230072969 + 3 ^ 40 * 873709 * 2
def baseEnd_873709 : Nat := 299088446106151562146261

theorem tailTrace_873709 : CollatzResearch.WordTrace tailWord_873709 prefixEnd_873709 299088446106151562146261 := by
  unfold tailWord_873709
  simp only [CollatzResearch.WordTrace]
  refine ⟨31866785191708985462488181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21244523461139323641658787 31866785191708985462488181)
  ·
    refine ⟨2987511111722717387108267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31866785191708985462488181 2987511111722717387108267)
    ·
      refine ⟨4481266667584076080662401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2987511111722717387108267 4481266667584076080662401)
      ·
        refine ⟨3360950000688057060496801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4481266667584076080662401 3360950000688057060496801)
        ·
          refine ⟨2520712500516042795372601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3360950000688057060496801 2520712500516042795372601)
          ·
            refine ⟨1890534375387032096529451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2520712500516042795372601 1890534375387032096529451)
            ·
              refine ⟨2835801563080548144794177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1890534375387032096529451 2835801563080548144794177)
              ·
                refine ⟨2126851172310411108595633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2835801563080548144794177 2126851172310411108595633)
                ·
                  refine ⟨1595138379232808331446725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2126851172310411108595633 1595138379232808331446725)
                  ·
                    refine ⟨299088446106151562146261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1595138379232808331446725 299088446106151562146261)
                    ·
                      rfl

theorem cell22_873709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_873709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_873709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_873709 prefixEnd_873709 := by exact prefixLift 873709
  have htrace : WordTrace (prefixWord ++ tailWord_873709) baseStart_873709 baseEnd_873709 := by
    simpa [prefixWord, tailWord_873709, baseEnd_873709] using wordTrace_append hprefix tailTrace_873709
  have hstable : (prefixWord ++ tailWord_873709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873709).length < 2 ^ (prefixWord ++ tailWord_873709).sum := by decide
  have hdescent : baseEnd_873709 < baseStart_873709 := by decide
  rcases family_descends (prefixWord ++ tailWord_873709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873829 : List Nat := [1, 3, 1, 3, 1, 2, 3, 1, 4, 3]
def baseStart_873829 : Nat := 118140960795 + 873829 * 2 ^ 59
def prefixEnd_873829 : Nat := 4983230072969 + 3 ^ 40 * 873829 * 2
def baseEnd_873829 : Nat := 299129524558511249145893

theorem tailTrace_873829 : CollatzResearch.WordTrace tailWord_873829 prefixEnd_873829 299129524558511249145893 := by
  unfold tailWord_873829
  simp only [CollatzResearch.WordTrace]
  refine ⟨31871161951274245956856541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21247441300849497304571027 31871161951274245956856541)
  ·
    refine ⟨11951685731727842233821203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31871161951274245956856541 11951685731727842233821203)
    ·
      refine ⟨17927528597591763350731805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11951685731727842233821203 17927528597591763350731805)
      ·
        refine ⟨6722823224096911256524427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17927528597591763350731805 6722823224096911256524427)
        ·
          refine ⟨10084234836145366884786641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6722823224096911256524427 10084234836145366884786641)
          ·
            refine ⟨7563176127109025163589981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10084234836145366884786641 7563176127109025163589981)
            ·
              refine ⟨2836191047665884436346243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7563176127109025163589981 2836191047665884436346243)
              ·
                refine ⟨4254286571498826654519365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2836191047665884436346243 4254286571498826654519365)
                ·
                  refine ⟨797678732156029997722381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4254286571498826654519365 797678732156029997722381)
                  ·
                    refine ⟨299129524558511249145893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 797678732156029997722381 299129524558511249145893)
                    ·
                      rfl

theorem cell22_873829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 1, 4, 3].length) (baseStart_873829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_873829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_873829 prefixEnd_873829 := by exact prefixLift 873829
  have htrace : WordTrace (prefixWord ++ tailWord_873829) baseStart_873829 baseEnd_873829 := by
    simpa [prefixWord, tailWord_873829, baseEnd_873829] using wordTrace_append hprefix tailTrace_873829
  have hstable : (prefixWord ++ tailWord_873829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873829).length < 2 ^ (prefixWord ++ tailWord_873829).sum := by decide
  have hdescent : baseEnd_873829 < baseStart_873829 := by decide
  rcases family_descends (prefixWord ++ tailWord_873829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873842 : List Nat := [3, 2, 1, 2, 1, 2, 2, 9]
def baseStart_873842 : Nat := 118140960795 + 873842 * 2 ^ 59
def prefixEnd_873842 : Nat := 4983230072969 + 3 ^ 40 * 873842 * 2
def baseEnd_873842 : Nat := 33237108302687060952317

theorem tailTrace_873842 : CollatzResearch.WordTrace tailWord_873842 prefixEnd_873842 33237108302687060952317 := by
  unfold tailWord_873842
  simp only [CollatzResearch.WordTrace]
  refine ⟨7967909025056787294269945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21247757400151432784719853 7967909025056787294269945)
  ·
    refine ⟨5975931768792590470702459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7967909025056787294269945 5975931768792590470702459)
    ·
      refine ⟨8963897653188885706053689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5975931768792590470702459 8963897653188885706053689)
      ·
        refine ⟨6722923239891664279540267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8963897653188885706053689 6722923239891664279540267)
        ·
          refine ⟨10084384859837496419310401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6722923239891664279540267 10084384859837496419310401)
          ·
            refine ⟨7563288644878122314482801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10084384859837496419310401 7563288644878122314482801)
            ·
              refine ⟨5672466483658591735862101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7563288644878122314482801 5672466483658591735862101)
              ·
                refine ⟨33237108302687060952317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5672466483658591735862101 33237108302687060952317)
                ·
                  rfl

theorem cell22_873842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 9].length) (baseStart_873842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_873842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_873842 prefixEnd_873842 := by exact prefixLift 873842
  have htrace : WordTrace (prefixWord ++ tailWord_873842) baseStart_873842 baseEnd_873842 := by
    simpa [prefixWord, tailWord_873842, baseEnd_873842] using wordTrace_append hprefix tailTrace_873842
  have hstable : (prefixWord ++ tailWord_873842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873842).length < 2 ^ (prefixWord ++ tailWord_873842).sum := by decide
  have hdescent : baseEnd_873842 < baseStart_873842 := by decide
  rcases family_descends (prefixWord ++ tailWord_873842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873859 : List Nat := [1, 1, 1, 3, 5, 1, 4, 6]
def baseStart_873859 : Nat := 118140960795 + 873859 * 2 ^ 59
def prefixEnd_873859 : Nat := 4983230072969 + 3 ^ 40 * 873859 * 2
def baseEnd_873859 : Nat := 33237754907955685655089

theorem tailTrace_873859 : CollatzResearch.WordTrace tailWord_873859 prefixEnd_873859 33237754907955685655089 := by
  unfold tailWord_873859
  simp only [CollatzResearch.WordTrace]
  refine ⟨31872256141165561080448631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21248170760777040720299087 31872256141165561080448631)
  ·
    refine ⟨47808384211748341620672947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31872256141165561080448631 47808384211748341620672947)
    ·
      refine ⟨71712576317622512431009421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47808384211748341620672947 71712576317622512431009421)
      ·
        refine ⟨26892216119108442161628533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71712576317622512431009421 26892216119108442161628533)
        ·
          refine ⟨2521145261166416452652675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26892216119108442161628533 2521145261166416452652675)
          ·
            refine ⟨3781717891749624678979013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2521145261166416452652675 3781717891749624678979013)
            ·
              refine ⟨709072104703054627308565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3781717891749624678979013 709072104703054627308565)
              ·
                refine ⟨33237754907955685655089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 709072104703054627308565 33237754907955685655089)
                ·
                  rfl

theorem cell22_873859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 4, 6].length) (baseStart_873859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_873859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_873859 prefixEnd_873859 := by exact prefixLift 873859
  have htrace : WordTrace (prefixWord ++ tailWord_873859) baseStart_873859 baseEnd_873859 := by
    simpa [prefixWord, tailWord_873859, baseEnd_873859] using wordTrace_append hprefix tailTrace_873859
  have hstable : (prefixWord ++ tailWord_873859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873859).length < 2 ^ (prefixWord ++ tailWord_873859).sum := by decide
  have hdescent : baseEnd_873859 < baseStart_873859 := by decide
  rcases family_descends (prefixWord ++ tailWord_873859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873942 : List Nat := [5, 2, 1, 1, 1, 2, 4, 2, 1, 3]
def baseStart_873942 : Nat := 118140960795 + 873942 * 2 ^ 59
def prefixEnd_873942 : Nat := 4983230072969 + 3 ^ 40 * 873942 * 2
def baseEnd_873942 : Nat := 299168206767816621070547

theorem tailTrace_873942 : CollatzResearch.WordTrace tailWord_873942 prefixEnd_873942 299168206767816621070547 := by
  unfold tailWord_873942
  simp only [CollatzResearch.WordTrace]
  refine ⟨1992205212491554140982505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21250188933243244170480053 1992205212491554140982505)
  ·
    refine ⟨1494153909368665605736879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1992205212491554140982505 1494153909368665605736879)
    ·
      refine ⟨2241230864052998408605319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1494153909368665605736879 2241230864052998408605319)
      ·
        refine ⟨3361846296079497612907979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2241230864052998408605319 3361846296079497612907979)
        ·
          refine ⟨5042769444119246419361969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3361846296079497612907979 5042769444119246419361969)
          ·
            refine ⟨3782077083089434814521477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5042769444119246419361969 3782077083089434814521477)
            ·
              refine ⟨709139453079269027722777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3782077083089434814521477 709139453079269027722777)
              ·
                refine ⟨531854589809451770792083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 709139453079269027722777 531854589809451770792083)
                ·
                  refine ⟨797781884714177656188125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 531854589809451770792083 797781884714177656188125)
                  ·
                    refine ⟨299168206767816621070547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 797781884714177656188125 299168206767816621070547)
                    ·
                      rfl

theorem cell22_873942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_873942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_873942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_873942 prefixEnd_873942 := by exact prefixLift 873942
  have htrace : WordTrace (prefixWord ++ tailWord_873942) baseStart_873942 baseEnd_873942 := by
    simpa [prefixWord, tailWord_873942, baseEnd_873942] using wordTrace_append hprefix tailTrace_873942
  have hstable : (prefixWord ++ tailWord_873942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873942).length < 2 ^ (prefixWord ++ tailWord_873942).sum := by decide
  have hdescent : baseEnd_873942 < baseStart_873942 := by decide
  rcases family_descends (prefixWord ++ tailWord_873942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873985 : List Nat := [1, 2, 4, 1, 4, 2, 2, 1, 1, 4]
def baseStart_873985 : Nat := 118140960795 + 873985 * 2 ^ 59
def prefixEnd_873985 : Nat := 4983230072969 + 3 ^ 40 * 873985 * 2
def baseEnd_873985 : Nat := 299182926546578842245415

theorem tailTrace_873985 : CollatzResearch.WordTrace tailWord_873985 prefixEnd_873985 299182926546578842245415 := by
  unfold tailWord_873985
  simp only [CollatzResearch.WordTrace]
  refine ⟨31876851738709084599535409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21251234492472723066356939 31876851738709084599535409)
  ·
    refine ⟨23907638804031813449651557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31876851738709084599535409 23907638804031813449651557)
    ·
      refine ⟨4482682275755965021809667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23907638804031813449651557 4482682275755965021809667)
      ·
        refine ⟨6724023413633947532714501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4482682275755965021809667 6724023413633947532714501)
        ·
          refine ⟨1260754390056365162383969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6724023413633947532714501 1260754390056365162383969)
          ·
            refine ⟨945565792542273871787977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1260754390056365162383969 945565792542273871787977)
            ·
              refine ⟨709174344406705403840983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 945565792542273871787977 709174344406705403840983)
              ·
                refine ⟨1063761516610058105761475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 709174344406705403840983 1063761516610058105761475)
                ·
                  refine ⟨1595642274915087158642213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1063761516610058105761475 1595642274915087158642213)
                  ·
                    refine ⟨299182926546578842245415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1595642274915087158642213 299182926546578842245415)
                    ·
                      rfl

theorem cell22_873985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 2, 1, 1, 4].length) (baseStart_873985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_873985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_873985 prefixEnd_873985 := by exact prefixLift 873985
  have htrace : WordTrace (prefixWord ++ tailWord_873985) baseStart_873985 baseEnd_873985 := by
    simpa [prefixWord, tailWord_873985, baseEnd_873985] using wordTrace_append hprefix tailTrace_873985
  have hstable : (prefixWord ++ tailWord_873985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873985).length < 2 ^ (prefixWord ++ tailWord_873985).sum := by decide
  have hdescent : baseEnd_873985 < baseStart_873985 := by decide
  rcases family_descends (prefixWord ++ tailWord_873985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873994 : List Nat := [3, 1, 2, 2, 2, 3, 9]
def baseStart_873994 : Nat := 118140960795 + 873994 * 2 ^ 59
def prefixEnd_873994 : Nat := 4983230072969 + 3 ^ 40 * 873994 * 2
def baseEnd_873994 : Nat := 11080963238166882176681

theorem tailTrace_873994 : CollatzResearch.WordTrace tailWord_873994 prefixEnd_873994 11080963238166882176681 := by
  unfold tailWord_873994
  simp only [CollatzResearch.WordTrace]
  refine ⟨7969294998919119784153259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21251453330450986091075357 7969294998919119784153259)
  ·
    refine ⟨11953942498378679676229889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7969294998919119784153259 11953942498378679676229889)
    ·
      refine ⟨8965456873784009757172417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11953942498378679676229889 8965456873784009757172417)
      ·
        refine ⟨6724092655338007317879313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8965456873784009757172417 6724092655338007317879313)
        ·
          refine ⟨5043069491503505488409485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6724092655338007317879313 5043069491503505488409485)
          ·
            refine ⟨1891151059313814558153557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5043069491503505488409485 1891151059313814558153557)
            ·
              refine ⟨11080963238166882176681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1891151059313814558153557 11080963238166882176681)
              ·
                rfl

theorem cell22_873994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 9].length) (baseStart_873994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_873994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_873994 prefixEnd_873994 := by exact prefixLift 873994
  have htrace : WordTrace (prefixWord ++ tailWord_873994) baseStart_873994 baseEnd_873994 := by
    simpa [prefixWord, tailWord_873994, baseEnd_873994] using wordTrace_append hprefix tailTrace_873994
  have hstable : (prefixWord ++ tailWord_873994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873994).length < 2 ^ (prefixWord ++ tailWord_873994).sum := by decide
  have hdescent : baseEnd_873994 < baseStart_873994 := by decide
  rcases family_descends (prefixWord ++ tailWord_873994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_873998 : List Nat := [4, 1, 1, 2, 4, 1, 1, 1, 4, 3]
def baseStart_873998 : Nat := 118140960795 + 873998 * 2 ^ 59
def prefixEnd_873998 : Nat := 4983230072969 + 3 ^ 40 * 873998 * 2
def baseEnd_873998 : Nat := 299187376712251141670375

theorem tailTrace_873998 : CollatzResearch.WordTrace tailWord_873998 prefixEnd_873998 299187376712251141670375 := by
  unfold tailWord_873998
  simp only [CollatzResearch.WordTrace]
  refine ⟨3984665735957748477469831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21251550591774658546505765 3984665735957748477469831)
  ·
    refine ⟨5976998603936622716204747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3984665735957748477469831 5976998603936622716204747)
    ·
      refine ⟨8965497905904934074307121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5976998603936622716204747 8965497905904934074307121)
      ·
        refine ⟨6724123429428700555730341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8965497905904934074307121 6724123429428700555730341)
        ·
          refine ⟨1260773143017881354199439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6724123429428700555730341 1260773143017881354199439)
          ·
            refine ⟨1891159714526822031299159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1260773143017881354199439 1891159714526822031299159)
            ·
              refine ⟨2836739571790233046948739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1891159714526822031299159 2836739571790233046948739)
              ·
                refine ⟨4255109357685349570423109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2836739571790233046948739 4255109357685349570423109)
                ·
                  refine ⟨797833004566003044454333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4255109357685349570423109 797833004566003044454333)
                  ·
                    refine ⟨299187376712251141670375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 797833004566003044454333 299187376712251141670375)
                    ·
                      rfl

theorem cell22_873998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 1, 4, 3].length) (baseStart_873998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_873998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_873998 prefixEnd_873998 := by exact prefixLift 873998
  have htrace : WordTrace (prefixWord ++ tailWord_873998) baseStart_873998 baseEnd_873998 := by
    simpa [prefixWord, tailWord_873998, baseEnd_873998] using wordTrace_append hprefix tailTrace_873998
  have hstable : (prefixWord ++ tailWord_873998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_873998).length < 2 ^ (prefixWord ++ tailWord_873998).sum := by decide
  have hdescent : baseEnd_873998 < baseStart_873998 := by decide
  rcases family_descends (prefixWord ++ tailWord_873998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874039 : List Nat := [1, 1, 3, 1, 2, 4, 1, 2, 7]
def baseStart_874039 : Nat := 118140960795 + 874039 * 2 ^ 59
def prefixEnd_874039 : Nat := 4983230072969 + 3 ^ 40 * 874039 * 2
def baseEnd_874039 : Nat := 99733803950046900465083

theorem tailTrace_874039 : CollatzResearch.WordTrace tailWord_874039 prefixEnd_874039 99733803950046900465083 := by
  unfold tailWord_874039
  simp only [CollatzResearch.WordTrace]
  refine ⟨31878821280513451822001171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21252547520342301214667447 31878821280513451822001171)
  ·
    refine ⟨47818231920770177733001757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31878821280513451822001171 47818231920770177733001757)
    ·
      refine ⟨17931836970288816649875659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47818231920770177733001757 17931836970288816649875659)
      ·
        refine ⟨26897755455433224974813489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17931836970288816649875659 26897755455433224974813489)
        ·
          refine ⟨20173316591574918731110117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26897755455433224974813489 20173316591574918731110117)
          ·
            refine ⟨3782496860920297262083147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20173316591574918731110117 3782496860920297262083147)
            ·
              refine ⟨5673745291380445893124721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3782496860920297262083147 5673745291380445893124721)
              ·
                refine ⟨4255308968535334419843541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5673745291380445893124721 4255308968535334419843541)
                ·
                  refine ⟨99733803950046900465083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4255308968535334419843541 99733803950046900465083)
                  ·
                    rfl

theorem cell22_874039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 2, 7].length) (baseStart_874039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_874039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_874039 prefixEnd_874039 := by exact prefixLift 874039
  have htrace : WordTrace (prefixWord ++ tailWord_874039) baseStart_874039 baseEnd_874039 := by
    simpa [prefixWord, tailWord_874039, baseEnd_874039] using wordTrace_append hprefix tailTrace_874039
  have hstable : (prefixWord ++ tailWord_874039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874039).length < 2 ^ (prefixWord ++ tailWord_874039).sum := by decide
  have hdescent : baseEnd_874039 < baseStart_874039 := by decide
  rcases family_descends (prefixWord ++ tailWord_874039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874069 : List Nat := [1, 3, 2, 2, 1, 1, 1, 1, 2, 8]
def baseStart_874069 : Nat := 118140960795 + 874069 * 2 ^ 59
def prefixEnd_874069 : Nat := 4983230072969 + 3 ^ 40 * 874069 * 2
def baseEnd_874069 : Nat := 299211681463230623145157

theorem tailTrace_874069 : CollatzResearch.WordTrace tailWord_874069 prefixEnd_874069 299211681463230623145157 := by
  unfold tailWord_874069
  simp only [CollatzResearch.WordTrace]
  refine ⟨31879915470404766945593261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21253276980269844630395507 31879915470404766945593261)
  ·
    refine ⟨11954968301401787604597473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31879915470404766945593261 11954968301401787604597473)
    ·
      refine ⟨8966226226051340703448105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11954968301401787604597473 8966226226051340703448105)
      ·
        refine ⟨6724669669538505527586079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8966226226051340703448105 6724669669538505527586079)
        ·
          refine ⟨10087004504307758291379119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6724669669538505527586079 10087004504307758291379119)
          ·
            refine ⟨15130506756461637437068679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10087004504307758291379119 15130506756461637437068679)
            ·
              refine ⟨22695760134692456155603019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15130506756461637437068679 22695760134692456155603019)
              ·
                refine ⟨34043640202038684233404529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22695760134692456155603019 34043640202038684233404529)
                ·
                  refine ⟨25532730151529013175053397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34043640202038684233404529 25532730151529013175053397)
                  ·
                    refine ⟨299211681463230623145157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 25532730151529013175053397 299211681463230623145157)
                    ·
                      rfl

theorem cell22_874069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 8].length) (baseStart_874069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_874069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_874069 prefixEnd_874069 := by exact prefixLift 874069
  have htrace : WordTrace (prefixWord ++ tailWord_874069) baseStart_874069 baseEnd_874069 := by
    simpa [prefixWord, tailWord_874069, baseEnd_874069] using wordTrace_append hprefix tailTrace_874069
  have hstable : (prefixWord ++ tailWord_874069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874069).length < 2 ^ (prefixWord ++ tailWord_874069).sum := by decide
  have hdescent : baseEnd_874069 < baseStart_874069 := by decide
  rcases family_descends (prefixWord ++ tailWord_874069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874129 : List Nat := [1, 2, 2, 1, 1, 1, 1, 13]
def baseStart_874129 : Nat := 118140960795 + 874129 * 2 ^ 59
def prefixEnd_874129 : Nat := 4983230072969 + 3 ^ 40 * 874129 * 2
def baseEnd_874129 : Nat := 33248024521045607404997

theorem tailTrace_874129 : CollatzResearch.WordTrace tailWord_874129 prefixEnd_874129 33248024521045607404997 := by
  unfold tailWord_874129
  simp only [CollatzResearch.WordTrace]
  refine ⟨31882103850187397192777441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21254735900124931461851627 31882103850187397192777441)
  ·
    refine ⟨23911577887640547894583081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31882103850187397192777441 23911577887640547894583081)
    ·
      refine ⟨17933683415730410920937311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23911577887640547894583081 17933683415730410920937311)
      ·
        refine ⟨26900525123595616381405967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17933683415730410920937311 26900525123595616381405967)
        ·
          refine ⟨40350787685393424572108951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26900525123595616381405967 40350787685393424572108951)
          ·
            refine ⟨60526181528090136858163427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40350787685393424572108951 60526181528090136858163427)
            ·
              refine ⟨90789272292135205287245141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60526181528090136858163427 90789272292135205287245141)
              ·
                refine ⟨33248024521045607404997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 90789272292135205287245141 33248024521045607404997)
                ·
                  rfl

theorem cell22_874129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 13].length) (baseStart_874129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_874129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_874129 prefixEnd_874129 := by exact prefixLift 874129
  have htrace : WordTrace (prefixWord ++ tailWord_874129) baseStart_874129 baseEnd_874129 := by
    simpa [prefixWord, tailWord_874129, baseEnd_874129] using wordTrace_append hprefix tailTrace_874129
  have hstable : (prefixWord ++ tailWord_874129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874129).length < 2 ^ (prefixWord ++ tailWord_874129).sum := by decide
  have hdescent : baseEnd_874129 < baseStart_874129 := by decide
  rcases family_descends (prefixWord ++ tailWord_874129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874148 : List Nat := [2, 3, 1, 2, 2, 2, 3, 1, 2, 4]
def baseStart_874148 : Nat := 118140960795 + 874148 * 2 ^ 59
def prefixEnd_874148 : Nat := 4983230072969 + 3 ^ 40 * 874148 * 2
def baseEnd_874148 : Nat := 299238724777700750419915

theorem tailTrace_874148 : CollatzResearch.WordTrace tailWord_874148 prefixEnd_874148 299238724777700750419915 := by
  unfold tailWord_874148
  simp only [CollatzResearch.WordTrace]
  refine ⟨15941398418559281718859549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21255197891412375625146065 15941398418559281718859549)
  ·
    refine ⟨5978024406959730644572331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15941398418559281718859549 5978024406959730644572331)
    ·
      refine ⟨8967036610439595966858497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5978024406959730644572331 8967036610439595966858497)
      ·
        refine ⟨6725277457829696975143873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8967036610439595966858497 6725277457829696975143873)
        ·
          refine ⟨5043958093372272731357905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6725277457829696975143873 5043958093372272731357905)
          ·
            refine ⟨3782968570029204548518429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5043958093372272731357905 3782968570029204548518429)
            ·
              refine ⟨1418613213760951705694411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3782968570029204548518429 1418613213760951705694411)
              ·
                refine ⟨2127919820641427558541617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1418613213760951705694411 2127919820641427558541617)
                ·
                  refine ⟨1595939865481070668906213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2127919820641427558541617 1595939865481070668906213)
                  ·
                    refine ⟨299238724777700750419915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1595939865481070668906213 299238724777700750419915)
                    ·
                      rfl

theorem cell22_874148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 1, 2, 4].length) (baseStart_874148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_874148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_874148 prefixEnd_874148 := by exact prefixLift 874148
  have htrace : WordTrace (prefixWord ++ tailWord_874148) baseStart_874148 baseEnd_874148 := by
    simpa [prefixWord, tailWord_874148, baseEnd_874148] using wordTrace_append hprefix tailTrace_874148
  have hstable : (prefixWord ++ tailWord_874148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874148).length < 2 ^ (prefixWord ++ tailWord_874148).sum := by decide
  have hdescent : baseEnd_874148 < baseStart_874148 := by decide
  rcases family_descends (prefixWord ++ tailWord_874148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874191 : List Nat := [1, 1, 2, 1, 1, 3, 1, 7, 5]
def baseStart_874191 : Nat := 118140960795 + 874191 * 2 ^ 59
def prefixEnd_874191 : Nat := 4983230072969 + 3 ^ 40 * 874191 * 2
def baseEnd_874191 : Nat := 99751148185487657198261

theorem tailTrace_874191 : CollatzResearch.WordTrace tailWord_874191 prefixEnd_874191 99751148185487657198261 := by
  unfold tailWord_874191
  simp only [CollatzResearch.WordTrace]
  refine ⟨31884365175962781781534427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21256243450641854521022951 31884365175962781781534427)
  ·
    refine ⟨47826547763944172672301641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31884365175962781781534427 47826547763944172672301641)
    ·
      refine ⟨35869910822958129504226231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47826547763944172672301641 35869910822958129504226231)
      ·
        refine ⟨53804866234437194256339347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35869910822958129504226231 53804866234437194256339347)
        ·
          refine ⟨80707299351655791384509021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53804866234437194256339347 80707299351655791384509021)
          ·
            refine ⟨30265237256870921769190883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80707299351655791384509021 30265237256870921769190883)
            ·
              refine ⟨45397855885306382653786325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30265237256870921769190883 45397855885306382653786325)
              ·
                refine ⟨1064012247311868343448117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 45397855885306382653786325 1064012247311868343448117)
                ·
                  refine ⟨99751148185487657198261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1064012247311868343448117 99751148185487657198261)
                  ·
                    rfl

theorem cell22_874191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 7, 5].length) (baseStart_874191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_874191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_874191 prefixEnd_874191 := by exact prefixLift 874191
  have htrace : WordTrace (prefixWord ++ tailWord_874191) baseStart_874191 baseEnd_874191 := by
    simpa [prefixWord, tailWord_874191, baseEnd_874191] using wordTrace_append hprefix tailTrace_874191
  have hstable : (prefixWord ++ tailWord_874191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874191).length < 2 ^ (prefixWord ++ tailWord_874191).sum := by decide
  have hdescent : baseEnd_874191 < baseStart_874191 := by decide
  rcases family_descends (prefixWord ++ tailWord_874191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874268 : List Nat := [2, 2, 3, 1, 1, 2, 3, 2, 1, 5]
def baseStart_874268 : Nat := 118140960795 + 874268 * 2 ^ 59
def prefixEnd_874268 : Nat := 4983230072969 + 3 ^ 40 * 874268 * 2
def baseEnd_874268 : Nat := 299279803230060437419547

theorem tailTrace_874268 : CollatzResearch.WordTrace tailWord_874268 prefixEnd_874268 299279803230060437419547 := by
  unfold tailWord_874268
  simp only [CollatzResearch.WordTrace]
  refine ⟨15943586798341911966043729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21258115731122549288058305 15943586798341911966043729)
  ·
    refine ⟨11957690098756433974532797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15943586798341911966043729 11957690098756433974532797)
    ·
      refine ⟨4484133787033662740449799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11957690098756433974532797 4484133787033662740449799)
      ·
        refine ⟨6726200680550494110674699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4484133787033662740449799 6726200680550494110674699)
        ·
          refine ⟨10089301020825741166012049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6726200680550494110674699 10089301020825741166012049)
          ·
            refine ⟨7566975765619305874509037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10089301020825741166012049 7566975765619305874509037)
            ·
              refine ⟨2837615912107239702940889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7566975765619305874509037 2837615912107239702940889)
              ·
                refine ⟨2128211934080429777205667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2837615912107239702940889 2128211934080429777205667)
                ·
                  refine ⟨3192317901120644665808501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2128211934080429777205667 3192317901120644665808501)
                  ·
                    refine ⟨299279803230060437419547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3192317901120644665808501 299279803230060437419547)
                    ·
                      rfl

theorem cell22_874268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_874268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_874268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_874268 prefixEnd_874268 := by exact prefixLift 874268
  have htrace : WordTrace (prefixWord ++ tailWord_874268) baseStart_874268 baseEnd_874268 := by
    simpa [prefixWord, tailWord_874268, baseEnd_874268] using wordTrace_append hprefix tailTrace_874268
  have hstable : (prefixWord ++ tailWord_874268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874268).length < 2 ^ (prefixWord ++ tailWord_874268).sum := by decide
  have hdescent : baseEnd_874268 < baseStart_874268 := by decide
  rcases family_descends (prefixWord ++ tailWord_874268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874298 : List Nat := [3, 1, 1, 1, 5, 1, 3, 7]
def baseStart_874298 : Nat := 118140960795 + 874298 * 2 ^ 59
def prefixEnd_874298 : Nat := 4983230072969 + 3 ^ 40 * 874298 * 2
def baseEnd_874298 : Nat := 33254452538127817685495

theorem tailTrace_874298 : CollatzResearch.WordTrace tailWord_874298 prefixEnd_874298 33254452538127817685495 := by
  unfold tailWord_874298
  simp only [CollatzResearch.WordTrace]
  refine ⟨7972066946643784763919887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21258845191050092703786365 7972066946643784763919887)
  ·
    refine ⟨11958100419965677145879831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7972066946643784763919887 11958100419965677145879831)
    ·
      refine ⟨17937150629948515718819747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11958100419965677145879831 17937150629948515718819747)
      ·
        refine ⟨26905725944922773578229621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17937150629948515718819747 26905725944922773578229621)
        ·
          refine ⟨2522411807336510022959027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26905725944922773578229621 2522411807336510022959027)
          ·
            refine ⟨3783617711004765034438541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2522411807336510022959027 3783617711004765034438541)
            ·
              refine ⟨1418856641626786887914453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3783617711004765034438541 1418856641626786887914453)
              ·
                refine ⟨33254452538127817685495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1418856641626786887914453 33254452538127817685495)
                ·
                  rfl

theorem cell22_874298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 7].length) (baseStart_874298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_874298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_874298 prefixEnd_874298 := by exact prefixLift 874298
  have htrace : WordTrace (prefixWord ++ tailWord_874298) baseStart_874298 baseEnd_874298 := by
    simpa [prefixWord, tailWord_874298, baseEnd_874298] using wordTrace_append hprefix tailTrace_874298
  have hstable : (prefixWord ++ tailWord_874298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874298).length < 2 ^ (prefixWord ++ tailWord_874298).sum := by decide
  have hdescent : baseEnd_874298 < baseStart_874298 := by decide
  rcases family_descends (prefixWord ++ tailWord_874298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874302 : List Nat := [4, 2, 1, 2, 2, 1, 2, 3, 2, 3]
def baseStart_874302 : Nat := 118140960795 + 874302 * 2 ^ 59
def prefixEnd_874302 : Nat := 4983230072969 + 3 ^ 40 * 874302 * 2
def baseEnd_874302 : Nat := 299291442124895682069443

theorem tailTrace_874302 : CollatzResearch.WordTrace tailWord_874302 prefixEnd_874302 299291442124895682069443 := by
  unfold tailWord_874302
  simp only [CollatzResearch.WordTrace]
  refine ⟨3986051709820080967353145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21258942452373765159216773 3986051709820080967353145)
  ·
    refine ⟨2989538782365060725514859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3986051709820080967353145 2989538782365060725514859)
    ·
      refine ⟨4484308173547591088272289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2989538782365060725514859 4484308173547591088272289)
      ·
        refine ⟨3363231130160693316204217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4484308173547591088272289 3363231130160693316204217)
        ·
          refine ⟨2522423347620519987153163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3363231130160693316204217 2522423347620519987153163)
          ·
            refine ⟨3783635021430779980729745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2522423347620519987153163 3783635021430779980729745)
            ·
              refine ⟨2837726266073084985547309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3783635021430779980729745 2837726266073084985547309)
              ·
                refine ⟨1064147349777406869580241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2837726266073084985547309 1064147349777406869580241)
                ·
                  refine ⟨798110512333055152185181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1064147349777406869580241 798110512333055152185181)
                  ·
                    refine ⟨299291442124895682069443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 798110512333055152185181 299291442124895682069443)
                    ·
                      rfl

theorem cell22_874302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 3, 2, 3].length) (baseStart_874302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_874302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_874302 prefixEnd_874302 := by exact prefixLift 874302
  have htrace : WordTrace (prefixWord ++ tailWord_874302) baseStart_874302 baseEnd_874302 := by
    simpa [prefixWord, tailWord_874302, baseEnd_874302] using wordTrace_append hprefix tailTrace_874302
  have hstable : (prefixWord ++ tailWord_874302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874302).length < 2 ^ (prefixWord ++ tailWord_874302).sum := by decide
  have hdescent : baseEnd_874302 < baseStart_874302 := by decide
  rcases family_descends (prefixWord ++ tailWord_874302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874317 : List Nat := [1, 6, 1, 2, 1, 1, 3, 1, 2, 4]
def baseStart_874317 : Nat := 118140960795 + 874317 * 2 ^ 59
def prefixEnd_874317 : Nat := 4983230072969 + 3 ^ 40 * 874317 * 2
def baseEnd_874317 : Nat := 299296576931440642944397

theorem tailTrace_874317 : CollatzResearch.WordTrace tailWord_874317 prefixEnd_874317 299296576931440642944397 := by
  unfold tailWord_874317
  simp only [CollatzResearch.WordTrace]
  refine ⟨31888960773506305300621205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21259307182337536867080803 31888960773506305300621205)
  ·
    refine ⟨1494795036258108060966619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 31888960773506305300621205 1494795036258108060966619)
    ·
      refine ⟨2242192554387162091449929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1494795036258108060966619 2242192554387162091449929)
      ·
        refine ⟨1681644415790371568587447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2242192554387162091449929 1681644415790371568587447)
        ·
          refine ⟨2522466623685557352881171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1681644415790371568587447 2522466623685557352881171)
          ·
            refine ⟨3783699935528336029321757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2522466623685557352881171 3783699935528336029321757)
            ·
              refine ⟨1418887475823126010995659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3783699935528336029321757 1418887475823126010995659)
              ·
                refine ⟨2128331213734689016493489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1418887475823126010995659 2128331213734689016493489)
                ·
                  refine ⟨1596248410301016762370117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2128331213734689016493489 1596248410301016762370117)
                  ·
                    refine ⟨299296576931440642944397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1596248410301016762370117 299296576931440642944397)
                    ·
                      rfl

theorem cell22_874317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_874317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_874317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_874317 prefixEnd_874317 := by exact prefixLift 874317
  have htrace : WordTrace (prefixWord ++ tailWord_874317) baseStart_874317 baseEnd_874317 := by
    simpa [prefixWord, tailWord_874317, baseEnd_874317] using wordTrace_append hprefix tailTrace_874317
  have hstable : (prefixWord ++ tailWord_874317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874317).length < 2 ^ (prefixWord ++ tailWord_874317).sum := by decide
  have hdescent : baseEnd_874317 < baseStart_874317 := by decide
  rcases family_descends (prefixWord ++ tailWord_874317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874343 : List Nat := [1, 1, 5, 1, 2, 1, 3, 1, 7]
def baseStart_874343 : Nat := 118140960795 + 874343 * 2 ^ 59
def prefixEnd_874343 : Nat := 4983230072969 + 3 ^ 40 * 874343 * 2
def baseEnd_874343 : Nat := 99768492420928413931439

theorem tailTrace_874343 : CollatzResearch.WordTrace tailWord_874343 prefixEnd_874343 99768492420928413931439 := by
  unfold tailWord_874343
  simp only [CollatzResearch.WordTrace]
  refine ⟨31889909071412111741067683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21259939380941407827378455 31889909071412111741067683)
  ·
    refine ⟨47834863607118167611601525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31889909071412111741067683 47834863607118167611601525)
    ·
      refine ⟨4484518463167328213587643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47834863607118167611601525 4484518463167328213587643)
      ·
        refine ⟨6726777694750992320381465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4484518463167328213587643 6726777694750992320381465)
        ·
          refine ⟨5045083271063244240286099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6726777694750992320381465 5045083271063244240286099)
          ·
            refine ⟨7567624906594866360429149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5045083271063244240286099 7567624906594866360429149)
            ·
              refine ⟨2837859339973074885160931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7567624906594866360429149 2837859339973074885160931)
              ·
                refine ⟨4256789009959612327741397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2837859339973074885160931 4256789009959612327741397)
                ·
                  refine ⟨99768492420928413931439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4256789009959612327741397 99768492420928413931439)
                  ·
                    rfl

theorem cell22_874343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 1, 7].length) (baseStart_874343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_874343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_874343 prefixEnd_874343 := by exact prefixLift 874343
  have htrace : WordTrace (prefixWord ++ tailWord_874343) baseStart_874343 baseEnd_874343 := by
    simpa [prefixWord, tailWord_874343, baseEnd_874343] using wordTrace_append hprefix tailTrace_874343
  have hstable : (prefixWord ++ tailWord_874343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874343).length < 2 ^ (prefixWord ++ tailWord_874343).sum := by decide
  have hdescent : baseEnd_874343 < baseStart_874343 := by decide
  rcases family_descends (prefixWord ++ tailWord_874343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874398 : List Nat := [4, 3, 1, 3, 2, 1, 1, 1, 3, 3]
def baseStart_874398 : Nat := 118140960795 + 874398 * 2 ^ 59
def prefixEnd_874398 : Nat := 4983230072969 + 3 ^ 40 * 874398 * 2
def baseEnd_874398 : Nat := 299324304886783431669149

theorem tailTrace_874398 : CollatzResearch.WordTrace tailWord_874398 prefixEnd_874398 299324304886783431669149 := by
  unfold tailWord_874398
  simp only [CollatzResearch.WordTrace]
  refine ⟨3986489385776607016789981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21261276724141904089546565 3986489385776607016789981)
  ·
    refine ⟨1494933519666227631296243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3986489385776607016789981 1494933519666227631296243)
    ·
      refine ⟨2242400279499341446944365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1494933519666227631296243 2242400279499341446944365)
      ·
        refine ⟨840900104812253042604137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2242400279499341446944365 840900104812253042604137)
        ·
          refine ⟨630675078609189781953103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 840900104812253042604137 630675078609189781953103)
          ·
            refine ⟨946012617913784672929655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 630675078609189781953103 946012617913784672929655)
            ·
              refine ⟨1419018926870677009394483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 946012617913784672929655 1419018926870677009394483)
              ·
                refine ⟨2128528390306015514091725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1419018926870677009394483 2128528390306015514091725)
                ·
                  refine ⟨798198146364755817784397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2128528390306015514091725 798198146364755817784397)
                  ·
                    refine ⟨299324304886783431669149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 798198146364755817784397 299324304886783431669149)
                    ·
                      rfl

theorem cell22_874398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_874398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_874398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_874398 prefixEnd_874398 := by exact prefixLift 874398
  have htrace : WordTrace (prefixWord ++ tailWord_874398) baseStart_874398 baseEnd_874398 := by
    simpa [prefixWord, tailWord_874398, baseEnd_874398] using wordTrace_append hprefix tailTrace_874398
  have hstable : (prefixWord ++ tailWord_874398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874398).length < 2 ^ (prefixWord ++ tailWord_874398).sum := by decide
  have hdescent : baseEnd_874398 < baseStart_874398 := by decide
  rcases family_descends (prefixWord ++ tailWord_874398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874405 : List Nat := [1, 3, 1, 2, 1, 1, 1, 8, 4]
def baseStart_874405 : Nat := 118140960795 + 874405 * 2 ^ 59
def prefixEnd_874405 : Nat := 4983230072969 + 3 ^ 40 * 874405 * 2
def baseEnd_874405 : Nat := 99775567043279248914709

theorem tailTrace_874405 : CollatzResearch.WordTrace tailWord_874405 prefixEnd_874405 99775567043279248914709 := by
  unfold tailWord_874405
  simp only [CollatzResearch.WordTrace]
  refine ⟨31892170397187496329824669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21261446931458330886549779 31892170397187496329824669)
  ·
    refine ⟨11959563898945311123684251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31892170397187496329824669 11959563898945311123684251)
    ·
      refine ⟨17939345848417966685526377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11959563898945311123684251 17939345848417966685526377)
      ·
        refine ⟨13454509386313475014144783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17939345848417966685526377 13454509386313475014144783)
        ·
          refine ⟨20181764079470212521217175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13454509386313475014144783 20181764079470212521217175)
          ·
            refine ⟨30272646119205318781825763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20181764079470212521217175 30272646119205318781825763)
            ·
              refine ⟨45408969178807978172738645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30272646119205318781825763 45408969178807978172738645)
              ·
                refine ⟨532136357564155994211781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 45408969178807978172738645 532136357564155994211781)
                ·
                  refine ⟨99775567043279248914709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 532136357564155994211781 99775567043279248914709)
                  ·
                    rfl

theorem cell22_874405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 8, 4].length) (baseStart_874405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_874405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_874405 prefixEnd_874405 := by exact prefixLift 874405
  have htrace : WordTrace (prefixWord ++ tailWord_874405) baseStart_874405 baseEnd_874405 := by
    simpa [prefixWord, tailWord_874405, baseEnd_874405] using wordTrace_append hprefix tailTrace_874405
  have hstable : (prefixWord ++ tailWord_874405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874405).length < 2 ^ (prefixWord ++ tailWord_874405).sum := by decide
  have hdescent : baseEnd_874405 < baseStart_874405 := by decide
  rcases family_descends (prefixWord ++ tailWord_874405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874418 : List Nat := [3, 2, 1, 1, 1, 1, 1, 3, 3, 6]
def baseStart_874418 : Nat := 118140960795 + 874418 * 2 ^ 59
def prefixEnd_874418 : Nat := 4983230072969 + 3 ^ 40 * 874418 * 2
def baseEnd_874418 : Nat := 299331151295510046169087

theorem tailTrace_874418 : CollatzResearch.WordTrace tailWord_874418 prefixEnd_874418 299331151295510046169087 := by
  unfold tailWord_874418
  simp only [CollatzResearch.WordTrace]
  refine ⟨7973161136535099887511977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21261763030760266366698605 7973161136535099887511977)
  ·
    refine ⟨5979870852401324915633983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7973161136535099887511977 5979870852401324915633983)
    ·
      refine ⟨8969806278601987373450975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5979870852401324915633983 8969806278601987373450975)
      ·
        refine ⟨13454709417902981060176463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8969806278601987373450975 13454709417902981060176463)
        ·
          refine ⟨20182064126854471590264695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13454709417902981060176463 20182064126854471590264695)
          ·
            refine ⟨30273096190281707385397043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20182064126854471590264695 30273096190281707385397043)
            ·
              refine ⟨45409644285422561078095565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30273096190281707385397043 45409644285422561078095565)
              ·
                refine ⟨17028616607033460404285837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45409644285422561078095565 17028616607033460404285837)
                ·
                  refine ⟨6385731227637547651607189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17028616607033460404285837 6385731227637547651607189)
                  ·
                    refine ⟨299331151295510046169087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6385731227637547651607189 299331151295510046169087)
                    ·
                      rfl

theorem cell22_874418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 3, 6].length) (baseStart_874418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_874418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_874418 prefixEnd_874418 := by exact prefixLift 874418
  have htrace : WordTrace (prefixWord ++ tailWord_874418) baseStart_874418 baseEnd_874418 := by
    simpa [prefixWord, tailWord_874418, baseEnd_874418] using wordTrace_append hprefix tailTrace_874418
  have hstable : (prefixWord ++ tailWord_874418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874418).length < 2 ^ (prefixWord ++ tailWord_874418).sum := by decide
  have hdescent : baseEnd_874418 < baseStart_874418 := by decide
  rcases family_descends (prefixWord ++ tailWord_874418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874450 : List Nat := [3, 2, 2, 3, 2, 10]
def baseStart_874450 : Nat := 118140960795 + 874450 * 2 ^ 59
def prefixEnd_874450 : Nat := 4983230072969 + 3 ^ 40 * 874450 * 2
def baseEnd_874450 : Nat := 3695581549993489251469

theorem tailTrace_874450 : CollatzResearch.WordTrace tailWord_874450 prefixEnd_874450 3695581549993489251469 := by
  unfold tailWord_874450
  simp only [CollatzResearch.WordTrace]
  refine ⟨7973452920506117253803201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21262541121349646010141869 7973452920506117253803201)
  ·
    refine ⟨5980089690379587940352401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7973452920506117253803201 5980089690379587940352401)
    ·
      refine ⟨4485067267784690955264301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5980089690379587940352401 4485067267784690955264301)
      ·
        refine ⟨1681900225419259108224113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4485067267784690955264301 1681900225419259108224113)
        ·
          refine ⟨1261425169064444331168085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1681900225419259108224113 1261425169064444331168085)
          ·
            refine ⟨3695581549993489251469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1261425169064444331168085 3695581549993489251469)
            ·
              rfl

theorem cell22_874450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 10].length) (baseStart_874450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_874450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_874450 prefixEnd_874450 := by exact prefixLift 874450
  have htrace : WordTrace (prefixWord ++ tailWord_874450) baseStart_874450 baseEnd_874450 := by
    simpa [prefixWord, tailWord_874450, baseEnd_874450] using wordTrace_append hprefix tailTrace_874450
  have hstable : (prefixWord ++ tailWord_874450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874450).length < 2 ^ (prefixWord ++ tailWord_874450).sum := by decide
  have hdescent : baseEnd_874450 < baseStart_874450 := by decide
  rcases family_descends (prefixWord ++ tailWord_874450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874486 : List Nat := [5, 1, 1, 1, 5, 1, 1, 1, 2, 4]
def baseStart_874486 : Nat := 118140960795 + 874486 * 2 ^ 59
def prefixEnd_874486 : Nat := 4983230072969 + 3 ^ 40 * 874486 * 2
def baseEnd_874486 : Nat := 299354429085180535468879

theorem tailTrace_874486 : CollatzResearch.WordTrace tailWord_874486 prefixEnd_874486 299354429085180535468879 := by
  unfold tailWord_874486
  simp only [CollatzResearch.WordTrace]
  refine ⟨1993445294368377947720207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21263416473262698109015541 1993445294368377947720207)
  ·
    refine ⟨2990167941552566921580311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1993445294368377947720207 2990167941552566921580311)
    ·
      refine ⟨4485251912328850382370467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2990167941552566921580311 4485251912328850382370467)
      ·
        refine ⟨6727877868493275573555701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4485251912328850382370467 6727877868493275573555701)
        ·
          refine ⟨630738550171244585020847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6727877868493275573555701 630738550171244585020847)
          ·
            refine ⟨946107825256866877531271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 630738550171244585020847 946107825256866877531271)
            ·
              refine ⟨1419161737885300316296907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 946107825256866877531271 1419161737885300316296907)
              ·
                refine ⟨2128742606827950474445361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1419161737885300316296907 2128742606827950474445361)
                ·
                  refine ⟨1596556955120962855834021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2128742606827950474445361 1596556955120962855834021)
                  ·
                    refine ⟨299354429085180535468879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1596556955120962855834021 299354429085180535468879)
                    ·
                      rfl

theorem cell22_874486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 1, 2, 4].length) (baseStart_874486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_874486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_874486 prefixEnd_874486 := by exact prefixLift 874486
  have htrace : WordTrace (prefixWord ++ tailWord_874486) baseStart_874486 baseEnd_874486 := by
    simpa [prefixWord, tailWord_874486, baseEnd_874486] using wordTrace_append hprefix tailTrace_874486
  have hstable : (prefixWord ++ tailWord_874486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874486).length < 2 ^ (prefixWord ++ tailWord_874486).sum := by decide
  have hdescent : baseEnd_874486 < baseStart_874486 := by decide
  rcases family_descends (prefixWord ++ tailWord_874486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874510 : List Nat := [4, 1, 1, 2, 2, 1, 1, 1, 4, 5]
def baseStart_874510 : Nat := 118140960795 + 874510 * 2 ^ 59
def prefixEnd_874510 : Nat := 4983230072969 + 3 ^ 40 * 874510 * 2
def baseEnd_874510 : Nat := 299362644775652472868805

theorem tailTrace_874510 : CollatzResearch.WordTrace tailWord_874510 prefixEnd_874510 299362644775652472868805 := by
  unfold tailWord_874510
  simp only [CollatzResearch.WordTrace]
  refine ⟨3987000007725887407799623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21264000041204732841597989 3987000007725887407799623)
  ·
    refine ⟨5980500011588831111699435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3987000007725887407799623 5980500011588831111699435)
    ·
      refine ⟨8970750017383246667549153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5980500011588831111699435 8970750017383246667549153)
      ·
        refine ⟨6728062513037435000661865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8970750017383246667549153 6728062513037435000661865)
        ·
          refine ⟨5046046884778076250496399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6728062513037435000661865 5046046884778076250496399)
          ·
            refine ⟨7569070327167114375744599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5046046884778076250496399 7569070327167114375744599)
            ·
              refine ⟨11353605490750671563616899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7569070327167114375744599 11353605490750671563616899)
              ·
                refine ⟨17030408236126007345425349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11353605490750671563616899 17030408236126007345425349)
                ·
                  refine ⟨3193201544273626377267253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17030408236126007345425349 3193201544273626377267253)
                  ·
                    refine ⟨299362644775652472868805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3193201544273626377267253 299362644775652472868805)
                    ·
                      rfl

theorem cell22_874510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 4, 5].length) (baseStart_874510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_874510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_874510 prefixEnd_874510 := by exact prefixLift 874510
  have htrace : WordTrace (prefixWord ++ tailWord_874510) baseStart_874510 baseEnd_874510 := by
    simpa [prefixWord, tailWord_874510, baseEnd_874510] using wordTrace_append hprefix tailTrace_874510
  have hstable : (prefixWord ++ tailWord_874510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874510).length < 2 ^ (prefixWord ++ tailWord_874510).sum := by decide
  have hdescent : baseEnd_874510 < baseStart_874510 := by decide
  rcases family_descends (prefixWord ++ tailWord_874510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874529 : List Nat := [1, 2, 3, 2, 4, 1, 3, 1, 5]
def baseStart_874529 : Nat := 118140960795 + 874529 * 2 ^ 59
def prefixEnd_874529 : Nat := 4983230072969 + 3 ^ 40 * 874529 * 2
def baseEnd_874529 : Nat := 99789716287980918881249

theorem tailTrace_874529 : CollatzResearch.WordTrace tailWord_874529 prefixEnd_874529 99789716287980918881249 := by
  unfold tailWord_874529
  simp only [CollatzResearch.WordTrace]
  refine ⟨31896693048738265507338641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21264462032492177004892427 31896693048738265507338641)
  ·
    refine ⟨23922519786553699130503981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31896693048738265507338641 23922519786553699130503981)
    ·
      refine ⟨8970944919957637173938993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23922519786553699130503981 8970944919957637173938993)
      ·
        refine ⟨6728208689968227880454245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8970944919957637173938993 6728208689968227880454245)
        ·
          refine ⟨1261539129369042727585171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6728208689968227880454245 1261539129369042727585171)
          ·
            refine ⟨1892308694053564091377757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1261539129369042727585171 1892308694053564091377757)
            ·
              refine ⟨709615760270086534266659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1892308694053564091377757 709615760270086534266659)
              ·
                refine ⟨1064423640405129801399989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 709615760270086534266659 1064423640405129801399989)
                ·
                  refine ⟨99789716287980918881249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1064423640405129801399989 99789716287980918881249)
                  ·
                    rfl

theorem cell22_874529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 3, 1, 5].length) (baseStart_874529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_874529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_874529 prefixEnd_874529 := by exact prefixLift 874529
  have htrace : WordTrace (prefixWord ++ tailWord_874529) baseStart_874529 baseEnd_874529 := by
    simpa [prefixWord, tailWord_874529, baseEnd_874529] using wordTrace_append hprefix tailTrace_874529
  have hstable : (prefixWord ++ tailWord_874529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874529).length < 2 ^ (prefixWord ++ tailWord_874529).sum := by decide
  have hdescent : baseEnd_874529 < baseStart_874529 := by decide
  rcases family_descends (prefixWord ++ tailWord_874529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874572 : List Nat := [2, 2, 1, 3, 1, 1, 4, 1, 4, 3]
def baseStart_874572 : Nat := 118140960795 + 874572 * 2 ^ 59
def prefixEnd_874572 : Nat := 4983230072969 + 3 ^ 40 * 874572 * 2
def baseEnd_874572 : Nat := 299383868642704977818615

theorem tailTrace_874572 : CollatzResearch.WordTrace tailWord_874572 prefixEnd_874572 299383868642704977818615 := by
  unfold tailWord_874572
  simp only [CollatzResearch.WordTrace]
  refine ⟨15949130693791241925576985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21265507591721655900769313 15949130693791241925576985)
  ·
    refine ⟨11961848020343431444182739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15949130693791241925576985 11961848020343431444182739)
    ·
      refine ⟨17942772030515147166274109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11961848020343431444182739 17942772030515147166274109)
      ·
        refine ⟨6728539511443180187352791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17942772030515147166274109 6728539511443180187352791)
        ·
          refine ⟨10092809267164770281029187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6728539511443180187352791 10092809267164770281029187)
          ·
            refine ⟨15139213900747155421543781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10092809267164770281029187 15139213900747155421543781)
            ·
              refine ⟨2838602606390091641539459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15139213900747155421543781 2838602606390091641539459)
              ·
                refine ⟨4257903909585137462309189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2838602606390091641539459 4257903909585137462309189)
                ·
                  refine ⟨798356983047213274182973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4257903909585137462309189 798356983047213274182973)
                  ·
                    refine ⟨299383868642704977818615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 798356983047213274182973 299383868642704977818615)
                    ·
                      rfl

theorem cell22_874572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 1, 4, 3].length) (baseStart_874572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_874572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_874572 prefixEnd_874572 := by exact prefixLift 874572
  have htrace : WordTrace (prefixWord ++ tailWord_874572) baseStart_874572 baseEnd_874572 := by
    simpa [prefixWord, tailWord_874572, baseEnd_874572] using wordTrace_append hprefix tailTrace_874572
  have hstable : (prefixWord ++ tailWord_874572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874572).length < 2 ^ (prefixWord ++ tailWord_874572).sum := by decide
  have hdescent : baseEnd_874572 < baseStart_874572 := by decide
  rcases family_descends (prefixWord ++ tailWord_874572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874585 : List Nat := [1, 2, 1, 2, 2, 1, 6, 7]
def baseStart_874585 : Nat := 118140960795 + 874585 * 2 ^ 59
def prefixEnd_874585 : Nat := 4983230072969 + 3 ^ 40 * 874585 * 2
def baseEnd_874585 : Nat := 33265368756486364138175

theorem tailTrace_874585 : CollatzResearch.WordTrace tailWord_874585 prefixEnd_874585 33265368756486364138175 := by
  unfold tailWord_874585
  simp only [CollatzResearch.WordTrace]
  refine ⟨31898735536535387071377209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21265823691023591380918139 31898735536535387071377209)
  ·
    refine ⟨23924051652401540303532907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31898735536535387071377209 23924051652401540303532907)
    ·
      refine ⟨35886077478602310455299361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23924051652401540303532907 35886077478602310455299361)
      ·
        refine ⟨26914558108951732841474521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35886077478602310455299361 26914558108951732841474521)
        ·
          refine ⟨20185918581713799631105891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26914558108951732841474521 20185918581713799631105891)
          ·
            refine ⟨30278877872570699446658837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20185918581713799631105891 30278877872570699446658837)
            ·
              refine ⟨1419322400276751536562133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 30278877872570699446658837 1419322400276751536562133)
              ·
                refine ⟨33265368756486364138175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1419322400276751536562133 33265368756486364138175)
                ·
                  rfl

theorem cell22_874585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 7].length) (baseStart_874585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_874585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_874585 prefixEnd_874585 := by exact prefixLift 874585
  have htrace : WordTrace (prefixWord ++ tailWord_874585) baseStart_874585 baseEnd_874585 := by
    simpa [prefixWord, tailWord_874585, baseEnd_874585] using wordTrace_append hprefix tailTrace_874585
  have hstable : (prefixWord ++ tailWord_874585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874585).length < 2 ^ (prefixWord ++ tailWord_874585).sum := by decide
  have hdescent : baseEnd_874585 < baseStart_874585 := by decide
  rcases family_descends (prefixWord ++ tailWord_874585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874632 : List Nat := [2, 1, 3, 4, 1, 1, 1, 1, 2, 6]
def baseStart_874632 : Nat := 118140960795 + 874632 * 2 ^ 59
def prefixEnd_874632 : Nat := 4983230072969 + 3 ^ 40 * 874632 * 2
def baseEnd_874632 : Nat := 299404407868884821318431

theorem tailTrace_874632 : CollatzResearch.WordTrace tailWord_874632 prefixEnd_874632 299404407868884821318431 := by
  unfold tailWord_874632
  simp only [CollatzResearch.WordTrace]
  refine ⟨15950224883682557049169075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21266966511576742732225433 15950224883682557049169075)
  ·
    refine ⟨23925337325523835573753613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15950224883682557049169075 23925337325523835573753613)
    ·
      refine ⟨8972001497071438340157605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23925337325523835573753613 8972001497071438340157605)
      ·
        refine ⟨1682250280700894688779551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8972001497071438340157605 1682250280700894688779551)
        ·
          refine ⟨2523375421051342033169327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1682250280700894688779551 2523375421051342033169327)
          ·
            refine ⟨3785063131577013049753991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2523375421051342033169327 3785063131577013049753991)
            ·
              refine ⟨5677594697365519574630987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3785063131577013049753991 5677594697365519574630987)
              ·
                refine ⟨8516392046048279361946481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5677594697365519574630987 8516392046048279361946481)
                ·
                  refine ⟨6387294034536209521459861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8516392046048279361946481 6387294034536209521459861)
                  ·
                    refine ⟨299404407868884821318431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6387294034536209521459861 299404407868884821318431)
                    ·
                      rfl

theorem cell22_874632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 2, 6].length) (baseStart_874632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_874632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_874632 prefixEnd_874632 := by exact prefixLift 874632
  have htrace : WordTrace (prefixWord ++ tailWord_874632) baseStart_874632 baseEnd_874632 := by
    simpa [prefixWord, tailWord_874632, baseEnd_874632] using wordTrace_append hprefix tailTrace_874632
  have hstable : (prefixWord ++ tailWord_874632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874632).length < 2 ^ (prefixWord ++ tailWord_874632).sum := by decide
  have hdescent : baseEnd_874632 < baseStart_874632 := by decide
  rcases family_descends (prefixWord ++ tailWord_874632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874675 : List Nat := [1, 1, 1, 2, 3, 2, 1, 1, 10]
def baseStart_874675 : Nat := 118140960795 + 874675 * 2 ^ 59
def prefixEnd_874675 : Nat := 4983230072969 + 3 ^ 40 * 874675 * 2
def baseEnd_874675 : Nat := 99806375882549014164433

theorem tailTrace_874675 : CollatzResearch.WordTrace tailWord_874675 prefixEnd_874675 99806375882549014164433 := by
  unfold tailWord_874675
  simp only [CollatzResearch.WordTrace]
  refine ⟨31902018106209332442153479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21268012070806221628102319 31902018106209332442153479)
  ·
    refine ⟨47853027159313998663230219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31902018106209332442153479 47853027159313998663230219)
    ·
      refine ⟨71779540738970997994845329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47853027159313998663230219 71779540738970997994845329)
      ·
        refine ⟨53834655554228248496133997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71779540738970997994845329 53834655554228248496133997)
        ·
          refine ⟨20187995832835593186050249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53834655554228248496133997 20187995832835593186050249)
          ·
            refine ⟨15140996874626694889537687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20187995832835593186050249 15140996874626694889537687)
            ·
              refine ⟨22711495311940042334306531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15140996874626694889537687 22711495311940042334306531)
              ·
                refine ⟨34067242967910063501459797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22711495311940042334306531 34067242967910063501459797)
                ·
                  refine ⟨99806375882549014164433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 34067242967910063501459797 99806375882549014164433)
                  ·
                    rfl

theorem cell22_874675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 10].length) (baseStart_874675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_874675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_874675 prefixEnd_874675 := by exact prefixLift 874675
  have htrace : WordTrace (prefixWord ++ tailWord_874675) baseStart_874675 baseEnd_874675 := by
    simpa [prefixWord, tailWord_874675, baseEnd_874675] using wordTrace_append hprefix tailTrace_874675
  have hstable : (prefixWord ++ tailWord_874675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874675).length < 2 ^ (prefixWord ++ tailWord_874675).sum := by decide
  have hdescent : baseEnd_874675 < baseStart_874675 := by decide
  rcases family_descends (prefixWord ++ tailWord_874675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874707 : List Nat := [1, 1, 1, 2, 1, 1, 1, 3, 8, 3]
def baseStart_874707 : Nat := 118140960795 + 874707 * 2 ^ 59
def prefixEnd_874707 : Nat := 4983230072969 + 3 ^ 40 * 874707 * 2
def baseEnd_874707 : Nat := 299430081901609625693201

theorem tailTrace_874707 : CollatzResearch.WordTrace tailWord_874707 prefixEnd_874707 299430081901609625693201 := by
  unfold tailWord_874707
  simp only [CollatzResearch.WordTrace]
  refine ⟨31903185242093401907318375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21268790161395601271545583 31903185242093401907318375)
  ·
    refine ⟨47854777863140102860977563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31903185242093401907318375 47854777863140102860977563)
    ·
      refine ⟨71782166794710154291466345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47854777863140102860977563 71782166794710154291466345)
      ·
        refine ⟨53836625096032615718599759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71782166794710154291466345 53836625096032615718599759)
        ·
          refine ⟨80754937644048923577899639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53836625096032615718599759 80754937644048923577899639)
          ·
            refine ⟨121132406466073385366849459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80754937644048923577899639 121132406466073385366849459)
            ·
              refine ⟨181698609699110078050274189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121132406466073385366849459 181698609699110078050274189)
              ·
                refine ⟨68136978637166279268852821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 181698609699110078050274189 68136978637166279268852821)
                ·
                  refine ⟨798480218404292335181869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 68136978637166279268852821 798480218404292335181869)
                  ·
                    refine ⟨299430081901609625693201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 798480218404292335181869 299430081901609625693201)
                    ·
                      rfl

theorem cell22_874707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 8, 3].length) (baseStart_874707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_874707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_874707 prefixEnd_874707 := by exact prefixLift 874707
  have htrace : WordTrace (prefixWord ++ tailWord_874707) baseStart_874707 baseEnd_874707 := by
    simpa [prefixWord, tailWord_874707, baseEnd_874707] using wordTrace_append hprefix tailTrace_874707
  have hstable : (prefixWord ++ tailWord_874707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874707).length < 2 ^ (prefixWord ++ tailWord_874707).sum := by decide
  have hdescent : baseEnd_874707 < baseStart_874707 := by decide
  rcases family_descends (prefixWord ++ tailWord_874707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874754 : List Nat := [3, 4, 1, 1, 2, 1, 1, 9]
def baseStart_874754 : Nat := 118140960795 + 874754 * 2 ^ 59
def prefixEnd_874754 : Nat := 4983230072969 + 3 ^ 40 * 874754 * 2
def baseEnd_874754 : Nat := 33271796773568574418673

theorem tailTrace_874754 : CollatzResearch.WordTrace tailWord_874754 prefixEnd_874754 33271796773568574418673 := by
  unfold tailWord_874754
  simp only [CollatzResearch.WordTrace]
  refine ⟨7976224868230782233569829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21269932981948752622852877 7976224868230782233569829)
  ·
    refine ⟨1495542162793271668794343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7976224868230782233569829 1495542162793271668794343)
    ·
      refine ⟨2243313244189907503191515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1495542162793271668794343 2243313244189907503191515)
      ·
        refine ⟨3364969866284861254787273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2243313244189907503191515 3364969866284861254787273)
        ·
          refine ⟨2523727399713645941090455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3364969866284861254787273 2523727399713645941090455)
          ·
            refine ⟨3785591099570468911635683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2523727399713645941090455 3785591099570468911635683)
            ·
              refine ⟨5678386649355703367453525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3785591099570468911635683 5678386649355703367453525)
              ·
                refine ⟨33271796773568574418673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5678386649355703367453525 33271796773568574418673)
                ·
                  rfl

theorem cell22_874754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 9].length) (baseStart_874754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_874754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_874754 prefixEnd_874754 := by exact prefixLift 874754
  have htrace : WordTrace (prefixWord ++ tailWord_874754) baseStart_874754 baseEnd_874754 := by
    simpa [prefixWord, tailWord_874754, baseEnd_874754] using wordTrace_append hprefix tailTrace_874754
  have hstable : (prefixWord ++ tailWord_874754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874754).length < 2 ^ (prefixWord ++ tailWord_874754).sum := by decide
  have hdescent : baseEnd_874754 < baseStart_874754 := by decide
  rcases family_descends (prefixWord ++ tailWord_874754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874814 : List Nat := [4, 2, 1, 2, 1, 2, 1, 1, 1, 7]
def baseStart_874814 : Nat := 118140960795 + 874814 * 2 ^ 59
def prefixEnd_874814 : Nat := 4983230072969 + 3 ^ 40 * 874814 * 2
def baseEnd_874814 : Nat := 299466710188297013267873

theorem tailTrace_874814 : CollatzResearch.WordTrace tailWord_874814 prefixEnd_874814 299466710188297013267873 := by
  unfold tailWord_874814
  simp only [CollatzResearch.WordTrace]
  refine ⟨3988385981588219897682937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21271391901803839454308997 3988385981588219897682937)
  ·
    refine ⟨2991289486191164923262203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3988385981588219897682937 2991289486191164923262203)
    ·
      refine ⟨4486934229286747384893305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2991289486191164923262203 4486934229286747384893305)
      ·
        refine ⟨3365200671965060538669979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4486934229286747384893305 3365200671965060538669979)
        ·
          refine ⟨5047801007947590808004969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3365200671965060538669979 5047801007947590808004969)
          ·
            refine ⟨3785850755960693106003727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5047801007947590808004969 3785850755960693106003727)
            ·
              refine ⟨5678776133941039659005591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3785850755960693106003727 5678776133941039659005591)
              ·
                refine ⟨8518164200911559488508387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5678776133941039659005591 8518164200911559488508387)
                ·
                  refine ⟨12777246301367339232762581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8518164200911559488508387 12777246301367339232762581)
                  ·
                    refine ⟨299466710188297013267873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12777246301367339232762581 299466710188297013267873)
                    ·
                      rfl

theorem cell22_874814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_874814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_874814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_874814 prefixEnd_874814 := by exact prefixLift 874814
  have htrace : WordTrace (prefixWord ++ tailWord_874814) baseStart_874814 baseEnd_874814 := by
    simpa [prefixWord, tailWord_874814, baseEnd_874814] using wordTrace_append hprefix tailTrace_874814
  have hstable : (prefixWord ++ tailWord_874814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874814).length < 2 ^ (prefixWord ++ tailWord_874814).sum := by decide
  have hdescent : baseEnd_874814 < baseStart_874814 := by decide
  rcases family_descends (prefixWord ++ tailWord_874814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874859 : List Nat := [1, 1, 1, 1, 2, 2, 2, 5, 4, 3]
def baseStart_874859 : Nat := 118140960795 + 874859 * 2 ^ 59
def prefixEnd_874859 : Nat := 4983230072969 + 3 ^ 40 * 874859 * 2
def baseEnd_874859 : Nat := 299482114607931895892735

theorem tailTrace_874859 : CollatzResearch.WordTrace tailWord_874859 prefixEnd_874859 299482114607931895892735 := by
  unfold tailWord_874859
  simp only [CollatzResearch.WordTrace]
  refine ⟨31908729137542731866851631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21272486091695154577901087 31908729137542731866851631)
  ·
    refine ⟨47863093706314097800277447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31908729137542731866851631 47863093706314097800277447)
    ·
      refine ⟨71794640559471146700416171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47863093706314097800277447 71794640559471146700416171)
      ·
        refine ⟨107691960839206720050624257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71794640559471146700416171 107691960839206720050624257)
        ·
          refine ⟨80768970629405040037968193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107691960839206720050624257 80768970629405040037968193)
          ·
            refine ⟨60576727972053780028476145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80768970629405040037968193 60576727972053780028476145)
            ·
              refine ⟨45432545979040335021357109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60576727972053780028476145 45432545979040335021357109)
              ·
                refine ⟨4259301185535031408252229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45432545979040335021357109 4259301185535031408252229)
                ·
                  refine ⟨798618972287818389047293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4259301185535031408252229 798618972287818389047293)
                  ·
                    refine ⟨299482114607931895892735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 798618972287818389047293 299482114607931895892735)
                    ·
                      rfl

theorem cell22_874859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5, 4, 3].length) (baseStart_874859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_874859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_874859 prefixEnd_874859 := by exact prefixLift 874859
  have htrace : WordTrace (prefixWord ++ tailWord_874859) baseStart_874859 baseEnd_874859 := by
    simpa [prefixWord, tailWord_874859, baseEnd_874859] using wordTrace_append hprefix tailTrace_874859
  have hstable : (prefixWord ++ tailWord_874859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874859).length < 2 ^ (prefixWord ++ tailWord_874859).sum := by decide
  have hdescent : baseEnd_874859 < baseStart_874859 := by decide
  rcases family_descends (prefixWord ++ tailWord_874859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874861 : List Nat := [1, 5, 1, 1, 1, 2, 1, 6, 4]
def baseStart_874861 : Nat := 118140960795 + 874861 * 2 ^ 59
def prefixEnd_874861 : Nat := 4983230072969 + 3 ^ 40 * 874861 * 2
def baseEnd_874861 : Nat := 99827599749601519114243

theorem tailTrace_874861 : CollatzResearch.WordTrace tailWord_874861 prefixEnd_874861 99827599749601519114243 := by
  unfold tailWord_874861
  simp only [CollatzResearch.WordTrace]
  refine ⟨31908802083535486208424437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21272534722356990805616291 31908802083535486208424437)
  ·
    refine ⟨2991450195331451832039791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31908802083535486208424437 2991450195331451832039791)
    ·
      refine ⟨4487175292997177748059687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2991450195331451832039791 4487175292997177748059687)
      ·
        refine ⟨6730762939495766622089531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4487175292997177748059687 6730762939495766622089531)
        ·
          refine ⟨10096144409243649933134297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6730762939495766622089531 10096144409243649933134297)
          ·
            refine ⟨7572108306932737449850723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10096144409243649933134297 7572108306932737449850723)
            ·
              refine ⟨11358162460399106174776085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7572108306932737449850723 11358162460399106174776085)
              ·
                refine ⟨532413865331208101942629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11358162460399106174776085 532413865331208101942629)
                ·
                  refine ⟨99827599749601519114243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 532413865331208101942629 99827599749601519114243)
                  ·
                    rfl

theorem cell22_874861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 6, 4].length) (baseStart_874861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_874861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_874861 prefixEnd_874861 := by exact prefixLift 874861
  have htrace : WordTrace (prefixWord ++ tailWord_874861) baseStart_874861 baseEnd_874861 := by
    simpa [prefixWord, tailWord_874861, baseEnd_874861] using wordTrace_append hprefix tailTrace_874861
  have hstable : (prefixWord ++ tailWord_874861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874861).length < 2 ^ (prefixWord ++ tailWord_874861).sum := by decide
  have hdescent : baseEnd_874861 < baseStart_874861 := by decide
  rcases family_descends (prefixWord ++ tailWord_874861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874889 : List Nat := [1, 2, 1, 1, 6, 2, 1, 8]
def baseStart_874889 : Nat := 118140960795 + 874889 * 2 ^ 59
def prefixEnd_874889 : Nat := 4983230072969 + 3 ^ 40 * 874889 * 2
def baseEnd_874889 : Nat := 33276931580113535293627

theorem tailTrace_874889 : CollatzResearch.WordTrace tailWord_874889 prefixEnd_874889 33276931580113535293627 := by
  unfold tailWord_874889
  simp only [CollatzResearch.WordTrace]
  refine ⟨31909823327434046990443721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21273215551622697993629147 31909823327434046990443721)
  ·
    refine ⟨23932367495575535242832791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31909823327434046990443721 23932367495575535242832791)
    ·
      refine ⟨35898551243363302864249187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23932367495575535242832791 35898551243363302864249187)
      ·
        refine ⟨53847826865044954296373781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35898551243363302864249187 53847826865044954296373781)
        ·
          refine ⟨2524116884298982232642521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 53847826865044954296373781 2524116884298982232642521)
          ·
            refine ⟨1893087663224236674481891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2524116884298982232642521 1893087663224236674481891)
            ·
              refine ⟨2839631494836355011722837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1893087663224236674481891 2839631494836355011722837)
              ·
                refine ⟨33276931580113535293627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2839631494836355011722837 33276931580113535293627)
                ·
                  rfl

theorem cell22_874889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 8].length) (baseStart_874889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_874889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_874889 prefixEnd_874889 := by exact prefixLift 874889
  have htrace : WordTrace (prefixWord ++ tailWord_874889) baseStart_874889 baseEnd_874889 := by
    simpa [prefixWord, tailWord_874889, baseEnd_874889] using wordTrace_append hprefix tailTrace_874889
  have hstable : (prefixWord ++ tailWord_874889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874889).length < 2 ^ (prefixWord ++ tailWord_874889).sum := by decide
  have hdescent : baseEnd_874889 < baseStart_874889 := by decide
  rcases family_descends (prefixWord ++ tailWord_874889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_874998 : List Nat := [5, 1, 1, 1, 2, 1, 2, 4, 1, 4]
def baseStart_874998 : Nat := 118140960795 + 874998 * 2 ^ 59
def prefixEnd_874998 : Nat := 4983230072969 + 3 ^ 40 * 874998 * 2
def baseEnd_874998 : Nat := 299529697148581866667309

theorem tailTrace_874998 : CollatzResearch.WordTrace tailWord_874998 prefixEnd_874998 299529697148581866667309 := by
  unfold tailWord_874998
  simp only [CollatzResearch.WordTrace]
  refine ⟨1994612430252447412885103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21275865922692772404107765 1994612430252447412885103)
  ·
    refine ⟨2991918645378671119327655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1994612430252447412885103 2991918645378671119327655)
    ·
      refine ⟨4487877968068006678991483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2991918645378671119327655 4487877968068006678991483)
      ·
        refine ⟨6731816952102010018487225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4487877968068006678991483 6731816952102010018487225)
        ·
          refine ⟨5048862714076507513865419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6731816952102010018487225 5048862714076507513865419)
          ·
            refine ⟨7573294071114761270798129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5048862714076507513865419 7573294071114761270798129)
            ·
              refine ⟨5679970553336070953098597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7573294071114761270798129 5679970553336070953098597)
              ·
                refine ⟨1064994478750513303705987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5679970553336070953098597 1064994478750513303705987)
                ·
                  refine ⟨1597491718125769955558981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1064994478750513303705987 1597491718125769955558981)
                  ·
                    refine ⟨299529697148581866667309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1597491718125769955558981 299529697148581866667309)
                    ·
                      rfl

theorem cell22_874998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_874998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_874998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_874998 prefixEnd_874998 := by exact prefixLift 874998
  have htrace : WordTrace (prefixWord ++ tailWord_874998) baseStart_874998 baseEnd_874998 := by
    simpa [prefixWord, tailWord_874998, baseEnd_874998] using wordTrace_append hprefix tailTrace_874998
  have hstable : (prefixWord ++ tailWord_874998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_874998).length < 2 ^ (prefixWord ++ tailWord_874998).sum := by decide
  have hdescent : baseEnd_874998 < baseStart_874998 := by decide
  rcases family_descends (prefixWord ++ tailWord_874998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875011 : List Nat := [1, 1, 1, 3, 2, 1, 4, 2, 4, 3]
def baseStart_875011 : Nat := 118140960795 + 875011 * 2 ^ 59
def prefixEnd_875011 : Nat := 4983230072969 + 3 ^ 40 * 875011 * 2
def baseEnd_875011 : Nat := 299534147314254166092269

theorem tailTrace_875011 : CollatzResearch.WordTrace tailWord_875011 prefixEnd_875011 299534147314254166092269 := by
  unfold tailWord_875011
  simp only [CollatzResearch.WordTrace]
  refine ⟨31914273032992061826384887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21276182021994707884256591 31914273032992061826384887)
  ·
    refine ⟨47871409549488092739577331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31914273032992061826384887 47871409549488092739577331)
    ·
      refine ⟨71807114324232139109365997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47871409549488092739577331 71807114324232139109365997)
      ·
        refine ⟨26927667871587052166012249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71807114324232139109365997 26927667871587052166012249)
        ·
          refine ⟨20195750903690289124509187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26927667871587052166012249 20195750903690289124509187)
          ·
            refine ⟨30293626355535433686763781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20195750903690289124509187 30293626355535433686763781)
            ·
              refine ⟨5680054941662893816268209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30293626355535433686763781 5680054941662893816268209)
              ·
                refine ⟨4260041206247170362201157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5680054941662893816268209 4260041206247170362201157)
                ·
                  refine ⟨798757726171344442912717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4260041206247170362201157 798757726171344442912717)
                  ·
                    refine ⟨299534147314254166092269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 798757726171344442912717 299534147314254166092269)
                    ·
                      rfl

theorem cell22_875011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2, 4, 3].length) (baseStart_875011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_875011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_875011 prefixEnd_875011 := by exact prefixLift 875011
  have htrace : WordTrace (prefixWord ++ tailWord_875011) baseStart_875011 baseEnd_875011 := by
    simpa [prefixWord, tailWord_875011, baseEnd_875011] using wordTrace_append hprefix tailTrace_875011
  have hstable : (prefixWord ++ tailWord_875011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875011).length < 2 ^ (prefixWord ++ tailWord_875011).sum := by decide
  have hdescent : baseEnd_875011 < baseStart_875011 := by decide
  rcases family_descends (prefixWord ++ tailWord_875011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875086 : List Nat := [4, 1, 1, 1, 1, 2, 4, 1, 7]
def baseStart_875086 : Nat := 118140960795 + 875086 * 2 ^ 59
def prefixEnd_875086 : Nat := 4983230072969 + 3 ^ 40 * 875086 * 2
def baseEnd_875086 : Nat := 99853273782326323489013

theorem tailTrace_875086 : CollatzResearch.WordTrace tailWord_875086 prefixEnd_875086 99853273782326323489013 := by
  unfold tailWord_875086
  simp only [CollatzResearch.WordTrace]
  refine ⟨3989626063465043704420639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21278005671813566423576741 3989626063465043704420639)
  ·
    refine ⟨5984439095197565556630959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3989626063465043704420639 5984439095197565556630959)
    ·
      refine ⟨8976658642796348334946439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5984439095197565556630959 8976658642796348334946439)
      ·
        refine ⟨13464987964194522502419659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8976658642796348334946439 13464987964194522502419659)
        ·
          refine ⟨20197481946291783753629489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13464987964194522502419659 20197481946291783753629489)
          ·
            refine ⟨15148111459718837815222117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20197481946291783753629489 15148111459718837815222117)
            ·
              refine ⟨2840270898697282090354147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15148111459718837815222117 2840270898697282090354147)
              ·
                refine ⟨4260406348045923135531221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2840270898697282090354147 4260406348045923135531221)
                ·
                  refine ⟨99853273782326323489013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4260406348045923135531221 99853273782326323489013)
                  ·
                    rfl

theorem cell22_875086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 1, 7].length) (baseStart_875086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_875086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_875086 prefixEnd_875086 := by exact prefixLift 875086
  have htrace : WordTrace (prefixWord ++ tailWord_875086) baseStart_875086 baseEnd_875086 := by
    simpa [prefixWord, tailWord_875086, baseEnd_875086] using wordTrace_append hprefix tailTrace_875086
  have hstable : (prefixWord ++ tailWord_875086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875086).length < 2 ^ (prefixWord ++ tailWord_875086).sum := by decide
  have hdescent : baseEnd_875086 < baseStart_875086 := by decide
  rcases family_descends (prefixWord ++ tailWord_875086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875161 : List Nat := [1, 2, 1, 2, 1, 2, 4, 2, 1, 6]
def baseStart_875161 : Nat := 118140960795 + 875161 * 2 ^ 59
def prefixEnd_875161 : Nat := 4983230072969 + 3 ^ 40 * 875161 * 2
def baseEnd_875161 : Nat := 299585495379703774841809

theorem tailTrace_875161 : CollatzResearch.WordTrace tailWord_875161 prefixEnd_875161 299585495379703774841809 := by
  unfold tailWord_875161
  simp only [CollatzResearch.WordTrace]
  refine ⟨31919743982448637444345337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21279829321632424962896891 31919743982448637444345337)
  ·
    refine ⟨23939807986836478083259003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31919743982448637444345337 23939807986836478083259003)
    ·
      refine ⟨35909711980254717124888505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23939807986836478083259003 35909711980254717124888505)
      ·
        refine ⟨26932283985191037843666379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35909711980254717124888505 26932283985191037843666379)
        ·
          refine ⟨40398425977786556765499569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26932283985191037843666379 40398425977786556765499569)
          ·
            refine ⟨30298819483339917574124677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40398425977786556765499569 30298819483339917574124677)
            ·
              refine ⟨5681028653126234545148377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30298819483339917574124677 5681028653126234545148377)
              ·
                refine ⟨4260771489844675908861283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5681028653126234545148377 4260771489844675908861283)
                ·
                  refine ⟨6391157234767013863291925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4260771489844675908861283 6391157234767013863291925)
                  ·
                    refine ⟨299585495379703774841809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6391157234767013863291925 299585495379703774841809)
                    ·
                      rfl

theorem cell22_875161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2, 1, 6].length) (baseStart_875161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_875161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_875161 prefixEnd_875161 := by exact prefixLift 875161
  have htrace : WordTrace (prefixWord ++ tailWord_875161) baseStart_875161 baseEnd_875161 := by
    simpa [prefixWord, tailWord_875161, baseEnd_875161] using wordTrace_append hprefix tailTrace_875161
  have hstable : (prefixWord ++ tailWord_875161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875161).length < 2 ^ (prefixWord ++ tailWord_875161).sum := by decide
  have hdescent : baseEnd_875161 < baseStart_875161 := by decide
  rcases family_descends (prefixWord ++ tailWord_875161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875182 : List Nat := [4, 1, 4, 1, 1, 1, 1, 5, 4]
def baseStart_875182 : Nat := 118140960795 + 875182 * 2 ^ 59
def prefixEnd_875182 : Nat := 4983230072969 + 3 ^ 40 * 875182 * 2
def baseEnd_875182 : Nat := 99864228036288906688915

theorem tailTrace_875182 : CollatzResearch.WordTrace tailWord_875182 prefixEnd_875182 99864228036288906688915 := by
  unfold tailWord_875182
  simp only [CollatzResearch.WordTrace]
  refine ⟨3990063739421569753857475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21280339943581705353906533 3990063739421569753857475)
  ·
    refine ⟨5985095609132354630786213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3990063739421569753857475 5985095609132354630786213)
    ·
      refine ⟨1122205426712316493272415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5985095609132354630786213 1122205426712316493272415)
      ·
        refine ⟨1683308140068474739908623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1122205426712316493272415 1683308140068474739908623)
        ·
          refine ⟨2524962210102712109862935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1683308140068474739908623 2524962210102712109862935)
          ·
            refine ⟨3787443315154068164794403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2524962210102712109862935 3787443315154068164794403)
            ·
              refine ⟨5681164972731102247191605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3787443315154068164794403 5681164972731102247191605)
              ·
                refine ⟨532609216193540835674213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5681164972731102247191605 532609216193540835674213)
                ·
                  refine ⟨99864228036288906688915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 532609216193540835674213 99864228036288906688915)
                  ·
                    rfl

theorem cell22_875182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 5, 4].length) (baseStart_875182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_875182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_875182 prefixEnd_875182 := by exact prefixLift 875182
  have htrace : WordTrace (prefixWord ++ tailWord_875182) baseStart_875182 baseEnd_875182 := by
    simpa [prefixWord, tailWord_875182, baseEnd_875182] using wordTrace_append hprefix tailTrace_875182
  have hstable : (prefixWord ++ tailWord_875182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875182).length < 2 ^ (prefixWord ++ tailWord_875182).sum := by decide
  have hdescent : baseEnd_875182 < baseStart_875182 := by decide
  rcases family_descends (prefixWord ++ tailWord_875182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875197 : List Nat := [1, 4, 1, 2, 1, 5, 1, 2, 2, 3]
def baseStart_875197 : Nat := 118140960795 + 875197 * 2 ^ 59
def prefixEnd_875197 : Nat := 4983230072969 + 3 ^ 40 * 875197 * 2
def baseEnd_875197 : Nat := 299597818915411680941699

theorem tailTrace_875197 : CollatzResearch.WordTrace tailWord_875197 prefixEnd_875197 299597818915411680941699 := by
  unfold tailWord_875197
  simp only [CollatzResearch.WordTrace]
  refine ⟨31921057010318215592655845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21280704673545477061770563 31921057010318215592655845)
  ·
    refine ⟨5985198189434665423622971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31921057010318215592655845 5985198189434665423622971)
    ·
      refine ⟨8977797284151998135434457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5985198189434665423622971 8977797284151998135434457)
      ·
        refine ⟨6733347963113998601575843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8977797284151998135434457 6733347963113998601575843)
        ·
          refine ⟨10100021944670997902363765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6733347963113998601575843 10100021944670997902363765)
          ·
            refine ⟨946877057312906053346603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10100021944670997902363765 946877057312906053346603)
            ·
              refine ⟨1420315585969359080019905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 946877057312906053346603 1420315585969359080019905)
              ·
                refine ⟨1065236689477019310014929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1420315585969359080019905 1065236689477019310014929)
                ·
                  refine ⟨798927517107764482511197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1065236689477019310014929 798927517107764482511197)
                  ·
                    refine ⟨299597818915411680941699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 798927517107764482511197 299597818915411680941699)
                    ·
                      rfl

theorem cell22_875197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 2, 2, 3].length) (baseStart_875197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_875197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_875197 prefixEnd_875197 := by exact prefixLift 875197
  have htrace : WordTrace (prefixWord ++ tailWord_875197) baseStart_875197 baseEnd_875197 := by
    simpa [prefixWord, tailWord_875197, baseEnd_875197] using wordTrace_append hprefix tailTrace_875197
  have hstable : (prefixWord ++ tailWord_875197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875197).length < 2 ^ (prefixWord ++ tailWord_875197).sum := by decide
  have hdescent : baseEnd_875197 < baseStart_875197 := by decide
  rcases family_descends (prefixWord ++ tailWord_875197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875272 : List Nat := [2, 1, 3, 2, 2, 4, 2, 1, 5]
def baseStart_875272 : Nat := 118140960795 + 875272 * 2 ^ 59
def prefixEnd_875272 : Nat := 4983230072969 + 3 ^ 40 * 875272 * 2
def baseEnd_875272 : Nat := 99874497649378828438823

theorem tailTrace_875272 : CollatzResearch.WordTrace tailWord_875272 prefixEnd_875272 99874497649378828438823 := by
  unfold tailWord_875272
  simp only [CollatzResearch.WordTrace]
  refine ⟨15961896242523251700818035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21282528323364335601090713 15961896242523251700818035)
  ·
    refine ⟨23942844363784877551227053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15961896242523251700818035 23942844363784877551227053)
    ·
      refine ⟨8978566636419329081710145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23942844363784877551227053 8978566636419329081710145)
      ·
        refine ⟨6733924977314496811282609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8978566636419329081710145 6733924977314496811282609)
        ·
          refine ⟨5050443732985872608461957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6733924977314496811282609 5050443732985872608461957)
          ·
            refine ⟨946958199934851114086617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5050443732985872608461957 946958199934851114086617)
            ·
              refine ⟨710218649951138335564963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 946958199934851114086617 710218649951138335564963)
              ·
                refine ⟨1065327974926707503347445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 710218649951138335564963 1065327974926707503347445)
                ·
                  refine ⟨99874497649378828438823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1065327974926707503347445 99874497649378828438823)
                  ·
                    rfl

theorem cell22_875272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 2, 1, 5].length) (baseStart_875272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_875272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_875272 prefixEnd_875272 := by exact prefixLift 875272
  have htrace : WordTrace (prefixWord ++ tailWord_875272) baseStart_875272 baseEnd_875272 := by
    simpa [prefixWord, tailWord_875272, baseEnd_875272] using wordTrace_append hprefix tailTrace_875272
  have hstable : (prefixWord ++ tailWord_875272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875272).length < 2 ^ (prefixWord ++ tailWord_875272).sum := by decide
  have hdescent : baseEnd_875272 < baseStart_875272 := by decide
  rcases family_descends (prefixWord ++ tailWord_875272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875317 : List Nat := [1, 3, 3, 1, 3, 2, 1, 4, 4]
def baseStart_875317 : Nat := 118140960795 + 875317 * 2 ^ 59
def prefixEnd_875317 : Nat := 4983230072969 + 3 ^ 40 * 875317 * 2
def baseEnd_875317 : Nat := 99879632455923789313777

theorem tailTrace_875317 : CollatzResearch.WordTrace tailWord_875317 prefixEnd_875317 99879632455923789313777 := by
  unfold tailWord_875317
  simp only [CollatzResearch.WordTrace]
  refine ⟨31925433769883476087024205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21283622513255650724682803 31925433769883476087024205)
  ·
    refine ⟨11972037663706303532634077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31925433769883476087024205 11972037663706303532634077)
    ·
      refine ⟨4489514123889863824737779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11972037663706303532634077 4489514123889863824737779)
      ·
        refine ⟨6734271185834795737106669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4489514123889863824737779 6734271185834795737106669)
        ·
          refine ⟨2525351694688048401415001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6734271185834795737106669 2525351694688048401415001)
          ·
            refine ⟨1894013771016036301061251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2525351694688048401415001 1894013771016036301061251)
            ·
              refine ⟨2841020656524054451591877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1894013771016036301061251 2841020656524054451591877)
              ·
                refine ⟨532691373098260209673477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2841020656524054451591877 532691373098260209673477)
                ·
                  refine ⟨99879632455923789313777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 532691373098260209673477 99879632455923789313777)
                  ·
                    rfl

theorem cell22_875317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 4, 4].length) (baseStart_875317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_875317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_875317 prefixEnd_875317 := by exact prefixLift 875317
  have htrace : WordTrace (prefixWord ++ tailWord_875317) baseStart_875317 baseEnd_875317 := by
    simpa [prefixWord, tailWord_875317, baseEnd_875317] using wordTrace_append hprefix tailTrace_875317
  have hstable : (prefixWord ++ tailWord_875317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875317).length < 2 ^ (prefixWord ++ tailWord_875317).sum := by decide
  have hdescent : baseEnd_875317 < baseStart_875317 := by decide
  rcases family_descends (prefixWord ++ tailWord_875317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875334 : List Nat := [6, 1, 1, 2, 2, 1, 1, 2, 6]
def baseStart_875334 : Nat := 118140960795 + 875334 * 2 ^ 59
def prefixEnd_875334 : Nat := 4983230072969 + 3 ^ 40 * 875334 * 2
def baseEnd_875334 : Nat := 99881572271729663422093

theorem tailTrace_875334 : CollatzResearch.WordTrace tailWord_875334 prefixEnd_875334 99881572271729663422093 := by
  unfold tailWord_875334
  simp only [CollatzResearch.WordTrace]
  refine ⟨997689181588183999699783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 21284035873881258660262037 997689181588183999699783)
  ·
    refine ⟨1496533772382275999549675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 997689181588183999699783 1496533772382275999549675)
    ·
      refine ⟨2244800658573413999324513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1496533772382275999549675 2244800658573413999324513)
      ·
        refine ⟨1683600493930060499493385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2244800658573413999324513 1683600493930060499493385)
        ·
          refine ⟨1262700370447545374620039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1683600493930060499493385 1262700370447545374620039)
          ·
            refine ⟨1894050555671318061930059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1262700370447545374620039 1894050555671318061930059)
            ·
              refine ⟨2841075833506977092895089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1894050555671318061930059 2841075833506977092895089)
              ·
                refine ⟨2130806875130232819671317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2841075833506977092895089 2130806875130232819671317)
                ·
                  refine ⟨99881572271729663422093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2130806875130232819671317 99881572271729663422093)
                  ·
                    rfl

theorem cell22_875334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_875334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_875334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_875334 prefixEnd_875334 := by exact prefixLift 875334
  have htrace : WordTrace (prefixWord ++ tailWord_875334) baseStart_875334 baseEnd_875334 := by
    simpa [prefixWord, tailWord_875334, baseEnd_875334] using wordTrace_append hprefix tailTrace_875334
  have hstable : (prefixWord ++ tailWord_875334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875334).length < 2 ^ (prefixWord ++ tailWord_875334).sum := by decide
  have hdescent : baseEnd_875334 < baseStart_875334 := by decide
  rcases family_descends (prefixWord ++ tailWord_875334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875360 : List Nat := [2, 1, 1, 3, 3, 1, 1, 2, 5, 3]
def baseStart_875360 : Nat := 118140960795 + 875360 * 2 ^ 59
def prefixEnd_875360 : Nat := 4983230072969 + 3 ^ 40 * 875360 * 2
def baseEnd_875360 : Nat := 299653617146533589116199

theorem tailTrace_875360 : CollatzResearch.WordTrace tailWord_875360 prefixEnd_875360 299653617146533589116199 := by
  unfold tailWord_875360
  simp only [CollatzResearch.WordTrace]
  refine ⟨15963501054363847215419767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21284668072485129620559689 15963501054363847215419767)
  ·
    refine ⟨23945251581545770823129651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15963501054363847215419767 23945251581545770823129651)
    ·
      refine ⟨35917877372318656234694477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23945251581545770823129651 35917877372318656234694477)
      ·
        refine ⟨13469204014619496088010429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35917877372318656234694477 13469204014619496088010429)
        ·
          refine ⟨5050951505482311033003911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13469204014619496088010429 5050951505482311033003911)
          ·
            refine ⟨7576427258223466549505867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5050951505482311033003911 7576427258223466549505867)
            ·
              refine ⟨11364640887335199824258801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7576427258223466549505867 11364640887335199824258801)
              ·
                refine ⟨8523480665501399868194101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11364640887335199824258801 8523480665501399868194101)
                ·
                  refine ⟨799076312390756237643197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8523480665501399868194101 799076312390756237643197)
                  ·
                    refine ⟨299653617146533589116199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 799076312390756237643197 299653617146533589116199)
                    ·
                      rfl

theorem cell22_875360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 5, 3].length) (baseStart_875360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_875360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_875360 prefixEnd_875360 := by exact prefixLift 875360
  have htrace : WordTrace (prefixWord ++ tailWord_875360) baseStart_875360 baseEnd_875360 := by
    simpa [prefixWord, tailWord_875360, baseEnd_875360] using wordTrace_append hprefix tailTrace_875360
  have hstable : (prefixWord ++ tailWord_875360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875360).length < 2 ^ (prefixWord ++ tailWord_875360).sum := by decide
  have hdescent : baseEnd_875360 < baseStart_875360 := by decide
  rcases family_descends (prefixWord ++ tailWord_875360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875377 : List Nat := [1, 2, 2, 2, 1, 5, 2, 1, 3, 3]
def baseStart_875377 : Nat := 118140960795 + 875377 * 2 ^ 59
def prefixEnd_875377 : Nat := 4983230072969 + 3 ^ 40 * 875377 * 2
def baseEnd_875377 : Nat := 299659436593951211441147

theorem tailTrace_875377 : CollatzResearch.WordTrace tailWord_875377 prefixEnd_875377 299659436593951211441147 := by
  unfold tailWord_875377
  simp only [CollatzResearch.WordTrace]
  refine ⟨31927622149666106334208385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21285081433110737556138923 31927622149666106334208385)
  ·
    refine ⟨23945716612249579750656289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31927622149666106334208385 23945716612249579750656289)
    ·
      refine ⟨17959287459187184812992217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23945716612249579750656289 17959287459187184812992217)
      ·
        refine ⟨13469465594390388609744163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17959287459187184812992217 13469465594390388609744163)
        ·
          refine ⟨20204198391585582914616245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13469465594390388609744163 20204198391585582914616245)
          ·
            refine ⟨1894143599211148398245273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20204198391585582914616245 1894143599211148398245273)
            ·
              refine ⟨1420607699408361298683955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1894143599211148398245273 1420607699408361298683955)
              ·
                refine ⟨2130911549112541948025933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1420607699408361298683955 2130911549112541948025933)
                ·
                  refine ⟨799091830917203230509725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2130911549112541948025933 799091830917203230509725)
                  ·
                    refine ⟨299659436593951211441147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 799091830917203230509725 299659436593951211441147)
                    ·
                      rfl

theorem cell22_875377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 1, 3, 3].length) (baseStart_875377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_875377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_875377 prefixEnd_875377 := by exact prefixLift 875377
  have htrace : WordTrace (prefixWord ++ tailWord_875377) baseStart_875377 baseEnd_875377 := by
    simpa [prefixWord, tailWord_875377, baseEnd_875377] using wordTrace_append hprefix tailTrace_875377
  have hstable : (prefixWord ++ tailWord_875377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875377).length < 2 ^ (prefixWord ++ tailWord_875377).sum := by decide
  have hdescent : baseEnd_875377 < baseStart_875377 := by decide
  rcases family_descends (prefixWord ++ tailWord_875377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875441 : List Nat := [1, 2, 2, 4, 4, 1, 2, 1, 5]
def baseStart_875441 : Nat := 118140960795 + 875441 * 2 ^ 59
def prefixEnd_875441 : Nat := 4983230072969 + 3 ^ 40 * 875441 * 2
def baseEnd_875441 : Nat := 99893781700625459280317

theorem tailTrace_875441 : CollatzResearch.WordTrace tailWord_875441 prefixEnd_875441 99893781700625459280317 := by
  unfold tailWord_875441
  simp only [CollatzResearch.WordTrace]
  refine ⟨31929956421434245264538177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21286637614289496843025451 31929956421434245264538177)
  ·
    refine ⟨23947467316075683948403633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31929956421434245264538177 23947467316075683948403633)
    ·
      refine ⟨17960600487056762961302725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23947467316075683948403633 17960600487056762961302725)
      ·
        refine ⟨3367612591323143055244261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17960600487056762961302725 3367612591323143055244261)
        ·
          refine ⟨631427360873089322858299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3367612591323143055244261 631427360873089322858299)
          ·
            refine ⟨947141041309633984287449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 631427360873089322858299 947141041309633984287449)
            ·
              refine ⟨710355780982225488215587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 947141041309633984287449 710355780982225488215587)
              ·
                refine ⟨1065533671473338232323381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 710355780982225488215587 1065533671473338232323381)
                ·
                  refine ⟨99893781700625459280317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1065533671473338232323381 99893781700625459280317)
                  ·
                    rfl

theorem cell22_875441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 2, 1, 5].length) (baseStart_875441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_875441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_875441 prefixEnd_875441 := by exact prefixLift 875441
  have htrace : WordTrace (prefixWord ++ tailWord_875441) baseStart_875441 baseEnd_875441 := by
    simpa [prefixWord, tailWord_875441, baseEnd_875441] using wordTrace_append hprefix tailTrace_875441
  have hstable : (prefixWord ++ tailWord_875441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875441).length < 2 ^ (prefixWord ++ tailWord_875441).sum := by decide
  have hdescent : baseEnd_875441 < baseStart_875441 := by decide
  rcases family_descends (prefixWord ++ tailWord_875441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875450 : List Nat := [3, 1, 1, 1, 2, 1, 4, 3, 1, 5]
def baseStart_875450 : Nat := 118140960795 + 875450 * 2 ^ 59
def prefixEnd_875450 : Nat := 4983230072969 + 3 ^ 40 * 875450 * 2
def baseEnd_875450 : Nat := 299684425985803354365923

theorem tailTrace_875450 : CollatzResearch.WordTrace tailWord_875450 prefixEnd_875450 299684425985803354365923 := by
  unfold tailWord_875450
  simp only [CollatzResearch.WordTrace]
  refine ⟨7982571169600409950403951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21286856452267759867743869 7982571169600409950403951)
  ·
    refine ⟨11973856754400614925605927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7982571169600409950403951 11973856754400614925605927)
    ·
      refine ⟨17960785131600922388408891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11973856754400614925605927 17960785131600922388408891)
      ·
        refine ⟨26941177697401383582613337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17960785131600922388408891 26941177697401383582613337)
        ·
          refine ⟨20205883273051037686960003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26941177697401383582613337 20205883273051037686960003)
          ·
            refine ⟨30308824909576556530440005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20205883273051037686960003 30308824909576556530440005)
            ·
              refine ⟨5682904670545604349457501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30308824909576556530440005 5682904670545604349457501)
              ·
                refine ⟨2131089251454601631046563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5682904670545604349457501 2131089251454601631046563)
                ·
                  refine ⟨3196633877181902446569845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2131089251454601631046563 3196633877181902446569845)
                  ·
                    refine ⟨299684425985803354365923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3196633877181902446569845 299684425985803354365923)
                    ·
                      rfl

theorem cell22_875450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 3, 1, 5].length) (baseStart_875450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_875450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_875450 prefixEnd_875450 := by exact prefixLift 875450
  have htrace : WordTrace (prefixWord ++ tailWord_875450) baseStart_875450 baseEnd_875450 := by
    simpa [prefixWord, tailWord_875450, baseEnd_875450] using wordTrace_append hprefix tailTrace_875450
  have hstable : (prefixWord ++ tailWord_875450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875450).length < 2 ^ (prefixWord ++ tailWord_875450).sum := by decide
  have hdescent : baseEnd_875450 < baseStart_875450 := by decide
  rcases family_descends (prefixWord ++ tailWord_875450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875482 : List Nat := [3, 1, 1, 2, 4, 1, 2, 2, 2, 4]
def baseStart_875482 : Nat := 118140960795 + 875482 * 2 ^ 59
def prefixEnd_875482 : Nat := 4983230072969 + 3 ^ 40 * 875482 * 2
def baseEnd_875482 : Nat := 299695380239765937565825

theorem tailTrace_875482 : CollatzResearch.WordTrace tailWord_875482 prefixEnd_875482 299695380239765937565825 := by
  unfold tailWord_875482
  simp only [CollatzResearch.WordTrace]
  refine ⟨7982862953571427316695175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21287634542857139511187133 7982862953571427316695175)
  ·
    refine ⟨11974294430357140975042763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7982862953571427316695175 11974294430357140975042763)
    ·
      refine ⟨17961441645535711462564145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11974294430357140975042763 17961441645535711462564145)
      ·
        refine ⟨13471081234151783596923109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17961441645535711462564145 13471081234151783596923109)
        ·
          refine ⟨2525827731403459424423083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13471081234151783596923109 2525827731403459424423083)
          ·
            refine ⟨3788741597105189136634625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2525827731403459424423083 3788741597105189136634625)
            ·
              refine ⟨2841556197828891852475969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3788741597105189136634625 2841556197828891852475969)
              ·
                refine ⟨2131167148371668889356977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2841556197828891852475969 2131167148371668889356977)
                ·
                  refine ⟨1598375361278751667017733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2131167148371668889356977 1598375361278751667017733)
                  ·
                    refine ⟨299695380239765937565825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1598375361278751667017733 299695380239765937565825)
                    ·
                      rfl

theorem cell22_875482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 2, 2, 4].length) (baseStart_875482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_875482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_875482 prefixEnd_875482 := by exact prefixLift 875482
  have htrace : WordTrace (prefixWord ++ tailWord_875482) baseStart_875482 baseEnd_875482 := by
    simpa [prefixWord, tailWord_875482, baseEnd_875482] using wordTrace_append hprefix tailTrace_875482
  have hstable : (prefixWord ++ tailWord_875482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875482).length < 2 ^ (prefixWord ++ tailWord_875482).sum := by decide
  have hdescent : baseEnd_875482 < baseStart_875482 := by decide
  rcases family_descends (prefixWord ++ tailWord_875482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875525 : List Nat := [1, 3, 1, 1, 2, 3, 2, 2, 7]
def baseStart_875525 : Nat := 118140960795 + 875525 * 2 ^ 59
def prefixEnd_875525 : Nat := 4983230072969 + 3 ^ 40 * 875525 * 2
def baseEnd_875525 : Nat := 99903366672842719580231

theorem tailTrace_875525 : CollatzResearch.WordTrace tailWord_875525 prefixEnd_875525 99903366672842719580231 := by
  unfold tailWord_875525
  simp only [CollatzResearch.WordTrace]
  refine ⟨31933020153129927610596029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21288680102086618407064019 31933020153129927610596029)
  ·
    refine ⟨11974882557423722853973511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31933020153129927610596029 11974882557423722853973511)
    ·
      refine ⟨17962323836135584280960267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11974882557423722853973511 17962323836135584280960267)
      ·
        refine ⟨26943485754203376421440401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17962323836135584280960267 26943485754203376421440401)
        ·
          refine ⟨20207614315652532316080301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26943485754203376421440401 20207614315652532316080301)
          ·
            refine ⟨7577855368369699618530113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20207614315652532316080301 7577855368369699618530113)
            ·
              refine ⟨5683391526277274713897585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7577855368369699618530113 5683391526277274713897585)
              ·
                refine ⟨4262543644707956035423189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5683391526277274713897585 4262543644707956035423189)
                ·
                  refine ⟨99903366672842719580231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4262543644707956035423189 99903366672842719580231)
                  ·
                    rfl

theorem cell22_875525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2, 7].length) (baseStart_875525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_875525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_875525 prefixEnd_875525 := by exact prefixLift 875525
  have htrace : WordTrace (prefixWord ++ tailWord_875525) baseStart_875525 baseEnd_875525 := by
    simpa [prefixWord, tailWord_875525, baseEnd_875525] using wordTrace_append hprefix tailTrace_875525
  have hstable : (prefixWord ++ tailWord_875525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875525).length < 2 ^ (prefixWord ++ tailWord_875525).sum := by decide
  have hdescent : baseEnd_875525 < baseStart_875525 := by decide
  rcases family_descends (prefixWord ++ tailWord_875525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875604 : List Nat := [2, 4, 1, 1, 1, 1, 2, 6, 4]
def baseStart_875604 : Nat := 118140960795 + 875604 * 2 ^ 59
def prefixEnd_875604 : Nat := 4983230072969 + 3 ^ 40 * 875604 * 2
def baseEnd_875604 : Nat := 99912381110999428671817

theorem tailTrace_875604 : CollatzResearch.WordTrace tailWord_875604 prefixEnd_875604 99912381110999428671817 := by
  unfold tailWord_875604
  simp only [CollatzResearch.WordTrace]
  refine ⟨15967950759921862051360933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21290601013229149401814577 15967950759921862051360933)
  ·
    refine ⟨2993990767485349134630175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15967950759921862051360933 2993990767485349134630175)
    ·
      refine ⟨4490986151228023701945263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2993990767485349134630175 4490986151228023701945263)
      ·
        refine ⟨6736479226842035552917895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4490986151228023701945263 6736479226842035552917895)
        ·
          refine ⟨10104718840263053329376843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6736479226842035552917895 10104718840263053329376843)
          ·
            refine ⟨15157078260394579994065265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10104718840263053329376843 15157078260394579994065265)
            ·
              refine ⟨11367808695295934995548949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15157078260394579994065265 11367808695295934995548949)
              ·
                refine ⟨532866032591996952916357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11367808695295934995548949 532866032591996952916357)
                ·
                  refine ⟨99912381110999428671817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 532866032591996952916357 99912381110999428671817)
                  ·
                    rfl

theorem cell22_875604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 6, 4].length) (baseStart_875604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_875604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_875604 prefixEnd_875604 := by exact prefixLift 875604
  have htrace : WordTrace (prefixWord ++ tailWord_875604) baseStart_875604 baseEnd_875604 := by
    simpa [prefixWord, tailWord_875604, baseEnd_875604] using wordTrace_append hprefix tailTrace_875604
  have hstable : (prefixWord ++ tailWord_875604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875604).length < 2 ^ (prefixWord ++ tailWord_875604).sum := by decide
  have hdescent : baseEnd_875604 < baseStart_875604 := by decide
  rcases family_descends (prefixWord ++ tailWord_875604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875634 : List Nat := [3, 2, 1, 2, 2, 1, 4, 1, 2, 4]
def baseStart_875634 : Nat := 118140960795 + 875634 * 2 ^ 59
def prefixEnd_875634 : Nat := 4983230072969 + 3 ^ 40 * 875634 * 2
def baseEnd_875634 : Nat := 299747412946088207765359

theorem tailTrace_875634 : CollatzResearch.WordTrace tailWord_875634 prefixEnd_875634 299747412946088207765359 := by
  unfold tailWord_875634
  simp only [CollatzResearch.WordTrace]
  refine ⟨7984248927433759806578489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21291330473156692817542637 7984248927433759806578489)
  ·
    refine ⟨5988186695575319854933867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7984248927433759806578489 5988186695575319854933867)
    ·
      refine ⟨8982280043362979782400801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5988186695575319854933867 8982280043362979782400801)
      ·
        refine ⟨6736710032522234836800601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8982280043362979782400801 6736710032522234836800601)
        ·
          refine ⟨5052532524391676127600451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6736710032522234836800601 5052532524391676127600451)
          ·
            refine ⟨7578798786587514191400677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5052532524391676127600451 7578798786587514191400677)
            ·
              refine ⟨1421024772485158910887627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7578798786587514191400677 1421024772485158910887627)
              ·
                refine ⟨2131537158727738366331441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1421024772485158910887627 2131537158727738366331441)
                ·
                  refine ⟨1598652869045803774748581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2131537158727738366331441 1598652869045803774748581)
                  ·
                    refine ⟨299747412946088207765359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1598652869045803774748581 299747412946088207765359)
                    ·
                      rfl

theorem cell22_875634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 1, 2, 4].length) (baseStart_875634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_875634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_875634 prefixEnd_875634 := by exact prefixLift 875634
  have htrace : WordTrace (prefixWord ++ tailWord_875634) baseStart_875634 baseEnd_875634 := by
    simpa [prefixWord, tailWord_875634, baseEnd_875634] using wordTrace_append hprefix tailTrace_875634
  have hstable : (prefixWord ++ tailWord_875634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875634).length < 2 ^ (prefixWord ++ tailWord_875634).sum := by decide
  have hdescent : baseEnd_875634 < baseStart_875634 := by decide
  rcases family_descends (prefixWord ++ tailWord_875634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875698 : List Nat := [3, 2, 1, 1, 1, 5, 2, 3, 1, 3]
def baseStart_875698 : Nat := 118140960795 + 875698 * 2 ^ 59
def prefixEnd_875698 : Nat := 4983230072969 + 3 ^ 40 * 875698 * 2
def baseEnd_875698 : Nat := 299769321454013374165163

theorem tailTrace_875698 : CollatzResearch.WordTrace tailWord_875698 prefixEnd_875698 299769321454013374165163 := by
  unfold tailWord_875698
  simp only [CollatzResearch.WordTrace]
  refine ⟨7984832495375794539160937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21292886654335452104429165 7984832495375794539160937)
  ·
    refine ⟨5988624371531845904370703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7984832495375794539160937 5988624371531845904370703)
    ·
      refine ⟨8982936557297768856556055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5988624371531845904370703 8982936557297768856556055)
      ·
        refine ⟨13474404835946653284834083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8982936557297768856556055 13474404835946653284834083)
        ·
          refine ⟨20211607253919979927251125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13474404835946653284834083 20211607253919979927251125)
          ·
            refine ⟨1894838180054998118179793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20211607253919979927251125 1894838180054998118179793)
            ·
              refine ⟨1421128635041248588634845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1894838180054998118179793 1421128635041248588634845)
              ·
                refine ⟨532923238140468220738067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1421128635041248588634845 532923238140468220738067)
                ·
                  refine ⟨799384857210702331107101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 532923238140468220738067 799384857210702331107101)
                  ·
                    refine ⟨299769321454013374165163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 799384857210702331107101 299769321454013374165163)
                    ·
                      rfl

theorem cell22_875698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 3, 1, 3].length) (baseStart_875698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_875698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_875698 prefixEnd_875698 := by exact prefixLift 875698
  have htrace : WordTrace (prefixWord ++ tailWord_875698) baseStart_875698 baseEnd_875698 := by
    simpa [prefixWord, tailWord_875698, baseEnd_875698] using wordTrace_append hprefix tailTrace_875698
  have hstable : (prefixWord ++ tailWord_875698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875698).length < 2 ^ (prefixWord ++ tailWord_875698).sum := by decide
  have hdescent : baseEnd_875698 < baseStart_875698 := by decide
  rcases family_descends (prefixWord ++ tailWord_875698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875707 : List Nat := [1, 1, 1, 1, 1, 2, 4, 2, 5, 4]
def baseStart_875707 : Nat := 118140960795 + 875707 * 2 ^ 59
def prefixEnd_875707 : Nat := 4983230072969 + 3 ^ 40 * 875707 * 2
def baseEnd_875707 : Nat := 299772402337940350690135

theorem tailTrace_875707 : CollatzResearch.WordTrace tailWord_875707 prefixEnd_875707 299772402337940350690135 := by
  unfold tailWord_875707
  simp only [CollatzResearch.WordTrace]
  refine ⟨31939658238470572693721375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21293105492313715129147583 31939658238470572693721375)
  ·
    refine ⟨47909487357705859040582063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31939658238470572693721375 47909487357705859040582063)
    ·
      refine ⟨71864231036558788560873095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47909487357705859040582063 71864231036558788560873095)
      ·
        refine ⟨107796346554838182841309643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71864231036558788560873095 107796346554838182841309643)
        ·
          refine ⟨161694519832257274261964465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107796346554838182841309643 161694519832257274261964465)
          ·
            refine ⟨121270889874192955696473349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161694519832257274261964465 121270889874192955696473349)
            ·
              refine ⟨22738291851411179193088753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121270889874192955696473349 22738291851411179193088753)
              ·
                refine ⟨17053718888558384394816565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22738291851411179193088753 17053718888558384394816565)
                ·
                  refine ⟨1598786145802348537014053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17053718888558384394816565 1598786145802348537014053)
                  ·
                    refine ⟨299772402337940350690135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1598786145802348537014053 299772402337940350690135)
                    ·
                      rfl

theorem cell22_875707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 5, 4].length) (baseStart_875707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_875707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_875707 prefixEnd_875707 := by exact prefixLift 875707
  have htrace : WordTrace (prefixWord ++ tailWord_875707) baseStart_875707 baseEnd_875707 := by
    simpa [prefixWord, tailWord_875707, baseEnd_875707] using wordTrace_append hprefix tailTrace_875707
  have hstable : (prefixWord ++ tailWord_875707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875707).length < 2 ^ (prefixWord ++ tailWord_875707).sum := by decide
  have hdescent : baseEnd_875707 < baseStart_875707 := by decide
  rcases family_descends (prefixWord ++ tailWord_875707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875756 : List Nat := [2, 2, 1, 1, 2, 4, 3, 3, 4]
def baseStart_875756 : Nat := 118140960795 + 875756 * 2 ^ 59
def prefixEnd_875756 : Nat := 4983230072969 + 3 ^ 40 * 875756 * 2
def baseEnd_875756 : Nat := 99929725346440185404995

theorem tailTrace_875756 : CollatzResearch.WordTrace tailWord_875756 prefixEnd_875756 99929725346440185404995 := by
  unfold tailWord_875756
  simp only [CollatzResearch.WordTrace]
  refine ⟨15970722707646527031127561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21294296943528702708170081 15970722707646527031127561)
  ·
    refine ⟨11978042030734895273345671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15970722707646527031127561 11978042030734895273345671)
    ·
      refine ⟨17967063046102342910018507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11978042030734895273345671 17967063046102342910018507)
      ·
        refine ⟨26950594569153514365027761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17967063046102342910018507 26950594569153514365027761)
        ·
          refine ⟨20212945926865135773770821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26950594569153514365027761 20212945926865135773770821)
          ·
            refine ⟨3789927361287212957582029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20212945926865135773770821 3789927361287212957582029)
            ·
              refine ⟨1421222760482704859093261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3789927361287212957582029 1421222760482704859093261)
              ·
                refine ⟨532958535181014322159973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1421222760482704859093261 532958535181014322159973)
                ·
                  refine ⟨99929725346440185404995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 532958535181014322159973 99929725346440185404995)
                  ·
                    rfl

theorem cell22_875756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 3, 4].length) (baseStart_875756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_875756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_875756 prefixEnd_875756 := by exact prefixLift 875756
  have htrace : WordTrace (prefixWord ++ tailWord_875756) baseStart_875756 baseEnd_875756 := by
    simpa [prefixWord, tailWord_875756, baseEnd_875756] using wordTrace_append hprefix tailTrace_875756
  have hstable : (prefixWord ++ tailWord_875756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875756).length < 2 ^ (prefixWord ++ tailWord_875756).sum := by decide
  have hdescent : baseEnd_875756 < baseStart_875756 := by decide
  rcases family_descends (prefixWord ++ tailWord_875756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875769 : List Nat := [1, 2, 1, 3, 1, 1, 5, 2, 2, 4]
def baseStart_875769 : Nat := 118140960795 + 875769 * 2 ^ 59
def prefixEnd_875769 : Nat := 4983230072969 + 3 ^ 40 * 875769 * 2
def baseEnd_875769 : Nat := 299793626204992855639945

theorem tailTrace_875769 : CollatzResearch.WordTrace tailWord_875769 prefixEnd_875769 299793626204992855639945 := by
  unfold tailWord_875769
  simp only [CollatzResearch.WordTrace]
  refine ⟨31941919564245957282478361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21294613042830638188318907 31941919564245957282478361)
  ·
    refine ⟨23956439673184467961858771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31941919564245957282478361 23956439673184467961858771)
    ·
      refine ⟨35934659509776701942788157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23956439673184467961858771 35934659509776701942788157)
      ·
        refine ⟨13475497316166263228545559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35934659509776701942788157 13475497316166263228545559)
        ·
          refine ⟨20213245974249394842818339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13475497316166263228545559 20213245974249394842818339)
          ·
            refine ⟨30319868961374092264227509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20213245974249394842818339 30319868961374092264227509)
            ·
              refine ⟨2842487715128821149771329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30319868961374092264227509 2842487715128821149771329)
              ·
                refine ⟨2131865786346615862328497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2842487715128821149771329 2131865786346615862328497)
                ·
                  refine ⟨1598899339759961896746373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2131865786346615862328497 1598899339759961896746373)
                  ·
                    refine ⟨299793626204992855639945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1598899339759961896746373 299793626204992855639945)
                    ·
                      rfl

theorem cell22_875769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 2, 2, 4].length) (baseStart_875769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_875769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_875769 prefixEnd_875769 := by exact prefixLift 875769
  have htrace : WordTrace (prefixWord ++ tailWord_875769) baseStart_875769 baseEnd_875769 := by
    simpa [prefixWord, tailWord_875769, baseEnd_875769] using wordTrace_append hprefix tailTrace_875769
  have hstable : (prefixWord ++ tailWord_875769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875769).length < 2 ^ (prefixWord ++ tailWord_875769).sum := by decide
  have hdescent : baseEnd_875769 < baseStart_875769 := by decide
  rcases family_descends (prefixWord ++ tailWord_875769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875788 : List Nat := [2, 2, 1, 2, 2, 3, 4, 1, 2, 3]
def baseStart_875788 : Nat := 118140960795 + 875788 * 2 ^ 59
def prefixEnd_875788 : Nat := 4983230072969 + 3 ^ 40 * 875788 * 2
def baseEnd_875788 : Nat := 299800130293283139414887

theorem tailTrace_875788 : CollatzResearch.WordTrace tailWord_875788 prefixEnd_875788 299800130293283139414887 := by
  unfold tailWord_875788
  simp only [CollatzResearch.WordTrace]
  refine ⟨15971306275588561763710009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21295075034118082351613345 15971306275588561763710009)
  ·
    refine ⟨11978479706691421322782507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15971306275588561763710009 11978479706691421322782507)
    ·
      refine ⟨17967719560037131984173761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11978479706691421322782507 17967719560037131984173761)
      ·
        refine ⟨13475789670027848988130321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17967719560037131984173761 13475789670027848988130321)
        ·
          refine ⟨10106842252520886741097741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13475789670027848988130321 10106842252520886741097741)
          ·
            refine ⟨3790065844695332527911653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10106842252520886741097741 3790065844695332527911653)
            ·
              refine ⟨710637345880374848983435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3790065844695332527911653 710637345880374848983435)
              ·
                refine ⟨1065956018820562273475153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 710637345880374848983435 1065956018820562273475153)
                ·
                  refine ⟨799467014115421705106365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1065956018820562273475153 799467014115421705106365)
                  ·
                    refine ⟨299800130293283139414887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 799467014115421705106365 299800130293283139414887)
                    ·
                      rfl

theorem cell22_875788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 4, 1, 2, 3].length) (baseStart_875788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_875788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_875788 prefixEnd_875788 := by exact prefixLift 875788
  have htrace : WordTrace (prefixWord ++ tailWord_875788) baseStart_875788 baseEnd_875788 := by
    simpa [prefixWord, tailWord_875788, baseEnd_875788] using wordTrace_append hprefix tailTrace_875788
  have hstable : (prefixWord ++ tailWord_875788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875788).length < 2 ^ (prefixWord ++ tailWord_875788).sum := by decide
  have hdescent : baseEnd_875788 < baseStart_875788 := by decide
  rcases family_descends (prefixWord ++ tailWord_875788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875859 : List Nat := [1, 1, 1, 2, 1, 1, 5, 3, 3, 4]
def baseStart_875859 : Nat := 118140960795 + 875859 * 2 ^ 59
def prefixEnd_875859 : Nat := 4983230072969 + 3 ^ 40 * 875859 * 2
def baseEnd_875859 : Nat := 299824435044262620889669

theorem tailTrace_875859 : CollatzResearch.WordTrace tailWord_875859 prefixEnd_875859 299824435044262620889669 := by
  unfold tailWord_875859
  simp only [CollatzResearch.WordTrace]
  refine ⟨31945202133919902653254631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21296801422613268435503087 31945202133919902653254631)
  ·
    refine ⟨47917803200879853979881947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31945202133919902653254631 47917803200879853979881947)
    ·
      refine ⟨71876704801319780969822921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47917803200879853979881947 71876704801319780969822921)
      ·
        refine ⟨53907528600989835727367191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71876704801319780969822921 53907528600989835727367191)
        ·
          refine ⟨80861292901484753591050787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53907528600989835727367191 80861292901484753591050787)
          ·
            refine ⟨121291939352227130386576181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80861292901484753591050787 121291939352227130386576181)
            ·
              refine ⟨11371119314271293473741517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 121291939352227130386576181 11371119314271293473741517)
              ·
                refine ⟨4264169742851735052653069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11371119314271293473741517 4264169742851735052653069)
                ·
                  refine ⟨1599063653569400644744901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4264169742851735052653069 1599063653569400644744901)
                  ·
                    refine ⟨299824435044262620889669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1599063653569400644744901 299824435044262620889669)
                    ·
                      rfl

theorem cell22_875859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3, 3, 4].length) (baseStart_875859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_875859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_875859 prefixEnd_875859 := by exact prefixLift 875859
  have htrace : WordTrace (prefixWord ++ tailWord_875859) baseStart_875859 baseEnd_875859 := by
    simpa [prefixWord, tailWord_875859, baseEnd_875859] using wordTrace_append hprefix tailTrace_875859
  have hstable : (prefixWord ++ tailWord_875859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875859).length < 2 ^ (prefixWord ++ tailWord_875859).sum := by decide
  have hdescent : baseEnd_875859 < baseStart_875859 := by decide
  rcases family_descends (prefixWord ++ tailWord_875859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875880 : List Nat := [2, 1, 4, 2, 4, 1, 1, 2, 5]
def baseStart_875880 : Nat := 118140960795 + 875880 * 2 ^ 59
def prefixEnd_875880 : Nat := 4983230072969 + 3 ^ 40 * 875880 * 2
def baseEnd_875880 : Nat := 99943874591141855371535

theorem tailTrace_875880 : CollatzResearch.WordTrace tailWord_875880 prefixEnd_875880 99943874591141855371535 := by
  unfold tailWord_875880
  simp only [CollatzResearch.WordTrace]
  refine ⟨15972984033421911619884547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21297312044562548826512729 15972984033421911619884547)
  ·
    refine ⟨23959476050132867429826821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15972984033421911619884547 23959476050132867429826821)
    ·
      refine ⟨4492401759399912643092529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23959476050132867429826821 4492401759399912643092529)
      ·
        refine ⟨3369301319549934482319397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4492401759399912643092529 3369301319549934482319397)
        ·
          refine ⟨631743997415612715434887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3369301319549934482319397 631743997415612715434887)
          ·
            refine ⟨947615996123419073152331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 631743997415612715434887 947615996123419073152331)
            ·
              refine ⟨1421423994185128609728497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 947615996123419073152331 1421423994185128609728497)
              ·
                refine ⟨1066067995638846457296373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1421423994185128609728497 1066067995638846457296373)
                ·
                  refine ⟨99943874591141855371535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1066067995638846457296373 99943874591141855371535)
                  ·
                    rfl

theorem cell22_875880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 2, 5].length) (baseStart_875880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_875880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_875880 prefixEnd_875880 := by exact prefixLift 875880
  have htrace : WordTrace (prefixWord ++ tailWord_875880) baseStart_875880 baseEnd_875880 := by
    simpa [prefixWord, tailWord_875880, baseEnd_875880] using wordTrace_append hprefix tailTrace_875880
  have hstable : (prefixWord ++ tailWord_875880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875880).length < 2 ^ (prefixWord ++ tailWord_875880).sum := by decide
  have hdescent : baseEnd_875880 < baseStart_875880 := by decide
  rcases family_descends (prefixWord ++ tailWord_875880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875889 : List Nat := [1, 2, 2, 2, 1, 2, 2, 2, 3, 5]
def baseStart_875889 : Nat := 118140960795 + 875889 * 2 ^ 59
def prefixEnd_875889 : Nat := 4983230072969 + 3 ^ 40 * 875889 * 2
def baseEnd_875889 : Nat := 299834704657352542639577

theorem tailTrace_875889 : CollatzResearch.WordTrace tailWord_875889 prefixEnd_875889 299834704657352542639577 := by
  unfold tailWord_875889
  simp only [CollatzResearch.WordTrace]
  refine ⟨31946296323811217776846721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21297530882540811851231147 31946296323811217776846721)
  ·
    refine ⟨23959722242858413332635041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31946296323811217776846721 23959722242858413332635041)
    ·
      refine ⟨17969791682143809999476281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23959722242858413332635041 17969791682143809999476281)
      ·
        refine ⟨13477343761607857499607211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17969791682143809999476281 13477343761607857499607211)
        ·
          refine ⟨20216015642411786249410817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13477343761607857499607211 20216015642411786249410817)
          ·
            refine ⟨15162011731808839687058113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20216015642411786249410817 15162011731808839687058113)
            ·
              refine ⟨11371508798856629765293585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15162011731808839687058113 11371508798856629765293585)
              ·
                refine ⟨8528631599142472323970189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11371508798856629765293585 8528631599142472323970189)
                ·
                  refine ⟨3198236849678427121488821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8528631599142472323970189 3198236849678427121488821)
                  ·
                    refine ⟨299834704657352542639577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3198236849678427121488821 299834704657352542639577)
                    ·
                      rfl

theorem cell22_875889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 3, 5].length) (baseStart_875889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_875889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_875889 prefixEnd_875889 := by exact prefixLift 875889
  have htrace : WordTrace (prefixWord ++ tailWord_875889) baseStart_875889 baseEnd_875889 := by
    simpa [prefixWord, tailWord_875889, baseEnd_875889] using wordTrace_append hprefix tailTrace_875889
  have hstable : (prefixWord ++ tailWord_875889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875889).length < 2 ^ (prefixWord ++ tailWord_875889).sum := by decide
  have hdescent : baseEnd_875889 < baseStart_875889 := by decide
  rcases family_descends (prefixWord ++ tailWord_875889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875938 : List Nat := [3, 3, 1, 2, 1, 3, 1, 2, 2, 4]
def baseStart_875938 : Nat := 118140960795 + 875938 * 2 ^ 59
def prefixEnd_875938 : Nat := 4983230072969 + 3 ^ 40 * 875938 * 2
def baseEnd_875938 : Nat := 299851478358732748164427

theorem tailTrace_875938 : CollatzResearch.WordTrace tailWord_875938 prefixEnd_875938 299851478358732748164427 := by
  unfold tailWord_875938
  simp only [CollatzResearch.WordTrace]
  refine ⟨7987020875158424786345117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21298722333755799430253645 7987020875158424786345117)
  ·
    refine ⟨2995132828184409294879419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7987020875158424786345117 2995132828184409294879419)
    ·
      refine ⟨4492699242276613942319129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2995132828184409294879419 4492699242276613942319129)
      ·
        refine ⟨3369524431707460456739347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4492699242276613942319129 3369524431707460456739347)
        ·
          refine ⟨5054286647561190685109021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3369524431707460456739347 5054286647561190685109021)
          ·
            refine ⟨1895357492835446506915883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5054286647561190685109021 1895357492835446506915883)
            ·
              refine ⟨2843036239253169760373825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1895357492835446506915883 2843036239253169760373825)
              ·
                refine ⟨2132277179439877320280369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2843036239253169760373825 2132277179439877320280369)
                ·
                  refine ⟨1599207884579907990210277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2132277179439877320280369 1599207884579907990210277)
                  ·
                    refine ⟨299851478358732748164427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1599207884579907990210277 299851478358732748164427)
                    ·
                      rfl

theorem cell22_875938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_875938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_875938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_875938 prefixEnd_875938 := by exact prefixLift 875938
  have htrace : WordTrace (prefixWord ++ tailWord_875938) baseStart_875938 baseEnd_875938 := by
    simpa [prefixWord, tailWord_875938, baseEnd_875938] using wordTrace_append hprefix tailTrace_875938
  have hstable : (prefixWord ++ tailWord_875938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875938).length < 2 ^ (prefixWord ++ tailWord_875938).sum := by decide
  have hdescent : baseEnd_875938 < baseStart_875938 := by decide
  rcases family_descends (prefixWord ++ tailWord_875938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_875957 : List Nat := [1, 3, 3, 2, 2, 3, 2, 1, 2, 3]
def baseStart_875957 : Nat := 118140960795 + 875957 * 2 ^ 59
def prefixEnd_875957 : Nat := 4983230072969 + 3 ^ 40 * 875957 * 2
def baseEnd_875957 : Nat := 299857982447023031939369

theorem tailTrace_875957 : CollatzResearch.WordTrace tailWord_875957 prefixEnd_875957 299857982447023031939369 := by
  unfold tailWord_875957
  simp only [CollatzResearch.WordTrace]
  refine ⟨31948776487564865390322125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21299184325043243593548083 31948776487564865390322125)
  ·
    refine ⟨11980791182836824521370797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31948776487564865390322125 11980791182836824521370797)
    ·
      refine ⟨4492796693563809195514049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11980791182836824521370797 4492796693563809195514049)
      ·
        refine ⟨3369597520172856896635537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4492796693563809195514049 3369597520172856896635537)
        ·
          refine ⟨2527198140129642672476653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3369597520172856896635537 2527198140129642672476653)
          ·
            refine ⟨947699302548616002178745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2527198140129642672476653 947699302548616002178745)
            ·
              refine ⟨710774476911462001634059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 947699302548616002178745 710774476911462001634059)
              ·
                refine ⟨1066161715367193002451089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 710774476911462001634059 1066161715367193002451089)
                ·
                  refine ⟨799621286525394751838317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1066161715367193002451089 799621286525394751838317)
                  ·
                    refine ⟨299857982447023031939369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 799621286525394751838317 299857982447023031939369)
                    ·
                      rfl

theorem cell22_875957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 2, 1, 2, 3].length) (baseStart_875957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_875957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_875957 prefixEnd_875957 := by exact prefixLift 875957
  have htrace : WordTrace (prefixWord ++ tailWord_875957) baseStart_875957 baseEnd_875957 := by
    simpa [prefixWord, tailWord_875957, baseEnd_875957] using wordTrace_append hprefix tailTrace_875957
  have hstable : (prefixWord ++ tailWord_875957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_875957).length < 2 ^ (prefixWord ++ tailWord_875957).sum := by decide
  have hdescent : baseEnd_875957 < baseStart_875957 := by decide
  rcases family_descends (prefixWord ++ tailWord_875957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876026 : List Nat := [3, 1, 1, 1, 1, 2, 5, 2, 6]
def baseStart_876026 : Nat := 118140960795 + 876026 * 2 ^ 59
def prefixEnd_876026 : Nat := 4983230072969 + 3 ^ 40 * 876026 * 2
def baseEnd_876026 : Nat := 99960534185709950654719

theorem tailTrace_876026 : CollatzResearch.WordTrace tailWord_876026 prefixEnd_876026 99960534185709950654719 := by
  unfold tailWord_876026
  simp only [CollatzResearch.WordTrace]
  refine ⟨7987823281078722543645983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21300862082876593449722621 7987823281078722543645983)
  ·
    refine ⟨11981734921618083815468975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7987823281078722543645983 11981734921618083815468975)
    ·
      refine ⟨17972602382427125723203463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11981734921618083815468975 17972602382427125723203463)
      ·
        refine ⟨26958903573640688584805195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17972602382427125723203463 26958903573640688584805195)
        ·
          refine ⟨40438355360461032877207793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26958903573640688584805195 40438355360461032877207793)
          ·
            refine ⟨30328766520345774657905845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40438355360461032877207793 30328766520345774657905845)
            ·
              refine ⟨2843321861282416374178673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30328766520345774657905845 2843321861282416374178673)
              ·
                refine ⟨2132491395961812280634005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2843321861282416374178673 2132491395961812280634005)
                ·
                  refine ⟨99960534185709950654719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2132491395961812280634005 99960534185709950654719)
                  ·
                    rfl

theorem cell22_876026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 2, 6].length) (baseStart_876026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_876026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_876026 prefixEnd_876026 := by exact prefixLift 876026
  have htrace : WordTrace (prefixWord ++ tailWord_876026) baseStart_876026 baseEnd_876026 := by
    simpa [prefixWord, tailWord_876026, baseEnd_876026] using wordTrace_append hprefix tailTrace_876026
  have hstable : (prefixWord ++ tailWord_876026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876026).length < 2 ^ (prefixWord ++ tailWord_876026).sum := by decide
  have hdescent : baseEnd_876026 < baseStart_876026 := by decide
  rcases family_descends (prefixWord ++ tailWord_876026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876041 : List Nat := [1, 2, 1, 1, 3, 1, 3, 4, 1, 5]
def baseStart_876041 : Nat := 118140960795 + 876041 * 2 ^ 59
def prefixEnd_876041 : Nat := 4983230072969 + 3 ^ 40 * 876041 * 2
def baseEnd_876041 : Nat := 299886737363674812839111

theorem tailTrace_876041 : CollatzResearch.WordTrace tailWord_876041 prefixEnd_876041 299886737363674812839111 := by
  unfold tailWord_876041
  simp only [CollatzResearch.WordTrace]
  refine ⟨31951840219260547736379977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21301226812840365157586651 31951840219260547736379977)
  ·
    refine ⟨23963880164445410802284983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31951840219260547736379977 23963880164445410802284983)
    ·
      refine ⟨35945820246668116203427475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23963880164445410802284983 35945820246668116203427475)
      ·
        refine ⟨53918730370002174305141213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35945820246668116203427475 53918730370002174305141213)
        ·
          refine ⟨20219523888750815364427955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53918730370002174305141213 20219523888750815364427955)
          ·
            refine ⟨30329285833126223046641933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20219523888750815364427955 30329285833126223046641933)
            ·
              refine ⟨11373482187422333642490725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30329285833126223046641933 11373482187422333642490725)
              ·
                refine ⟨2132527910141687557967011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11373482187422333642490725 2132527910141687557967011)
                ·
                  refine ⟨3198791865212531336950517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2132527910141687557967011 3198791865212531336950517)
                  ·
                    refine ⟨299886737363674812839111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3198791865212531336950517 299886737363674812839111)
                    ·
                      rfl

theorem cell22_876041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 4, 1, 5].length) (baseStart_876041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_876041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_876041 prefixEnd_876041 := by exact prefixLift 876041
  have htrace : WordTrace (prefixWord ++ tailWord_876041) baseStart_876041 baseEnd_876041 := by
    simpa [prefixWord, tailWord_876041, baseEnd_876041] using wordTrace_append hprefix tailTrace_876041
  have hstable : (prefixWord ++ tailWord_876041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876041).length < 2 ^ (prefixWord ++ tailWord_876041).sum := by decide
  have hdescent : baseEnd_876041 < baseStart_876041 := by decide
  rcases family_descends (prefixWord ++ tailWord_876041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876088 : List Nat := [2, 1, 2, 1, 4, 2, 4, 6]
def baseStart_876088 : Nat := 118140960795 + 876088 * 2 ^ 59
def prefixEnd_876088 : Nat := 4983230072969 + 3 ^ 40 * 876088 * 2
def baseEnd_876088 : Nat := 33322536269353595212663

theorem tailTrace_876088 : CollatzResearch.WordTrace tailWord_876088 prefixEnd_876088 33322536269353595212663 := by
  unfold tailWord_876088
  simp only [CollatzResearch.WordTrace]
  refine ⟨15976777225045137381670459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21302369633393516508893945 15976777225045137381670459)
  ·
    refine ⟨23965165837567706072505689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15976777225045137381670459 23965165837567706072505689)
    ·
      refine ⟨17973874378175779554379267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23965165837567706072505689 17973874378175779554379267)
      ·
        refine ⟨26960811567263669331568901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17973874378175779554379267 26960811567263669331568901)
        ·
          refine ⟨5055152168861937999669169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26960811567263669331568901 5055152168861937999669169)
          ·
            refine ⟨3791364126646453499751877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5055152168861937999669169 3791364126646453499751877)
            ·
              refine ⟨710880773746210031203477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3791364126646453499751877 710880773746210031203477)
              ·
                refine ⟨33322536269353595212663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 710880773746210031203477 33322536269353595212663)
                ·
                  rfl

theorem cell22_876088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 4, 6].length) (baseStart_876088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_876088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_876088 prefixEnd_876088 := by exact prefixLift 876088
  have htrace : WordTrace (prefixWord ++ tailWord_876088) baseStart_876088 baseEnd_876088 := by
    simpa [prefixWord, tailWord_876088, baseEnd_876088] using wordTrace_append hprefix tailTrace_876088
  have hstable : (prefixWord ++ tailWord_876088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876088).length < 2 ^ (prefixWord ++ tailWord_876088).sum := by decide
  have hdescent : baseEnd_876088 < baseStart_876088 := by decide
  rcases family_descends (prefixWord ++ tailWord_876088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876214 : List Nat := [5, 1, 3, 1, 1, 2, 1, 3, 1, 4]
def baseStart_876214 : Nat := 118140960795 + 876214 * 2 ^ 59
def prefixEnd_876214 : Nat := 4983230072969 + 3 ^ 40 * 876214 * 2
def baseEnd_876214 : Nat := 299945958799160028263581

theorem tailTrace_876214 : CollatzResearch.WordTrace tailWord_876214 prefixEnd_876214 299945958799160028263581 := by
  unfold tailWord_876214
  simp only [CollatzResearch.WordTrace]
  refine ⟨1997384377977112392651731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21305433365089198854951797 1997384377977112392651731)
  ·
    refine ⟨2996076566965668588977597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1997384377977112392651731 2996076566965668588977597)
    ·
      refine ⟨1123528712612125720866599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2996076566965668588977597 1123528712612125720866599)
      ·
        refine ⟨1685293068918188581299899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1123528712612125720866599 1685293068918188581299899)
        ·
          refine ⟨2527939603377282871949849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1685293068918188581299899 2527939603377282871949849)
          ·
            refine ⟨1895954702532962153962387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2527939603377282871949849 1895954702532962153962387)
            ·
              refine ⟨2843932053799443230943581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1895954702532962153962387 2843932053799443230943581)
              ·
                refine ⟨1066474520174791211603843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2843932053799443230943581 1066474520174791211603843)
                ·
                  refine ⟨1599711780262186817405765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1066474520174791211603843 1599711780262186817405765)
                  ·
                    refine ⟨299945958799160028263581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1599711780262186817405765 299945958799160028263581)
                    ·
                      rfl

theorem cell22_876214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_876214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_876214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_876214 prefixEnd_876214 := by exact prefixLift 876214
  have htrace : WordTrace (prefixWord ++ tailWord_876214) baseStart_876214 baseEnd_876214 := by
    simpa [prefixWord, tailWord_876214, baseEnd_876214] using wordTrace_append hprefix tailTrace_876214
  have hstable : (prefixWord ++ tailWord_876214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876214).length < 2 ^ (prefixWord ++ tailWord_876214).sum := by decide
  have hdescent : baseEnd_876214 < baseStart_876214 := by decide
  rcases family_descends (prefixWord ++ tailWord_876214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876255 : List Nat := [1, 1, 2, 3, 2, 2, 1, 4, 3, 3]
def baseStart_876255 : Nat := 118140960795 + 876255 * 2 ^ 59
def prefixEnd_876255 : Nat := 4983230072969 + 3 ^ 40 * 876255 * 2
def baseEnd_876255 : Nat := 299959993937049587988455

theorem tailTrace_876255 : CollatzResearch.WordTrace tailWord_876255 prefixEnd_876255 299959993937049587988455 := by
  unfold tailWord_876255
  simp only [CollatzResearch.WordTrace]
  refine ⟨31959645440485262284670219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21306430293656841523113479 31959645440485262284670219)
  ·
    refine ⟨47939468160727893427005329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31959645440485262284670219 47939468160727893427005329)
    ·
      refine ⟨35954601120545920070253997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47939468160727893427005329 35954601120545920070253997)
      ·
        refine ⟨13482975420204720026345249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35954601120545920070253997 13482975420204720026345249)
        ·
          refine ⟨10112231565153540019758937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13482975420204720026345249 10112231565153540019758937)
          ·
            refine ⟨7584173673865155014819203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10112231565153540019758937 7584173673865155014819203)
            ·
              refine ⟨11376260510797732522228805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7584173673865155014819203 11376260510797732522228805)
              ·
                refine ⟨2133048845774574847917901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11376260510797732522228805 2133048845774574847917901)
                ·
                  refine ⟨799893317165465567969213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2133048845774574847917901 799893317165465567969213)
                  ·
                    refine ⟨299959993937049587988455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 799893317165465567969213 299959993937049587988455)
                    ·
                      rfl

theorem cell22_876255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 4, 3, 3].length) (baseStart_876255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_876255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_876255 prefixEnd_876255 := by exact prefixLift 876255
  have htrace : WordTrace (prefixWord ++ tailWord_876255) baseStart_876255 baseEnd_876255 := by
    simpa [prefixWord, tailWord_876255, baseEnd_876255] using wordTrace_append hprefix tailTrace_876255
  have hstable : (prefixWord ++ tailWord_876255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876255).length < 2 ^ (prefixWord ++ tailWord_876255).sum := by decide
  have hdescent : baseEnd_876255 < baseStart_876255 := by decide
  rcases family_descends (prefixWord ++ tailWord_876255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876257 : List Nat := [1, 2, 3, 1, 5, 2, 2, 6]
def baseStart_876257 : Nat := 118140960795 + 876257 * 2 ^ 59
def prefixEnd_876257 : Nat := 4983230072969 + 3 ^ 40 * 876257 * 2
def baseEnd_876257 : Nat := 33328964286435805493161

theorem tailTrace_876257 : CollatzResearch.WordTrace tailWord_876257 prefixEnd_876257 33328964286435805493161 := by
  unfold tailWord_876257
  simp only [CollatzResearch.WordTrace]
  refine ⟨31959718386478016626243025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21306478924318677750828683 31959718386478016626243025)
  ·
    refine ⟨23969788789858512469682269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31959718386478016626243025 23969788789858512469682269)
    ·
      refine ⟨8988670796196942176130851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23969788789858512469682269 8988670796196942176130851)
      ·
        refine ⟨13483006194295413264196277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8988670796196942176130851 13483006194295413264196277)
        ·
          refine ⟨1264031830715194993518401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13483006194295413264196277 1264031830715194993518401)
          ·
            refine ⟨948023873036396245138801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1264031830715194993518401 948023873036396245138801)
            ·
              refine ⟨711017904777297183854101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 948023873036396245138801 711017904777297183854101)
              ·
                refine ⟨33328964286435805493161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 711017904777297183854101 33328964286435805493161)
                ·
                  rfl

theorem cell22_876257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 2, 6].length) (baseStart_876257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_876257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_876257 prefixEnd_876257 := by exact prefixLift 876257
  have htrace : WordTrace (prefixWord ++ tailWord_876257) baseStart_876257 baseEnd_876257 := by
    simpa [prefixWord, tailWord_876257, baseEnd_876257] using wordTrace_append hprefix tailTrace_876257
  have hstable : (prefixWord ++ tailWord_876257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876257).length < 2 ^ (prefixWord ++ tailWord_876257).sum := by decide
  have hdescent : baseEnd_876257 < baseStart_876257 := by decide
  rcases family_descends (prefixWord ++ tailWord_876257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876268 : List Nat := [2, 2, 1, 1, 2, 2, 3, 2, 7]
def baseStart_876268 : Nat := 118140960795 + 876268 * 2 ^ 59
def prefixEnd_876268 : Nat := 4983230072969 + 3 ^ 40 * 876268 * 2
def baseEnd_876268 : Nat := 99988148034240629137805

theorem tailTrace_876268 : CollatzResearch.WordTrace tailWord_876268 prefixEnd_876268 99988148034240629137805 := by
  unfold tailWord_876268
  simp only [CollatzResearch.WordTrace]
  refine ⟨15980059794719082752446729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21306746392958777003262305 15980059794719082752446729)
  ·
    refine ⟨11985044846039312064335047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15980059794719082752446729 11985044846039312064335047)
    ·
      refine ⟨17977567269058968096502571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11985044846039312064335047 17977567269058968096502571)
      ·
        refine ⟨26966350903588452144753857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17977567269058968096502571 26966350903588452144753857)
        ·
          refine ⟨20224763177691339108565393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26966350903588452144753857 20224763177691339108565393)
          ·
            refine ⟨15168572383268504331424045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20224763177691339108565393 15168572383268504331424045)
            ·
              refine ⟨5688214643725689124284017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15168572383268504331424045 5688214643725689124284017)
              ·
                refine ⟨4266160982794266843213013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5688214643725689124284017 4266160982794266843213013)
                ·
                  refine ⟨99988148034240629137805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4266160982794266843213013 99988148034240629137805)
                  ·
                    rfl

theorem cell22_876268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 7].length) (baseStart_876268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_876268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_876268 prefixEnd_876268 := by exact prefixLift 876268
  have htrace : WordTrace (prefixWord ++ tailWord_876268) baseStart_876268 baseEnd_876268 := by
    simpa [prefixWord, tailWord_876268, baseEnd_876268] using wordTrace_append hprefix tailTrace_876268
  have hstable : (prefixWord ++ tailWord_876268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876268).length < 2 ^ (prefixWord ++ tailWord_876268).sum := by decide
  have hdescent : baseEnd_876268 < baseStart_876268 := by decide
  rcases family_descends (prefixWord ++ tailWord_876268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876272 : List Nat := [2, 1, 1, 1, 3, 1, 2, 7, 1, 3]
def baseStart_876272 : Nat := 118140960795 + 876272 * 2 ^ 59
def prefixEnd_876272 : Nat := 4983230072969 + 3 ^ 40 * 876272 * 2
def baseEnd_876272 : Nat := 299965813384467210313403

theorem tailTrace_876272 : CollatzResearch.WordTrace tailWord_876272 prefixEnd_876272 299965813384467210313403 := by
  unfold tailWord_876272
  simp only [CollatzResearch.WordTrace]
  refine ⟨15980132740711837094019535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21306843654282449458692713 15980132740711837094019535)
  ·
    refine ⟨23970199111067755641029303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15980132740711837094019535 23970199111067755641029303)
    ·
      refine ⟨35955298666601633461543955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23970199111067755641029303 35955298666601633461543955)
      ·
        refine ⟨53932947999902450192315933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35955298666601633461543955 53932947999902450192315933)
        ·
          refine ⟨20224855499963418822118475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53932947999902450192315933 20224855499963418822118475)
          ·
            refine ⟨30337283249945128233177713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20224855499963418822118475 30337283249945128233177713)
            ·
              refine ⟨22752962437458846174883285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30337283249945128233177713 22752962437458846174883285)
              ·
                refine ⟨533272557127941707223827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 22752962437458846174883285 533272557127941707223827)
                ·
                  refine ⟨799908835691912560835741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 533272557127941707223827 799908835691912560835741)
                  ·
                    refine ⟨299965813384467210313403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 799908835691912560835741 299965813384467210313403)
                    ·
                      rfl

theorem cell22_876272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 7, 1, 3].length) (baseStart_876272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_876272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_876272 prefixEnd_876272 := by exact prefixLift 876272
  have htrace : WordTrace (prefixWord ++ tailWord_876272) baseStart_876272 baseEnd_876272 := by
    simpa [prefixWord, tailWord_876272, baseEnd_876272] using wordTrace_append hprefix tailTrace_876272
  have hstable : (prefixWord ++ tailWord_876272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876272).length < 2 ^ (prefixWord ++ tailWord_876272).sum := by decide
  have hdescent : baseEnd_876272 < baseStart_876272 := by decide
  rcases family_descends (prefixWord ++ tailWord_876272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876283 : List Nat := [1, 1, 1, 1, 1, 3, 1, 6, 2, 5]
def baseStart_876283 : Nat := 118140960795 + 876283 * 2 ^ 59
def prefixEnd_876283 : Nat := 4983230072969 + 3 ^ 40 * 876283 * 2
def baseEnd_876283 : Nat := 299969578909266848288369

theorem tailTrace_876283 : CollatzResearch.WordTrace tailWord_876283 prefixEnd_876283 299969578909266848288369 := by
  unfold tailWord_876283
  simp only [CollatzResearch.WordTrace]
  refine ⟨31960666684383823066689503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21307111122922548711126335 31960666684383823066689503)
  ·
    refine ⟨47941000026575734600034255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31960666684383823066689503 47941000026575734600034255)
    ·
      refine ⟨71911500039863601900051383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47941000026575734600034255 71911500039863601900051383)
      ·
        refine ⟨107867250059795402850077075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71911500039863601900051383 107867250059795402850077075)
        ·
          refine ⟨161800875089693104275115613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107867250059795402850077075 161800875089693104275115613)
          ·
            refine ⟨60675328158634914103168355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161800875089693104275115613 60675328158634914103168355)
            ·
              refine ⟨91012992237952371154752533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60675328158634914103168355 91012992237952371154752533)
              ·
                refine ⟨4266234011154017397879025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 91012992237952371154752533 4266234011154017397879025)
                ·
                  refine ⟨3199675508365513048409269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4266234011154017397879025 3199675508365513048409269)
                  ·
                    refine ⟨299969578909266848288369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3199675508365513048409269 299969578909266848288369)
                    ·
                      rfl

theorem cell22_876283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 2, 5].length) (baseStart_876283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_876283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_876283 prefixEnd_876283 := by exact prefixLift 876283
  have htrace : WordTrace (prefixWord ++ tailWord_876283) baseStart_876283 baseEnd_876283 := by
    simpa [prefixWord, tailWord_876283, baseEnd_876283] using wordTrace_append hprefix tailTrace_876283
  have hstable : (prefixWord ++ tailWord_876283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876283).length < 2 ^ (prefixWord ++ tailWord_876283).sum := by decide
  have hdescent : baseEnd_876283 < baseStart_876283 := by decide
  rcases family_descends (prefixWord ++ tailWord_876283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876302 : List Nat := [4, 1, 1, 2, 1, 1, 6, 1, 5]
def baseStart_876302 : Nat := 118140960795 + 876302 * 2 ^ 59
def prefixEnd_876302 : Nat := 4983230072969 + 3 ^ 40 * 876302 * 2
def baseEnd_876302 : Nat := 99992027665852377354437

theorem tailTrace_876302 : CollatzResearch.WordTrace tailWord_876302 prefixEnd_876302 99992027665852377354437 := by
  unfold tailWord_876302
  simp only [CollatzResearch.WordTrace]
  refine ⟨3995169958914373663953895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21307573114209992874420773 3995169958914373663953895)
  ·
    refine ⟨5992754938371560495930843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3995169958914373663953895 5992754938371560495930843)
    ·
      refine ⟨8989132407557340743896265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5992754938371560495930843 8989132407557340743896265)
      ·
        refine ⟨6741849305668005557922199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8989132407557340743896265 6741849305668005557922199)
        ·
          refine ⟨10112773958502008336883299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6741849305668005557922199 10112773958502008336883299)
          ·
            refine ⟨15169160937753012505324949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10112773958502008336883299 15169160937753012505324949)
            ·
              refine ⟨711054418957172461187107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15169160937753012505324949 711054418957172461187107)
              ·
                refine ⟨1066581628435758691780661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 711054418957172461187107 1066581628435758691780661)
                ·
                  refine ⟨99992027665852377354437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1066581628435758691780661 99992027665852377354437)
                  ·
                    rfl

theorem cell22_876302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 6, 1, 5].length) (baseStart_876302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_876302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_876302 prefixEnd_876302 := by exact prefixLift 876302
  have htrace : WordTrace (prefixWord ++ tailWord_876302) baseStart_876302 baseEnd_876302 := by
    simpa [prefixWord, tailWord_876302, baseEnd_876302] using wordTrace_append hprefix tailTrace_876302
  have hstable : (prefixWord ++ tailWord_876302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876302).length < 2 ^ (prefixWord ++ tailWord_876302).sum := by decide
  have hdescent : baseEnd_876302 < baseStart_876302 := by decide
  rcases family_descends (prefixWord ++ tailWord_876302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876362 : List Nat := [3, 1, 2, 1, 1, 1, 3, 5, 2, 3]
def baseStart_876362 : Nat := 118140960795 + 876362 * 2 ^ 59
def prefixEnd_876362 : Nat := 4983230072969 + 3 ^ 40 * 876362 * 2
def baseEnd_876362 : Nat := 299996622223736975563127

theorem tailTrace_876362 : CollatzResearch.WordTrace tailWord_876362 prefixEnd_876362 299996622223736975563127 := by
  unfold tailWord_876362
  simp only [CollatzResearch.WordTrace]
  refine ⟨7990887012774404889703835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21309032034065079705876893 7990887012774404889703835)
  ·
    refine ⟨11986330519161607334555753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7990887012774404889703835 11986330519161607334555753)
    ·
      refine ⟨8989747889371205500916815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11986330519161607334555753 8989747889371205500916815)
      ·
        refine ⟨13484621834056808251375223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8989747889371205500916815 13484621834056808251375223)
        ·
          refine ⟨20226932751085212377062835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13484621834056808251375223 20226932751085212377062835)
          ·
            refine ⟨30340399126627818565594253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20226932751085212377062835 30340399126627818565594253)
            ·
              refine ⟨11377649672485431962097845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30340399126627818565594253 11377649672485431962097845)
              ·
                refine ⟨1066654656795509246446673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11377649672485431962097845 1066654656795509246446673)
                ·
                  refine ⟨799990992596631934835005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1066654656795509246446673 799990992596631934835005)
                  ·
                    refine ⟨299996622223736975563127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 799990992596631934835005 299996622223736975563127)
                    ·
                      rfl

theorem cell22_876362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 5, 2, 3].length) (baseStart_876362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_876362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_876362 prefixEnd_876362 := by exact prefixLift 876362
  have htrace : WordTrace (prefixWord ++ tailWord_876362) baseStart_876362 baseEnd_876362 := by
    simpa [prefixWord, tailWord_876362, baseEnd_876362] using wordTrace_append hprefix tailTrace_876362
  have hstable : (prefixWord ++ tailWord_876362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876362).length < 2 ^ (prefixWord ++ tailWord_876362).sum := by decide
  have hdescent : baseEnd_876362 < baseStart_876362 := by decide
  rcases family_descends (prefixWord ++ tailWord_876362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876426 : List Nat := [3, 1, 2, 4, 3, 1, 2, 6]
def baseStart_876426 : Nat := 118140960795 + 876426 * 2 ^ 59
def prefixEnd_876426 : Nat := 4983230072969 + 3 ^ 40 * 876426 * 2
def baseEnd_876426 : Nat := 33335392303518015773659

theorem tailTrace_876426 : CollatzResearch.WordTrace tailWord_876426 prefixEnd_876426 33335392303518015773659 := by
  unfold tailWord_876426
  simp only [CollatzResearch.WordTrace]
  refine ⟨7991470580716439622286283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21310588215243838992763421 7991470580716439622286283)
  ·
    refine ⟨11987205871074659433429425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7991470580716439622286283 11987205871074659433429425)
    ·
      refine ⟨8990404403305994575072069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11987205871074659433429425 8990404403305994575072069)
      ·
        refine ⟨1685700825619873982826013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8990404403305994575072069 1685700825619873982826013)
        ·
          refine ⟨632137809607452743559755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1685700825619873982826013 632137809607452743559755)
          ·
            refine ⟨948206714411179115339633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 632137809607452743559755 948206714411179115339633)
            ·
              refine ⟨711155035808384336504725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 948206714411179115339633 711155035808384336504725)
              ·
                refine ⟨33335392303518015773659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 711155035808384336504725 33335392303518015773659)
                ·
                  rfl

theorem cell22_876426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 2, 6].length) (baseStart_876426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_876426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_876426 prefixEnd_876426 := by exact prefixLift 876426
  have htrace : WordTrace (prefixWord ++ tailWord_876426) baseStart_876426 baseEnd_876426 := by
    simpa [prefixWord, tailWord_876426, baseEnd_876426] using wordTrace_append hprefix tailTrace_876426
  have hstable : (prefixWord ++ tailWord_876426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876426).length < 2 ^ (prefixWord ++ tailWord_876426).sum := by decide
  have hdescent : baseEnd_876426 < baseStart_876426 := by decide
  rcases family_descends (prefixWord ++ tailWord_876426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876497 : List Nat := [1, 2, 2, 1, 2, 1, 2, 4, 4, 3]
def baseStart_876497 : Nat := 118140960795 + 876497 * 2 ^ 59
def prefixEnd_876497 : Nat := 4983230072969 + 3 ^ 40 * 876497 * 2
def baseEnd_876497 : Nat := 300042835482641623437713

theorem tailTrace_876497 : CollatzResearch.WordTrace tailWord_876497 prefixEnd_876497 300042835482641623437713 := by
  unfold tailWord_876497
  simp only [CollatzResearch.WordTrace]
  refine ⟨31968471905608537614979745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21312314603739025076653163 31968471905608537614979745)
  ·
    refine ⟨23976353929206403211234809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31968471905608537614979745 23976353929206403211234809)
    ·
      refine ⟨17982265446904802408426107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23976353929206403211234809 17982265446904802408426107)
      ·
        refine ⟨26973398170357203612639161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17982265446904802408426107 26973398170357203612639161)
        ·
          refine ⟨20230048627767902709479371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26973398170357203612639161 20230048627767902709479371)
          ·
            refine ⟨30345072941651854064219057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20230048627767902709479371 30345072941651854064219057)
            ·
              refine ⟨22758804706238890548164293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30345072941651854064219057 22758804706238890548164293)
              ·
                refine ⟨4267275882419791977780805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22758804706238890548164293 4267275882419791977780805)
                ·
                  refine ⟨800114227953710995833901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4267275882419791977780805 800114227953710995833901)
                  ·
                    refine ⟨300042835482641623437713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 800114227953710995833901 300042835482641623437713)
                    ·
                      rfl

theorem cell22_876497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4, 4, 3].length) (baseStart_876497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_876497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_876497 prefixEnd_876497 := by exact prefixLift 876497
  have htrace : WordTrace (prefixWord ++ tailWord_876497) baseStart_876497 baseEnd_876497 := by
    simpa [prefixWord, tailWord_876497, baseEnd_876497] using wordTrace_append hprefix tailTrace_876497
  have hstable : (prefixWord ++ tailWord_876497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876497).length < 2 ^ (prefixWord ++ tailWord_876497).sum := by decide
  have hdescent : baseEnd_876497 < baseStart_876497 := by decide
  rcases family_descends (prefixWord ++ tailWord_876497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876501 : List Nat := [1, 3, 2, 3, 2, 2, 3, 1, 1, 4]
def baseStart_876501 : Nat := 118140960795 + 876501 * 2 ^ 59
def prefixEnd_876501 : Nat := 4983230072969 + 3 ^ 40 * 876501 * 2
def baseEnd_876501 : Nat := 300044204764386946337701

theorem tailTrace_876501 : CollatzResearch.WordTrace tailWord_876501 prefixEnd_876501 300044204764386946337701 := by
  unfold tailWord_876501
  simp only [CollatzResearch.WordTrace]
  refine ⟨31968617797594046298125357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21312411865062697532083571 31968617797594046298125357)
  ·
    refine ⟨11988231674097767361797009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31968617797594046298125357 11988231674097767361797009)
    ·
      refine ⟨8991173755573325521347757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11988231674097767361797009 8991173755573325521347757)
      ·
        refine ⟨3371690158339997070505409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8991173755573325521347757 3371690158339997070505409)
        ·
          refine ⟨2528767618754997802879057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3371690158339997070505409 2528767618754997802879057)
          ·
            refine ⟨1896575714066248352159293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2528767618754997802879057 1896575714066248352159293)
            ·
              refine ⟨711215892774843132059735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1896575714066248352159293 711215892774843132059735)
              ·
                refine ⟨1066823839162264698089603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 711215892774843132059735 1066823839162264698089603)
                ·
                  refine ⟨1600235758743397047134405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1066823839162264698089603 1600235758743397047134405)
                  ·
                    refine ⟨300044204764386946337701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1600235758743397047134405 300044204764386946337701)
                    ·
                      rfl

theorem cell22_876501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 3, 1, 1, 4].length) (baseStart_876501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_876501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_876501 prefixEnd_876501 := by exact prefixLift 876501
  have htrace : WordTrace (prefixWord ++ tailWord_876501) baseStart_876501 baseEnd_876501 := by
    simpa [prefixWord, tailWord_876501, baseEnd_876501] using wordTrace_append hprefix tailTrace_876501
  have hstable : (prefixWord ++ tailWord_876501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876501).length < 2 ^ (prefixWord ++ tailWord_876501).sum := by decide
  have hdescent : baseEnd_876501 < baseStart_876501 := by decide
  rcases family_descends (prefixWord ++ tailWord_876501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876696 : List Nat := [2, 1, 2, 4, 3, 2, 1, 7]
def baseStart_876696 : Nat := 118140960795 + 876696 * 2 ^ 59
def prefixEnd_876696 : Nat := 4983230072969 + 3 ^ 40 * 876696 * 2
def baseEnd_876696 : Nat := 33345661916607937523567

theorem tailTrace_876696 : CollatzResearch.WordTrace tailWord_876696 prefixEnd_876696 33345661916607937523567 := by
  unfold tailWord_876696
  simp only [CollatzResearch.WordTrace]
  refine ⟨15987865015943797300736971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21317153354591729734315961 15987865015943797300736971)
  ·
    refine ⟨23981797523915695951105457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15987865015943797300736971 23981797523915695951105457)
    ·
      refine ⟨17986348142936771963329093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23981797523915695951105457 17986348142936771963329093)
      ·
        refine ⟨3372440276800644743124205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17986348142936771963329093 3372440276800644743124205)
        ·
          refine ⟨1264665103800241778671577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3372440276800644743124205 1264665103800241778671577)
          ·
            refine ⟨948498827850181334003683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1264665103800241778671577 948498827850181334003683)
            ·
              refine ⟨1422748241775272001005525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 948498827850181334003683 1422748241775272001005525)
              ·
                refine ⟨33345661916607937523567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1422748241775272001005525 33345661916607937523567)
                ·
                  rfl

theorem cell22_876696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 7].length) (baseStart_876696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_876696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_876696 prefixEnd_876696 := by exact prefixLift 876696
  have htrace : WordTrace (prefixWord ++ tailWord_876696) baseStart_876696 baseEnd_876696 := by
    simpa [prefixWord, tailWord_876696, baseEnd_876696] using wordTrace_append hprefix tailTrace_876696
  have hstable : (prefixWord ++ tailWord_876696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876696).length < 2 ^ (prefixWord ++ tailWord_876696).sum := by decide
  have hdescent : baseEnd_876696 < baseStart_876696 := by decide
  rcases family_descends (prefixWord ++ tailWord_876696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876707 : List Nat := [1, 1, 1, 4, 1, 1, 1, 1, 11]
def baseStart_876707 : Nat := 118140960795 + 876707 * 2 ^ 59
def prefixEnd_876707 : Nat := 4983230072969 + 3 ^ 40 * 876707 * 2
def baseEnd_876707 : Nat := 100038240924757025229023

theorem tailTrace_876707 : CollatzResearch.WordTrace tailWord_876707 prefixEnd_876707 100038240924757025229023 := by
  unfold tailWord_876707
  simp only [CollatzResearch.WordTrace]
  refine ⟨31976131234847743480124375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21317420823231828986749583 31976131234847743480124375)
  ·
    refine ⟨47964196852271615220186563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31976131234847743480124375 47964196852271615220186563)
    ·
      refine ⟨71946295278407422830279845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47964196852271615220186563 71946295278407422830279845)
      ·
        refine ⟨13489930364701391780677471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71946295278407422830279845 13489930364701391780677471)
        ·
          refine ⟨20234895547052087671016207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13489930364701391780677471 20234895547052087671016207)
          ·
            refine ⟨30352343320578131506524311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20234895547052087671016207 30352343320578131506524311)
            ·
              refine ⟨45528514980867197259786467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30352343320578131506524311 45528514980867197259786467)
              ·
                refine ⟨68292772471300795889679701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45528514980867197259786467 68292772471300795889679701)
                ·
                  refine ⟨100038240924757025229023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 68292772471300795889679701 100038240924757025229023)
                  ·
                    rfl

theorem cell22_876707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 11].length) (baseStart_876707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_876707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_876707 prefixEnd_876707 := by exact prefixLift 876707
  have htrace : WordTrace (prefixWord ++ tailWord_876707) baseStart_876707 baseEnd_876707 := by
    simpa [prefixWord, tailWord_876707, baseEnd_876707] using wordTrace_append hprefix tailTrace_876707
  have hstable : (prefixWord ++ tailWord_876707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876707).length < 2 ^ (prefixWord ++ tailWord_876707).sum := by decide
  have hdescent : baseEnd_876707 < baseStart_876707 := by decide
  rcases family_descends (prefixWord ++ tailWord_876707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876728 : List Nat := [2, 1, 2, 1, 2, 1, 6, 3, 1, 3]
def baseStart_876728 : Nat := 118140960795 + 876728 * 2 ^ 59
def prefixEnd_876728 : Nat := 4983230072969 + 3 ^ 40 * 876728 * 2
def baseEnd_876728 : Nat := 300121911503434020912005

theorem tailTrace_876728 : CollatzResearch.WordTrace tailWord_876728 prefixEnd_876728 300121911503434020912005 := by
  unfold tailWord_876728
  simp only [CollatzResearch.WordTrace]
  refine ⟨15988448583885832033319419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21317931445181109377759225 15988448583885832033319419)
  ·
    refine ⟨23982672875828748049979129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15988448583885832033319419 23982672875828748049979129)
    ·
      refine ⟨17987004656871561037484347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23982672875828748049979129 17987004656871561037484347)
      ·
        refine ⟨26980506985307341556226521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17987004656871561037484347 26980506985307341556226521)
        ·
          refine ⟨20235380238980506167169891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26980506985307341556226521 20235380238980506167169891)
          ·
            refine ⟨30353070358470759250754837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20235380238980506167169891 30353070358470759250754837)
            ·
              refine ⟨1422800173053316839879133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 30353070358470759250754837 1422800173053316839879133)
              ·
                refine ⟨533550064894993814954675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1422800173053316839879133 533550064894993814954675)
                ·
                  refine ⟨800325097342490722432013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 533550064894993814954675 800325097342490722432013)
                  ·
                    refine ⟨300121911503434020912005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 800325097342490722432013 300121911503434020912005)
                    ·
                      rfl

theorem cell22_876728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 3, 1, 3].length) (baseStart_876728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_876728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_876728 prefixEnd_876728 := by exact prefixLift 876728
  have htrace : WordTrace (prefixWord ++ tailWord_876728) baseStart_876728 baseEnd_876728 := by
    simpa [prefixWord, tailWord_876728, baseEnd_876728] using wordTrace_append hprefix tailTrace_876728
  have hstable : (prefixWord ++ tailWord_876728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876728).length < 2 ^ (prefixWord ++ tailWord_876728).sum := by decide
  have hdescent : baseEnd_876728 < baseStart_876728 := by decide
  rcases family_descends (prefixWord ++ tailWord_876728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876769 : List Nat := [1, 2, 3, 1, 3, 1, 1, 4, 6]
def baseStart_876769 : Nat := 118140960795 + 876769 * 2 ^ 59
def prefixEnd_876769 : Nat := 4983230072969 + 3 ^ 40 * 876769 * 2
def baseEnd_876769 : Nat := 100045315547107860212293

theorem tailTrace_876769 : CollatzResearch.WordTrace tailWord_876769 prefixEnd_876769 100045315547107860212293 := by
  unfold tailWord_876769
  simp only [CollatzResearch.WordTrace]
  refine ⟨31978392560623128068881361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21318928373748752045920907 31978392560623128068881361)
  ·
    refine ⟨23983794420467346051661021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31978392560623128068881361 23983794420467346051661021)
    ·
      refine ⟨8993922907675254769372883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23983794420467346051661021 8993922907675254769372883)
      ·
        refine ⟨13490884361512882154059325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8993922907675254769372883 13490884361512882154059325)
        ·
          refine ⟨5059081635567330807772247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13490884361512882154059325 5059081635567330807772247)
          ·
            refine ⟨7588622453350996211658371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5059081635567330807772247 7588622453350996211658371)
            ·
              refine ⟨11382933680026494317487557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7588622453350996211658371 11382933680026494317487557)
              ·
                refine ⟨2134300065004967684528917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11382933680026494317487557 2134300065004967684528917)
                ·
                  refine ⟨100045315547107860212293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2134300065004967684528917 100045315547107860212293)
                  ·
                    rfl

theorem cell22_876769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 4, 6].length) (baseStart_876769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_876769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_876769 prefixEnd_876769 := by exact prefixLift 876769
  have htrace : WordTrace (prefixWord ++ tailWord_876769) baseStart_876769 baseEnd_876769 := by
    simpa [prefixWord, tailWord_876769, baseEnd_876769] using wordTrace_append hprefix tailTrace_876769
  have hstable : (prefixWord ++ tailWord_876769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876769).length < 2 ^ (prefixWord ++ tailWord_876769).sum := by decide
  have hdescent : baseEnd_876769 < baseStart_876769 := by decide
  rcases family_descends (prefixWord ++ tailWord_876769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876784 : List Nat := [2, 1, 1, 1, 3, 1, 1, 6, 1, 5]
def baseStart_876784 : Nat := 118140960795 + 876784 * 2 ^ 59
def prefixEnd_876784 : Nat := 4983230072969 + 3 ^ 40 * 876784 * 2
def baseEnd_876784 : Nat := 300141081447868541511833

theorem tailTrace_876784 : CollatzResearch.WordTrace tailWord_876784 prefixEnd_876784 300141081447868541511833 := by
  unfold tailWord_876784
  simp only [CollatzResearch.WordTrace]
  refine ⟨15989469827784392815338703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21319293103712523753784937 15989469827784392815338703)
  ·
    refine ⟨23984204741676589223008055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15989469827784392815338703 23984204741676589223008055)
    ·
      refine ⟨35976307112514883834512083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23984204741676589223008055 35976307112514883834512083)
      ·
        refine ⟨53964460668772325751768125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35976307112514883834512083 53964460668772325751768125)
        ·
          refine ⟨20236672750789622156913047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53964460668772325751768125 20236672750789622156913047)
          ·
            refine ⟨30355009126184433235369571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20236672750789622156913047 30355009126184433235369571)
            ·
              refine ⟨45532513689276649853054357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30355009126184433235369571 45532513689276649853054357)
              ·
                refine ⟨2134336579184842961861923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 45532513689276649853054357 2134336579184842961861923)
                ·
                  refine ⟨3201504868777264442792885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2134336579184842961861923 3201504868777264442792885)
                  ·
                    refine ⟨300141081447868541511833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3201504868777264442792885 300141081447868541511833)
                    ·
                      rfl

theorem cell22_876784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 6, 1, 5].length) (baseStart_876784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_876784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_876784 prefixEnd_876784 := by exact prefixLift 876784
  have htrace : WordTrace (prefixWord ++ tailWord_876784) baseStart_876784 baseEnd_876784 := by
    simpa [prefixWord, tailWord_876784, baseEnd_876784] using wordTrace_append hprefix tailTrace_876784
  have hstable : (prefixWord ++ tailWord_876784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876784).length < 2 ^ (prefixWord ++ tailWord_876784).sum := by decide
  have hdescent : baseEnd_876784 < baseStart_876784 := by decide
  rcases family_descends (prefixWord ++ tailWord_876784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876801 : List Nat := [1, 2, 4, 1, 1, 2, 1, 3, 4, 3]
def baseStart_876801 : Nat := 118140960795 + 876801 * 2 ^ 59
def prefixEnd_876801 : Nat := 4983230072969 + 3 ^ 40 * 876801 * 2
def baseEnd_876801 : Nat := 300146900895286163836781

theorem tailTrace_876801 : CollatzResearch.WordTrace tailWord_876801 prefixEnd_876801 300146900895286163836781 := by
  unfold tailWord_876801
  simp only [CollatzResearch.WordTrace]
  refine ⟨31979559696507197534046257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21319706464338131689364171 31979559696507197534046257)
  ·
    refine ⟨23984669772380398150534693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31979559696507197534046257 23984669772380398150534693)
    ·
      refine ⟨4497125582321324653225255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23984669772380398150534693 4497125582321324653225255)
      ·
        refine ⟨6745688373481986979837883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4497125582321324653225255 6745688373481986979837883)
        ·
          refine ⟨10118532560222980469756825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6745688373481986979837883 10118532560222980469756825)
          ·
            refine ⟨7588899420167235352317619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10118532560222980469756825 7588899420167235352317619)
            ·
              refine ⟨11383349130250853028476429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7588899420167235352317619 11383349130250853028476429)
              ·
                refine ⟨4268755923844069885678661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11383349130250853028476429 4268755923844069885678661)
                ·
                  refine ⟨800391735720763103564749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4268755923844069885678661 800391735720763103564749)
                  ·
                    refine ⟨300146900895286163836781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 800391735720763103564749 300146900895286163836781)
                    ·
                      rfl

theorem cell22_876801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 3, 4, 3].length) (baseStart_876801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_876801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_876801 prefixEnd_876801 := by exact prefixLift 876801
  have htrace : WordTrace (prefixWord ++ tailWord_876801) baseStart_876801 baseEnd_876801 := by
    simpa [prefixWord, tailWord_876801, baseEnd_876801] using wordTrace_append hprefix tailTrace_876801
  have hstable : (prefixWord ++ tailWord_876801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876801).length < 2 ^ (prefixWord ++ tailWord_876801).sum := by decide
  have hdescent : baseEnd_876801 < baseStart_876801 := by decide
  rcases family_descends (prefixWord ++ tailWord_876801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876803 : List Nat := [1, 1, 1, 3, 2, 3, 5, 2, 4]
def baseStart_876803 : Nat := 118140960795 + 876803 * 2 ^ 59
def prefixEnd_876803 : Nat := 4983230072969 + 3 ^ 40 * 876803 * 2
def baseEnd_876803 : Nat := 100049195178719608428925

theorem tailTrace_876803 : CollatzResearch.WordTrace tailWord_876803 prefixEnd_876803 100049195178719608428925 := by
  unfold tailWord_876803
  simp only [CollatzResearch.WordTrace]
  refine ⟨31979632642499951875619063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21319755094999967917079375 31979632642499951875619063)
  ·
    refine ⟨47969448963749927813428595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31979632642499951875619063 47969448963749927813428595)
    ·
      refine ⟨71954173445624891720142893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47969448963749927813428595 71954173445624891720142893)
      ·
        refine ⟨26982815042109334395053585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71954173445624891720142893 26982815042109334395053585)
        ·
          refine ⟨20237111281582000796290189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26982815042109334395053585 20237111281582000796290189)
          ·
            refine ⟨7588916730593250298608821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20237111281582000796290189 7588916730593250298608821)
            ·
              refine ⟨711460943493117215494577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7588916730593250298608821 711460943493117215494577)
              ·
                refine ⟨533595707619837911620933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 711460943493117215494577 533595707619837911620933)
                ·
                  refine ⟨100049195178719608428925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 533595707619837911620933 100049195178719608428925)
                  ·
                    rfl

theorem cell22_876803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 5, 2, 4].length) (baseStart_876803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_876803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_876803 prefixEnd_876803 := by exact prefixLift 876803
  have htrace : WordTrace (prefixWord ++ tailWord_876803) baseStart_876803 baseEnd_876803 := by
    simpa [prefixWord, tailWord_876803, baseEnd_876803] using wordTrace_append hprefix tailTrace_876803
  have hstable : (prefixWord ++ tailWord_876803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876803).length < 2 ^ (prefixWord ++ tailWord_876803).sum := by decide
  have hdescent : baseEnd_876803 < baseStart_876803 := by decide
  rcases family_descends (prefixWord ++ tailWord_876803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876839 : List Nat := [1, 1, 8, 1, 1, 1, 3, 1, 1, 4]
def baseStart_876839 : Nat := 118140960795 + 876839 * 2 ^ 59
def prefixEnd_876839 : Nat := 4983230072969 + 3 ^ 40 * 876839 * 2
def baseEnd_876839 : Nat := 300159909071866731386665

theorem tailTrace_876839 : CollatzResearch.WordTrace tailWord_876839 prefixEnd_876839 300159909071866731386665 := by
  unfold tailWord_876839
  simp only [CollatzResearch.WordTrace]
  refine ⟨31980945670369530023929571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21320630446913020015953047 31980945670369530023929571)
  ·
    refine ⟨47971418505554295035894357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31980945670369530023929571 47971418505554295035894357)
    ·
      refine ⟨562165060611964394951887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 47971418505554295035894357 562165060611964394951887)
      ·
        refine ⟨843247590917946592427831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 562165060611964394951887 843247590917946592427831)
        ·
          refine ⟨1264871386376919888641747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 843247590917946592427831 1264871386376919888641747)
          ·
            refine ⟨1897307079565379832962621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1264871386376919888641747 1897307079565379832962621)
            ·
              refine ⟨711490154837017437360983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1897307079565379832962621 711490154837017437360983)
              ·
                refine ⟨1067235232255526156041475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 711490154837017437360983 1067235232255526156041475)
                ·
                  refine ⟨1600852848383289234062213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1067235232255526156041475 1600852848383289234062213)
                  ·
                    refine ⟨300159909071866731386665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1600852848383289234062213 300159909071866731386665)
                    ·
                      rfl

theorem cell22_876839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_876839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_876839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_876839 prefixEnd_876839 := by exact prefixLift 876839
  have htrace : WordTrace (prefixWord ++ tailWord_876839) baseStart_876839 baseEnd_876839 := by
    simpa [prefixWord, tailWord_876839, baseEnd_876839] using wordTrace_append hprefix tailTrace_876839
  have hstable : (prefixWord ++ tailWord_876839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876839).length < 2 ^ (prefixWord ++ tailWord_876839).sum := by decide
  have hdescent : baseEnd_876839 < baseStart_876839 := by decide
  rcases family_descends (prefixWord ++ tailWord_876839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876865 : List Nat := [1, 2, 5, 2, 3, 1, 1, 7]
def baseStart_876865 : Nat := 118140960795 + 876865 * 2 ^ 59
def prefixEnd_876865 : Nat := 4983230072969 + 3 ^ 40 * 876865 * 2
def baseEnd_876865 : Nat := 33352089933690147804065

theorem tailTrace_876865 : CollatzResearch.WordTrace tailWord_876865 prefixEnd_876865 33352089933690147804065 := by
  unfold tailWord_876865
  simp only [CollatzResearch.WordTrace]
  refine ⟨31981893968275336464376049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21321262645516890976250699 31981893968275336464376049)
  ·
    refine ⟨23986420476206502348282037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31981893968275336464376049 23986420476206502348282037)
    ·
      refine ⟨2248726919644359595151441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23986420476206502348282037 2248726919644359595151441)
      ·
        refine ⟨1686545189733269696363581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2248726919644359595151441 1686545189733269696363581)
        ·
          refine ⟨632454446149976136136343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1686545189733269696363581 632454446149976136136343)
          ·
            refine ⟨948681669224964204204515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 632454446149976136136343 948681669224964204204515)
            ·
              refine ⟨1423022503837446306306773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 948681669224964204204515 1423022503837446306306773)
              ·
                refine ⟨33352089933690147804065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1423022503837446306306773 33352089933690147804065)
                ·
                  rfl

theorem cell22_876865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 7].length) (baseStart_876865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_876865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_876865 prefixEnd_876865 := by exact prefixLift 876865
  have htrace : WordTrace (prefixWord ++ tailWord_876865) baseStart_876865 baseEnd_876865 := by
    simpa [prefixWord, tailWord_876865, baseEnd_876865] using wordTrace_append hprefix tailTrace_876865
  have hstable : (prefixWord ++ tailWord_876865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876865).length < 2 ^ (prefixWord ++ tailWord_876865).sum := by decide
  have hdescent : baseEnd_876865 < baseStart_876865 := by decide
  rcases family_descends (prefixWord ++ tailWord_876865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876876 : List Nat := [2, 2, 1, 3, 2, 1, 1, 5, 5]
def baseStart_876876 : Nat := 118140960795 + 876876 * 2 ^ 59
def prefixEnd_876876 : Nat := 4983230072969 + 3 ^ 40 * 876876 * 2
def baseEnd_876876 : Nat := 100057524976003656070517

theorem tailTrace_876876 : CollatzResearch.WordTrace tailWord_876876 prefixEnd_876876 100057524976003656070517 := by
  unfold tailWord_876876
  simp only [CollatzResearch.WordTrace]
  refine ⟨15991147585617742671513241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21321530114156990228684321 15991147585617742671513241)
  ·
    refine ⟨11993360689213307003634931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15991147585617742671513241 11993360689213307003634931)
    ·
      refine ⟨17990041033819960505452397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11993360689213307003634931 17990041033819960505452397)
      ·
        refine ⟨6746265387682485189544649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17990041033819960505452397 6746265387682485189544649)
        ·
          refine ⟨5059699040761863892158487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6746265387682485189544649 5059699040761863892158487)
          ·
            refine ⟨7589548561142795838237731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5059699040761863892158487 7589548561142795838237731)
            ·
              refine ⟨11384322841714193757356597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7589548561142795838237731 11384322841714193757356597)
              ·
                refine ⟨1067280266410705664752181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11384322841714193757356597 1067280266410705664752181)
                ·
                  refine ⟨100057524976003656070517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1067280266410705664752181 100057524976003656070517)
                  ·
                    rfl

theorem cell22_876876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 5, 5].length) (baseStart_876876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_876876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_876876 prefixEnd_876876 := by exact prefixLift 876876
  have htrace : WordTrace (prefixWord ++ tailWord_876876) baseStart_876876 baseEnd_876876 := by
    simpa [prefixWord, tailWord_876876, baseEnd_876876] using wordTrace_append hprefix tailTrace_876876
  have hstable : (prefixWord ++ tailWord_876876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876876).length < 2 ^ (prefixWord ++ tailWord_876876).sum := by decide
  have hdescent : baseEnd_876876 < baseStart_876876 := by decide
  rcases family_descends (prefixWord ++ tailWord_876876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876951 : List Nat := [1, 1, 3, 3, 1, 1, 4, 1, 1, 6]
def baseStart_876951 : Nat := 118140960795 + 876951 * 2 ^ 59
def prefixEnd_876951 : Nat := 4983230072969 + 3 ^ 40 * 876951 * 2
def baseEnd_876951 : Nat := 300198248960735772586321

theorem tailTrace_876951 : CollatzResearch.WordTrace tailWord_876951 prefixEnd_876951 300198248960735772586321 := by
  unfold tailWord_876951
  simp only [CollatzResearch.WordTrace]
  refine ⟨31985030645963773152006707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21323353763975848768004471 31985030645963773152006707)
  ·
    refine ⟨47977545968945659728010061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31985030645963773152006707 47977545968945659728010061)
    ·
      refine ⟨17991579738354622398003773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47977545968945659728010061 17991579738354622398003773)
      ·
        refine ⟨6746842401882983399251415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17991579738354622398003773 6746842401882983399251415)
        ·
          refine ⟨10120263602824475098877123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6746842401882983399251415 10120263602824475098877123)
          ·
            refine ⟨15180395404236712648315685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10120263602824475098877123 15180395404236712648315685)
            ·
              refine ⟨2846324138294383621559191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15180395404236712648315685 2846324138294383621559191)
              ·
                refine ⟨4269486207441575432338787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2846324138294383621559191 4269486207441575432338787)
                ·
                  refine ⟨6404229311162363148508181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4269486207441575432338787 6404229311162363148508181)
                  ·
                    refine ⟨300198248960735772586321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6404229311162363148508181 300198248960735772586321)
                    ·
                      rfl

theorem cell22_876951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 1, 1, 6].length) (baseStart_876951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_876951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_876951 prefixEnd_876951 := by exact prefixLift 876951
  have htrace : WordTrace (prefixWord ++ tailWord_876951) baseStart_876951 baseEnd_876951 := by
    simpa [prefixWord, tailWord_876951, baseEnd_876951] using wordTrace_append hprefix tailTrace_876951
  have hstable : (prefixWord ++ tailWord_876951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876951).length < 2 ^ (prefixWord ++ tailWord_876951).sum := by decide
  have hdescent : baseEnd_876951 < baseStart_876951 := by decide
  rcases family_descends (prefixWord ++ tailWord_876951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877032 : List Nat := [2, 1, 4, 1, 1, 4, 1, 4, 1, 3]
def baseStart_877032 : Nat := 118140960795 + 877032 * 2 ^ 59
def prefixEnd_877032 : Nat := 4983230072969 + 3 ^ 40 * 877032 * 2
def baseEnd_877032 : Nat := 300225976916078561311073

theorem tailTrace_877032 : CollatzResearch.WordTrace tailWord_877032 prefixEnd_877032 300225976916078561311073 := by
  unfold tailWord_877032
  simp only [CollatzResearch.WordTrace]
  refine ⟨15993992479335161992852675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21325323305780215990470233 15993992479335161992852675)
  ·
    refine ⟨23990988719002742989279013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15993992479335161992852675 23990988719002742989279013)
    ·
      refine ⟨4498310384813014310489815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23990988719002742989279013 4498310384813014310489815)
      ·
        refine ⟨6747465577219521465734723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4498310384813014310489815 6747465577219521465734723)
        ·
          refine ⟨10121198365829282198602085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6747465577219521465734723 10121198365829282198602085)
          ·
            refine ⟨1897724693592990412237891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10121198365829282198602085 1897724693592990412237891)
            ·
              refine ⟨2846587040389485618356837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1897724693592990412237891 2846587040389485618356837)
              ·
                refine ⟨533735070073028553441907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2846587040389485618356837 533735070073028553441907)
                ·
                  refine ⟨800602605109542830162861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 533735070073028553441907 800602605109542830162861)
                  ·
                    refine ⟨300225976916078561311073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 800602605109542830162861 300225976916078561311073)
                    ·
                      rfl

theorem cell22_877032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 4, 1, 3].length) (baseStart_877032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_877032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_877032 prefixEnd_877032 := by exact prefixLift 877032
  have htrace : WordTrace (prefixWord ++ tailWord_877032) baseStart_877032 baseEnd_877032 := by
    simpa [prefixWord, tailWord_877032, baseEnd_877032] using wordTrace_append hprefix tailTrace_877032
  have hstable : (prefixWord ++ tailWord_877032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877032).length < 2 ^ (prefixWord ++ tailWord_877032).sum := by decide
  have hdescent : baseEnd_877032 < baseStart_877032 := by decide
  rcases family_descends (prefixWord ++ tailWord_877032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877079 : List Nat := [1, 1, 3, 6, 2, 1, 1, 2, 5]
def baseStart_877079 : Nat := 118140960795 + 877079 * 2 ^ 59
def prefixEnd_877079 : Nat := 4983230072969 + 3 ^ 40 * 877079 * 2
def baseEnd_877079 : Nat := 100080688658862035128643

theorem tailTrace_877079 : CollatzResearch.WordTrace tailWord_877079 prefixEnd_877079 100080688658862035128643 := by
  unfold tailWord_877079
  simp only [CollatzResearch.WordTrace]
  refine ⟨31989699189500051012666291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21326466126333367341777527 31989699189500051012666291)
  ·
    refine ⟨47984548784250076518999437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31989699189500051012666291 47984548784250076518999437)
    ·
      refine ⟨17994205794093778694624789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47984548784250076518999437 17994205794093778694624789)
      ·
        refine ⟨843478396598145876310537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 17994205794093778694624789 843478396598145876310537)
        ·
          refine ⟨632608797448609407232903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 843478396598145876310537 632608797448609407232903)
          ·
            refine ⟨948913196172914110849355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 632608797448609407232903 948913196172914110849355)
            ·
              refine ⟨1423369794259371166274033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 948913196172914110849355 1423369794259371166274033)
              ·
                refine ⟨1067527345694528374705525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1423369794259371166274033 1067527345694528374705525)
                ·
                  refine ⟨100080688658862035128643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1067527345694528374705525 100080688658862035128643)
                  ·
                    rfl

theorem cell22_877079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 2, 5].length) (baseStart_877079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_877079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_877079 prefixEnd_877079 := by exact prefixLift 877079
  have htrace : WordTrace (prefixWord ++ tailWord_877079) baseStart_877079 baseEnd_877079 := by
    simpa [prefixWord, tailWord_877079, baseEnd_877079] using wordTrace_append hprefix tailTrace_877079
  have hstable : (prefixWord ++ tailWord_877079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877079).length < 2 ^ (prefixWord ++ tailWord_877079).sum := by decide
  have hdescent : baseEnd_877079 < baseStart_877079 := by decide
  rcases family_descends (prefixWord ++ tailWord_877079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877105 : List Nat := [1, 2, 2, 3, 1, 1, 2, 5, 2, 3]
def baseStart_877105 : Nat := 118140960795 + 877105 * 2 ^ 59
def prefixEnd_877105 : Nat := 4983230072969 + 3 ^ 40 * 877105 * 2
def baseEnd_877105 : Nat := 300250966307930704235849

theorem tailTrace_877105 : CollatzResearch.WordTrace tailWord_877105 prefixEnd_877105 300250966307930704235849 := by
  unfold tailWord_877105
  simp only [CollatzResearch.WordTrace]
  refine ⟨31990647487405857453112769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21327098324937238302075179 31990647487405857453112769)
  ·
    refine ⟨23992985615554393089834577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31990647487405857453112769 23992985615554393089834577)
    ·
      refine ⟨17994739211665794817375933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23992985615554393089834577 17994739211665794817375933)
      ·
        refine ⟨6748027204374673056515975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17994739211665794817375933 6748027204374673056515975)
        ·
          refine ⟨10122040806562009584773963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6748027204374673056515975 10122040806562009584773963)
          ·
            refine ⟨15183061209843014377160945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10122040806562009584773963 15183061209843014377160945)
            ·
              refine ⟨11387295907382260782870709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15183061209843014377160945 11387295907382260782870709)
              ·
                refine ⟨1067558991317086948394129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11387295907382260782870709 1067558991317086948394129)
                ·
                  refine ⟨800669243487815211295597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1067558991317086948394129 800669243487815211295597)
                  ·
                    refine ⟨300250966307930704235849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 800669243487815211295597 300250966307930704235849)
                    ·
                      rfl

theorem cell22_877105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 5, 2, 3].length) (baseStart_877105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_877105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_877105 prefixEnd_877105 := by exact prefixLift 877105
  have htrace : WordTrace (prefixWord ++ tailWord_877105) baseStart_877105 baseEnd_877105 := by
    simpa [prefixWord, tailWord_877105, baseEnd_877105] using wordTrace_append hprefix tailTrace_877105
  have hstable : (prefixWord ++ tailWord_877105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877105).length < 2 ^ (prefixWord ++ tailWord_877105).sum := by decide
  have hdescent : baseEnd_877105 < baseStart_877105 := by decide
  rcases family_descends (prefixWord ++ tailWord_877105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877242 : List Nat := [3, 1, 1, 1, 2, 3, 4, 3, 4]
def baseStart_877242 : Nat := 118140960795 + 877242 * 2 ^ 59
def prefixEnd_877242 : Nat := 4983230072969 + 3 ^ 40 * 877242 * 2
def baseEnd_877242 : Nat := 100099288069236004520143

theorem tailTrace_877242 : CollatzResearch.WordTrace tailWord_877242 prefixEnd_877242 100099288069236004520143 := by
  unfold tailWord_877242
  simp only [CollatzResearch.WordTrace]
  refine ⟨7998911071977382462712495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21330429525273019900566653 7998911071977382462712495)
  ·
    refine ⟨11998366607966073694068743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7998911071977382462712495 11998366607966073694068743)
    ·
      refine ⟨17997549911949110541103115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11998366607966073694068743 17997549911949110541103115)
      ·
        refine ⟨26996324867923665811654673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17997549911949110541103115 26996324867923665811654673)
        ·
          refine ⟨20247243650942749358741005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26996324867923665811654673 20247243650942749358741005)
          ·
            refine ⟨7592716369103531009527877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20247243650942749358741005 7592716369103531009527877)
            ·
              refine ⟨1423634319206912064286477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7592716369103531009527877 1423634319206912064286477)
              ·
                refine ⟨533862869702592024107429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1423634319206912064286477 533862869702592024107429)
                ·
                  refine ⟨100099288069236004520143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 533862869702592024107429 100099288069236004520143)
                  ·
                    rfl

theorem cell22_877242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 3, 4].length) (baseStart_877242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_877242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_877242 prefixEnd_877242 := by exact prefixLift 877242
  have htrace : WordTrace (prefixWord ++ tailWord_877242) baseStart_877242 baseEnd_877242 := by
    simpa [prefixWord, tailWord_877242, baseEnd_877242] using wordTrace_append hprefix tailTrace_877242
  have hstable : (prefixWord ++ tailWord_877242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877242).length < 2 ^ (prefixWord ++ tailWord_877242).sum := by decide
  have hdescent : baseEnd_877242 < baseStart_877242 := by decide
  rcases family_descends (prefixWord ++ tailWord_877242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877274 : List Nat := [3, 1, 1, 2, 2, 2, 5, 1, 2, 3]
def baseStart_877274 : Nat := 118140960795 + 877274 * 2 ^ 59
def prefixEnd_877274 : Nat := 4983230072969 + 3 ^ 40 * 877274 * 2
def baseEnd_877274 : Nat := 300308818461670596760331

theorem tailTrace_877274 : CollatzResearch.WordTrace tailWord_877274 prefixEnd_877274 300308818461670596760331 := by
  unfold tailWord_877274
  simp only [CollatzResearch.WordTrace]
  refine ⟨7999202855948399829003719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21331207615862399544009917 7999202855948399829003719)
  ·
    refine ⟨11998804283922599743505579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7999202855948399829003719 11998804283922599743505579)
    ·
      refine ⟨17998206425883899615258369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11998804283922599743505579 17998206425883899615258369)
      ·
        refine ⟨13498654819412924711443777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17998206425883899615258369 13498654819412924711443777)
        ·
          refine ⟨10123991114559693533582833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13498654819412924711443777 10123991114559693533582833)
          ·
            refine ⟨7592993335919770150187125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10123991114559693533582833 7592993335919770150187125)
            ·
              refine ⟨711843125242478451580043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7592993335919770150187125 711843125242478451580043)
              ·
                refine ⟨1067764687863717677370065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 711843125242478451580043 1067764687863717677370065)
                ·
                  refine ⟨800823515897788258027549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1067764687863717677370065 800823515897788258027549)
                  ·
                    refine ⟨300308818461670596760331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 800823515897788258027549 300308818461670596760331)
                    ·
                      rfl

theorem cell22_877274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 5, 1, 2, 3].length) (baseStart_877274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_877274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_877274 prefixEnd_877274 := by exact prefixLift 877274
  have htrace : WordTrace (prefixWord ++ tailWord_877274) baseStart_877274 baseEnd_877274 := by
    simpa [prefixWord, tailWord_877274, baseEnd_877274] using wordTrace_append hprefix tailTrace_877274
  have hstable : (prefixWord ++ tailWord_877274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877274).length < 2 ^ (prefixWord ++ tailWord_877274).sum := by decide
  have hdescent : baseEnd_877274 < baseStart_877274 := by decide
  rcases family_descends (prefixWord ++ tailWord_877274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877315 : List Nat := [1, 1, 1, 3, 2, 2, 1, 6, 5]
def baseStart_877315 : Nat := 118140960795 + 877315 * 2 ^ 59
def prefixEnd_877315 : Nat := 4983230072969 + 3 ^ 40 * 877315 * 2
def baseEnd_877315 : Nat := 100107617866520052161735

theorem tailTrace_877315 : CollatzResearch.WordTrace tailWord_877315 prefixEnd_877315 100107617866520052161735 := by
  unfold tailWord_877315
  simp only [CollatzResearch.WordTrace]
  refine ⟨31998306816645063318257399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21332204544430042212171599 31998306816645063318257399)
  ·
    refine ⟨47997460224967594977386099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31998306816645063318257399 47997460224967594977386099)
    ·
      refine ⟨71996190337451392466079149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47997460224967594977386099 71996190337451392466079149)
      ·
        refine ⟨26998571376544272174779681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71996190337451392466079149 26998571376544272174779681)
        ·
          refine ⟨20248928532408204131084761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26998571376544272174779681 20248928532408204131084761)
          ·
            refine ⟨15186696399306153098313571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20248928532408204131084761 15186696399306153098313571)
            ·
              refine ⟨22780044598959229647470357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15186696399306153098313571 22780044598959229647470357)
              ·
                refine ⟨1067814590576213889725173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22780044598959229647470357 1067814590576213889725173)
                ·
                  refine ⟨100107617866520052161735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1067814590576213889725173 100107617866520052161735)
                  ·
                    rfl

theorem cell22_877315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 6, 5].length) (baseStart_877315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_877315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_877315 prefixEnd_877315 := by exact prefixLift 877315
  have htrace : WordTrace (prefixWord ++ tailWord_877315) baseStart_877315 baseEnd_877315 := by
    simpa [prefixWord, tailWord_877315, baseEnd_877315] using wordTrace_append hprefix tailTrace_877315
  have hstable : (prefixWord ++ tailWord_877315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877315).length < 2 ^ (prefixWord ++ tailWord_877315).sum := by decide
  have hdescent : baseEnd_877315 < baseStart_877315 := by decide
  rcases family_descends (prefixWord ++ tailWord_877315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877319 : List Nat := [1, 1, 4, 4, 1, 1, 3, 1, 3, 3]
def baseStart_877319 : Nat := 118140960795 + 877319 * 2 ^ 59
def prefixEnd_877319 : Nat := 4983230072969 + 3 ^ 40 * 877319 * 2
def baseEnd_877319 : Nat := 300324222881305479385193

theorem tailTrace_877319 : CollatzResearch.WordTrace tailWord_877319 prefixEnd_877319 300324222881305479385193 := by
  unfold tailWord_877319
  simp only [CollatzResearch.WordTrace]
  refine ⟨31998452708630572001403011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21332301805753714667602007 31998452708630572001403011)
  ·
    refine ⟨47997679062945858002104517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31998452708630572001403011 47997679062945858002104517)
    ·
      refine ⟨8999564824302348375394597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47997679062945858002104517 8999564824302348375394597)
      ·
        refine ⟨1687418404556690320386487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8999564824302348375394597 1687418404556690320386487)
        ·
          refine ⟨2531127606835035480579731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1687418404556690320386487 2531127606835035480579731)
          ·
            refine ⟨3796691410252553220869597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2531127606835035480579731 3796691410252553220869597)
            ·
              refine ⟨1423759278844707457826099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3796691410252553220869597 1423759278844707457826099)
              ·
                refine ⟨2135638918267061186739149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1423759278844707457826099 2135638918267061186739149)
                ·
                  refine ⟨800864594350147945027181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2135638918267061186739149 800864594350147945027181)
                  ·
                    refine ⟨300324222881305479385193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 800864594350147945027181 300324222881305479385193)
                    ·
                      rfl

theorem cell22_877319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 1, 3, 3].length) (baseStart_877319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_877319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_877319 prefixEnd_877319 := by exact prefixLift 877319
  have htrace : WordTrace (prefixWord ++ tailWord_877319) baseStart_877319 baseEnd_877319 := by
    simpa [prefixWord, tailWord_877319, baseEnd_877319] using wordTrace_append hprefix tailTrace_877319
  have hstable : (prefixWord ++ tailWord_877319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877319).length < 2 ^ (prefixWord ++ tailWord_877319).sum := by decide
  have hdescent : baseEnd_877319 < baseStart_877319 := by decide
  rcases family_descends (prefixWord ++ tailWord_877319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877366 : List Nat := [5, 1, 2, 2, 2, 1, 2, 2, 5]
def baseStart_877366 : Nat := 118140960795 + 877366 * 2 ^ 59
def prefixEnd_877366 : Nat := 4983230072969 + 3 ^ 40 * 877366 * 2
def baseEnd_877366 : Nat := 100113437313937674486683

theorem tailTrace_877366 : CollatzResearch.WordTrace tailWord_877366 prefixEnd_877366 100113437313937674486683 := by
  unfold tailWord_877366
  simp only [CollatzResearch.WordTrace]
  refine ⟨2000010433716268689272747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21333444626306866018909301 2000010433716268689272747)
  ·
    refine ⟨3000015650574403033909121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2000010433716268689272747 3000015650574403033909121)
    ·
      refine ⟨2250011737930802275431841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3000015650574403033909121 2250011737930802275431841)
      ·
        refine ⟨1687508803448101706573881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2250011737930802275431841 1687508803448101706573881)
        ·
          refine ⟨1265631602586076279930411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1687508803448101706573881 1265631602586076279930411)
          ·
            refine ⟨1898447403879114419895617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1265631602586076279930411 1898447403879114419895617)
            ·
              refine ⟨1423835552909335814921713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1898447403879114419895617 1423835552909335814921713)
              ·
                refine ⟨1067876664682001861191285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1423835552909335814921713 1067876664682001861191285)
                ·
                  refine ⟨100113437313937674486683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1067876664682001861191285 100113437313937674486683)
                  ·
                    rfl

theorem cell22_877366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 2, 5].length) (baseStart_877366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_877366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_877366 prefixEnd_877366 := by exact prefixLift 877366
  have htrace : WordTrace (prefixWord ++ tailWord_877366) baseStart_877366 baseEnd_877366 := by
    simpa [prefixWord, tailWord_877366, baseEnd_877366] using wordTrace_append hprefix tailTrace_877366
  have hstable : (prefixWord ++ tailWord_877366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877366).length < 2 ^ (prefixWord ++ tailWord_877366).sum := by decide
  have hdescent : baseEnd_877366 < baseStart_877366 := by decide
  rcases family_descends (prefixWord ++ tailWord_877366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877370 : List Nat := [3, 1, 1, 1, 7, 1, 2, 2, 1, 3]
def baseStart_877370 : Nat := 118140960795 + 877370 * 2 ^ 59
def prefixEnd_877370 : Nat := 4983230072969 + 3 ^ 40 * 877370 * 2
def baseEnd_877370 : Nat := 300341681223558346360037

theorem tailTrace_877370 : CollatzResearch.WordTrace tailWord_877370 prefixEnd_877370 300341681223558346360037 := by
  unfold tailWord_877370
  simp only [CollatzResearch.WordTrace]
  refine ⟨8000078207861451927877391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21333541887630538474339709 8000078207861451927877391)
  ·
    refine ⟨12000117311792177891816087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8000078207861451927877391 12000117311792177891816087)
    ·
      refine ⟨18000175967688266837724131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12000117311792177891816087 18000175967688266837724131)
      ·
        refine ⟨27000263951532400256586197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18000175967688266837724131 27000263951532400256586197)
        ·
          refine ⟨632818686364040631013739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 27000263951532400256586197 632818686364040631013739)
          ·
            refine ⟨949228029546060946520609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 632818686364040631013739 949228029546060946520609)
            ·
              refine ⟨711921022159545709890457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 949228029546060946520609 711921022159545709890457)
              ·
                refine ⟨533940766619659282417843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 711921022159545709890457 533940766619659282417843)
                ·
                  refine ⟨800911149929488923626765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 533940766619659282417843 800911149929488923626765)
                  ·
                    refine ⟨300341681223558346360037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 800911149929488923626765 300341681223558346360037)
                    ·
                      rfl

theorem cell22_877370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 2, 2, 1, 3].length) (baseStart_877370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_877370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_877370 prefixEnd_877370 := by exact prefixLift 877370
  have htrace : WordTrace (prefixWord ++ tailWord_877370) baseStart_877370 baseEnd_877370 := by
    simpa [prefixWord, tailWord_877370, baseEnd_877370] using wordTrace_append hprefix tailTrace_877370
  have hstable : (prefixWord ++ tailWord_877370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877370).length < 2 ^ (prefixWord ++ tailWord_877370).sum := by decide
  have hdescent : baseEnd_877370 < baseStart_877370 := by decide
  rcases family_descends (prefixWord ++ tailWord_877370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877435 : List Nat := [1, 1, 1, 1, 1, 5, 2, 1, 1, 8]
def baseStart_877435 : Nat := 118140960795 + 877435 * 2 ^ 59
def prefixEnd_877435 : Nat := 4983230072969 + 3 ^ 40 * 877435 * 2
def baseEnd_877435 : Nat := 300363932051919843484837

theorem tailTrace_877435 : CollatzResearch.WordTrace tailWord_877435 prefixEnd_877435 300363932051919843484837 := by
  unfold tailWord_877435
  simp only [CollatzResearch.WordTrace]
  refine ⟨32002683576210323812625759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21335122384140215875083839 32002683576210323812625759)
  ·
    refine ⟨48004025364315485718938639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32002683576210323812625759 48004025364315485718938639)
    ·
      refine ⟨72006038046473228578407959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48004025364315485718938639 72006038046473228578407959)
      ·
        refine ⟨108009057069709842867611939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72006038046473228578407959 108009057069709842867611939)
        ·
          refine ⟨162013585604564764301417909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108009057069709842867611939 162013585604564764301417909)
          ·
            refine ⟨15188773650427946653257929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 162013585604564764301417909 15188773650427946653257929)
            ·
              refine ⟨11391580237820959989943447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15188773650427946653257929 11391580237820959989943447)
              ·
                refine ⟨17087370356731439984915171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11391580237820959989943447 17087370356731439984915171)
                ·
                  refine ⟨25631055535097159977372757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17087370356731439984915171 25631055535097159977372757)
                  ·
                    refine ⟨300363932051919843484837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 25631055535097159977372757 300363932051919843484837)
                    ·
                      rfl

theorem cell22_877435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 8].length) (baseStart_877435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_877435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_877435 prefixEnd_877435 := by exact prefixLift 877435
  have htrace : WordTrace (prefixWord ++ tailWord_877435) baseStart_877435 baseEnd_877435 := by
    simpa [prefixWord, tailWord_877435, baseEnd_877435] using wordTrace_append hprefix tailTrace_877435
  have hstable : (prefixWord ++ tailWord_877435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877435).length < 2 ^ (prefixWord ++ tailWord_877435).sum := by decide
  have hdescent : baseEnd_877435 < baseStart_877435 := by decide
  rcases family_descends (prefixWord ++ tailWord_877435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877494 : List Nat := [5, 1, 4, 1, 1, 2, 2, 1, 2, 3]
def baseStart_877494 : Nat := 118140960795 + 877494 * 2 ^ 59
def prefixEnd_877494 : Nat := 4983230072969 + 3 ^ 40 * 877494 * 2
def baseEnd_877494 : Nat := 300384128957663356259657

theorem tailTrace_877494 : CollatzResearch.WordTrace tailWord_877494 prefixEnd_877494 300384128957663356259657 := by
  unfold tailWord_877494
  simp only [CollatzResearch.WordTrace]
  refine ⟨2000302217687286055563971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21336556988664384592682357 2000302217687286055563971)
  ·
    refine ⟨3000453326530929083345957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2000302217687286055563971 3000453326530929083345957)
    ·
      refine ⟨562584998724549203127367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3000453326530929083345957 562584998724549203127367)
      ·
        refine ⟨843877498086823804691051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 562584998724549203127367 843877498086823804691051)
        ·
          refine ⟨1265816247130235707036577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 843877498086823804691051 1265816247130235707036577)
          ·
            refine ⟨949362185347676780277433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1265816247130235707036577 949362185347676780277433)
            ·
              refine ⟨712021639010757585208075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 949362185347676780277433 712021639010757585208075)
              ·
                refine ⟨1068032458516136377812113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 712021639010757585208075 1068032458516136377812113)
                ·
                  refine ⟨801024343887102283359085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1068032458516136377812113 801024343887102283359085)
                  ·
                    refine ⟨300384128957663356259657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 801024343887102283359085 300384128957663356259657)
                    ·
                      rfl

theorem cell22_877494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_877494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_877494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_877494 prefixEnd_877494 := by exact prefixLift 877494
  have htrace : WordTrace (prefixWord ++ tailWord_877494) baseStart_877494 baseEnd_877494 := by
    simpa [prefixWord, tailWord_877494, baseEnd_877494] using wordTrace_append hprefix tailTrace_877494
  have hstable : (prefixWord ++ tailWord_877494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877494).length < 2 ^ (prefixWord ++ tailWord_877494).sum := by decide
  have hdescent : baseEnd_877494 < baseStart_877494 := by decide
  rcases family_descends (prefixWord ++ tailWord_877494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877544 : List Nat := [2, 1, 4, 1, 1, 1, 2, 3, 4, 3]
def baseStart_877544 : Nat := 118140960795 + 877544 * 2 ^ 59
def prefixEnd_877544 : Nat := 4983230072969 + 3 ^ 40 * 877544 * 2
def baseEnd_877544 : Nat := 300401244979479892509503

theorem tailTrace_877544 : CollatzResearch.WordTrace tailWord_877544 prefixEnd_877544 300401244979479892509503 := by
  unfold tailWord_877544
  simp only [CollatzResearch.WordTrace]
  refine ⟨16003329566407717714171843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21337772755210290285562457 16003329566407717714171843)
  ·
    refine ⟨24004994349611576571257765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16003329566407717714171843 24004994349611576571257765)
    ·
      refine ⟨4500936440552170607110831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24004994349611576571257765 4500936440552170607110831)
      ·
        refine ⟨6751404660828255910666247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4500936440552170607110831 6751404660828255910666247)
        ·
          refine ⟨10127106991242383865999371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6751404660828255910666247 10127106991242383865999371)
          ·
            refine ⟨15190660486863575798999057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10127106991242383865999371 15190660486863575798999057)
            ·
              refine ⟨11392995365147681849249293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15190660486863575798999057 11392995365147681849249293)
              ·
                refine ⟨4272373261930380693468485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11392995365147681849249293 4272373261930380693468485)
                ·
                  refine ⟨801069986611946380025341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4272373261930380693468485 801069986611946380025341)
                  ·
                    refine ⟨300401244979479892509503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 801069986611946380025341 300401244979479892509503)
                    ·
                      rfl

theorem cell22_877544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 3, 4, 3].length) (baseStart_877544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_877544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_877544 prefixEnd_877544 := by exact prefixLift 877544
  have htrace : WordTrace (prefixWord ++ tailWord_877544) baseStart_877544 baseEnd_877544 := by
    simpa [prefixWord, tailWord_877544, baseEnd_877544] using wordTrace_append hprefix tailTrace_877544
  have hstable : (prefixWord ++ tailWord_877544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877544).length < 2 ^ (prefixWord ++ tailWord_877544).sum := by decide
  have hdescent : baseEnd_877544 < baseStart_877544 := by decide
  rcases family_descends (prefixWord ++ tailWord_877544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877546 : List Nat := [3, 1, 3, 1, 2, 3, 1, 4, 4]
def baseStart_877546 : Nat := 118140960795 + 877546 * 2 ^ 59
def prefixEnd_877546 : Nat := 4983230072969 + 3 ^ 40 * 877546 * 2
def baseEnd_877546 : Nat := 100133976540117517986499

theorem tailTrace_877546 : CollatzResearch.WordTrace tailWord_877546 prefixEnd_877546 100133976540117517986499 := by
  unfold tailWord_877546
  simp only [CollatzResearch.WordTrace]
  refine ⟨8001683019702047442479123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21337821385872126513277661 8001683019702047442479123)
  ·
    refine ⟨12002524529553071163718685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8001683019702047442479123 12002524529553071163718685)
    ·
      refine ⟨4500946698582401686394507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12002524529553071163718685 4500946698582401686394507)
      ·
        refine ⟨6751420047873602529591761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4500946698582401686394507 6751420047873602529591761)
        ·
          refine ⟨5063565035905201897193821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6751420047873602529591761 5063565035905201897193821)
          ·
            refine ⟨1898836888464450711447683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5063565035905201897193821 1898836888464450711447683)
            ·
              refine ⟨2848255332696676067171525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1898836888464450711447683 2848255332696676067171525)
              ·
                refine ⟨534047874880626762594661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2848255332696676067171525 534047874880626762594661)
                ·
                  refine ⟨100133976540117517986499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 534047874880626762594661 100133976540117517986499)
                  ·
                    rfl

theorem cell22_877546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 4, 4].length) (baseStart_877546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_877546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_877546 prefixEnd_877546 := by exact prefixLift 877546
  have htrace : WordTrace (prefixWord ++ tailWord_877546) baseStart_877546 baseEnd_877546 := by
    simpa [prefixWord, tailWord_877546, baseEnd_877546] using wordTrace_append hprefix tailTrace_877546
  have hstable : (prefixWord ++ tailWord_877546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877546).length < 2 ^ (prefixWord ++ tailWord_877546).sum := by decide
  have hdescent : baseEnd_877546 < baseStart_877546 := by decide
  rcases family_descends (prefixWord ++ tailWord_877546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877576 : List Nat := [2, 1, 3, 2, 1, 5, 1, 1, 2, 4]
def baseStart_877576 : Nat := 118140960795 + 877576 * 2 ^ 59
def prefixEnd_877576 : Nat := 4983230072969 + 3 ^ 40 * 877576 * 2
def baseEnd_877576 : Nat := 300412199233442475709405

theorem tailTrace_877576 : CollatzResearch.WordTrace tailWord_877576 prefixEnd_877576 300412199233442475709405 := by
  unfold tailWord_877576
  simp only [CollatzResearch.WordTrace]
  refine ⟨16003913134349752446754291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21338550845799669929005721 16003913134349752446754291)
  ·
    refine ⟨24005869701524628670131437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16003913134349752446754291 24005869701524628670131437)
    ·
      refine ⟨9002201138071735751299289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24005869701524628670131437 9002201138071735751299289)
      ·
        refine ⟨6751650853553801813474467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9002201138071735751299289 6751650853553801813474467)
        ·
          refine ⟨10127476280330702720211701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6751650853553801813474467 10127476280330702720211701)
          ·
            refine ⟨949450901281003380019847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10127476280330702720211701 949450901281003380019847)
            ·
              refine ⟨1424176351921505070029771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 949450901281003380019847 1424176351921505070029771)
              ·
                refine ⟨2136264527882257605044657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1424176351921505070029771 2136264527882257605044657)
                ·
                  refine ⟨1602198395911693203783493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2136264527882257605044657 1602198395911693203783493)
                  ·
                    refine ⟨300412199233442475709405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1602198395911693203783493 300412199233442475709405)
                    ·
                      rfl

theorem cell22_877576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 1, 2, 4].length) (baseStart_877576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_877576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_877576 prefixEnd_877576 := by exact prefixLift 877576
  have htrace : WordTrace (prefixWord ++ tailWord_877576) baseStart_877576 baseEnd_877576 := by
    simpa [prefixWord, tailWord_877576, baseEnd_877576] using wordTrace_append hprefix tailTrace_877576
  have hstable : (prefixWord ++ tailWord_877576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877576).length < 2 ^ (prefixWord ++ tailWord_877576).sum := by decide
  have hdescent : baseEnd_877576 < baseStart_877576 := by decide
  rcases family_descends (prefixWord ++ tailWord_877576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877679 : List Nat := [1, 1, 2, 1, 3, 3, 2, 3, 1, 5]
def baseStart_877679 : Nat := 118140960795 + 877679 * 2 ^ 59
def prefixEnd_877679 : Nat := 4983230072969 + 3 ^ 40 * 877679 * 2
def baseEnd_877679 : Nat := 300447458238384540384089

theorem tailTrace_877679 : CollatzResearch.WordTrace tailWord_877679 prefixEnd_877679 300447458238384540384089 := by
  unfold tailWord_877679
  simp only [CollatzResearch.WordTrace]
  refine ⟨32011582987326353484508091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21341055324884235656338727 32011582987326353484508091)
  ·
    refine ⟨48017374480989530226762137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32011582987326353484508091 48017374480989530226762137)
    ·
      refine ⟨36013030860742147670071603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48017374480989530226762137 36013030860742147670071603)
      ·
        refine ⟨54019546291113221505107405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36013030860742147670071603 54019546291113221505107405)
        ·
          refine ⟨20257329859167458064415277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54019546291113221505107405 20257329859167458064415277)
          ·
            refine ⟨7596498697187796774155729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20257329859167458064415277 7596498697187796774155729)
            ·
              refine ⟨5697374022890847580616797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7596498697187796774155729 5697374022890847580616797)
              ·
                refine ⟨2136515258584067842731299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5697374022890847580616797 2136515258584067842731299)
                ·
                  refine ⟨3204772887876101764096949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2136515258584067842731299 3204772887876101764096949)
                  ·
                    refine ⟨300447458238384540384089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3204772887876101764096949 300447458238384540384089)
                    ·
                      rfl

theorem cell22_877679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 3, 1, 5].length) (baseStart_877679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_877679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_877679 prefixEnd_877679 := by exact prefixLift 877679
  have htrace : WordTrace (prefixWord ++ tailWord_877679) baseStart_877679 baseEnd_877679 := by
    simpa [prefixWord, tailWord_877679, baseEnd_877679] using wordTrace_append hprefix tailTrace_877679
  have hstable : (prefixWord ++ tailWord_877679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877679).length < 2 ^ (prefixWord ++ tailWord_877679).sum := by decide
  have hdescent : baseEnd_877679 < baseStart_877679 := by decide
  rcases family_descends (prefixWord ++ tailWord_877679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877754 : List Nat := [3, 1, 1, 1, 2, 2, 1, 4, 7]
def baseStart_877754 : Nat := 118140960795 + 877754 * 2 ^ 59
def prefixEnd_877754 : Nat := 4983230072969 + 3 ^ 40 * 877754 * 2
def baseEnd_877754 : Nat := 100157710757036448252953

theorem tailTrace_877754 : CollatzResearch.WordTrace tailWord_877754 prefixEnd_877754 100157710757036448252953 := by
  unfold tailWord_877754
  simp only [CollatzResearch.WordTrace]
  refine ⟨8003579615513660323372079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21342878974703094195658877 8003579615513660323372079)
  ·
    refine ⟨12005369423270490485058119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8003579615513660323372079 12005369423270490485058119)
    ·
      refine ⟨18008054134905735727587179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12005369423270490485058119 18008054134905735727587179)
      ·
        refine ⟨27012081202358603591380769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18008054134905735727587179 27012081202358603591380769)
        ·
          refine ⟨20259060901768952693535577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27012081202358603591380769 20259060901768952693535577)
          ·
            refine ⟨15194295676326714520151683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20259060901768952693535577 15194295676326714520151683)
            ·
              refine ⟨22791443514490071780227525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15194295676326714520151683 22791443514490071780227525)
              ·
                refine ⟨4273395658966888458792661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22791443514490071780227525 4273395658966888458792661)
                ·
                  refine ⟨100157710757036448252953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4273395658966888458792661 100157710757036448252953)
                  ·
                    rfl

theorem cell22_877754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4, 7].length) (baseStart_877754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_877754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_877754 prefixEnd_877754 := by exact prefixLift 877754
  have htrace : WordTrace (prefixWord ++ tailWord_877754) baseStart_877754 baseEnd_877754 := by
    simpa [prefixWord, tailWord_877754, baseEnd_877754] using wordTrace_append hprefix tailTrace_877754
  have hstable : (prefixWord ++ tailWord_877754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877754).length < 2 ^ (prefixWord ++ tailWord_877754).sum := by decide
  have hdescent : baseEnd_877754 < baseStart_877754 := by decide
  rcases family_descends (prefixWord ++ tailWord_877754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877861 : List Nat := [1, 3, 1, 2, 4, 1, 2, 8]
def baseStart_877861 : Nat := 118140960795 + 877861 * 2 ^ 59
def prefixEnd_877861 : Nat := 4983230072969 + 3 ^ 40 * 877861 * 2
def baseEnd_877861 : Nat := 33389973395310748037059

theorem tailTrace_877861 : CollatzResearch.WordTrace tailWord_877861 prefixEnd_877861 33389973395310748037059 := by
  unfold tailWord_877861
  simp only [CollatzResearch.WordTrace]
  refine ⟨32018221072666998567633437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21345480715111332378422291 32018221072666998567633437)
  ·
    refine ⟨12006832902250124462862539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32018221072666998567633437 12006832902250124462862539)
    ·
      refine ⟨18010249353375186694293809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12006832902250124462862539 18010249353375186694293809)
      ·
        refine ⟨13507687015031390020720357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18010249353375186694293809 13507687015031390020720357)
        ·
          refine ⟨2532691315318385628885067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13507687015031390020720357 2532691315318385628885067)
          ·
            refine ⟨3799036972977578443327601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2532691315318385628885067 3799036972977578443327601)
            ·
              refine ⟨2849277729733183832495701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3799036972977578443327601 2849277729733183832495701)
              ·
                refine ⟨33389973395310748037059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2849277729733183832495701 33389973395310748037059)
                ·
                  rfl

theorem cell22_877861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 8].length) (baseStart_877861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_877861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_877861 prefixEnd_877861 := by exact prefixLift 877861
  have htrace : WordTrace (prefixWord ++ tailWord_877861) baseStart_877861 baseEnd_877861 := by
    simpa [prefixWord, tailWord_877861, baseEnd_877861] using wordTrace_append hprefix tailTrace_877861
  have hstable : (prefixWord ++ tailWord_877861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877861).length < 2 ^ (prefixWord ++ tailWord_877861).sum := by decide
  have hdescent : baseEnd_877861 < baseStart_877861 := by decide
  rcases family_descends (prefixWord ++ tailWord_877861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877878 : List Nat := [5, 1, 2, 3, 11]
def baseStart_877878 : Nat := 118140960795 + 877878 * 2 ^ 59
def prefixEnd_877878 : Nat := 4983230072969 + 3 ^ 40 * 877878 * 2
def baseEnd_877878 : Nat := 1236689629651087879253

theorem tailTrace_877878 : CollatzResearch.WordTrace tailWord_877878 prefixEnd_877878 1236689629651087879253 := by
  unfold tailWord_877878
  simp only [CollatzResearch.WordTrace]
  refine ⟨2001177569600338154437643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21345894075736940314001525 2001177569600338154437643)
  ·
    refine ⟨3001766354400507231656465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2001177569600338154437643 3001766354400507231656465)
    ·
      refine ⟨2251324765800380423742349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3001766354400507231656465 2251324765800380423742349)
      ·
        refine ⟨844246787175142658903381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2251324765800380423742349 844246787175142658903381)
        ·
          refine ⟨1236689629651087879253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 844246787175142658903381 1236689629651087879253)
          ·
            rfl

theorem cell22_877878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 11].length) (baseStart_877878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_877878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_877878 prefixEnd_877878 := by exact prefixLift 877878
  have htrace : WordTrace (prefixWord ++ tailWord_877878) baseStart_877878 baseEnd_877878 := by
    simpa [prefixWord, tailWord_877878, baseEnd_877878] using wordTrace_append hprefix tailTrace_877878
  have hstable : (prefixWord ++ tailWord_877878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877878).length < 2 ^ (prefixWord ++ tailWord_877878).sum := by decide
  have hdescent : baseEnd_877878 < baseStart_877878 := by decide
  rcases family_descends (prefixWord ++ tailWord_877878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877906 : List Nat := [3, 2, 2, 1, 1, 1, 1, 2, 9]
def baseStart_877906 : Nat := 118140960795 + 877906 * 2 ^ 59
def prefixEnd_877906 : Nat := 4983230072969 + 3 ^ 40 * 877906 * 2
def baseEnd_877906 : Nat := 100175054992477204986131

theorem tailTrace_877906 : CollatzResearch.WordTrace tailWord_877906 prefixEnd_877906 100175054992477204986131 := by
  unfold tailWord_877906
  simp only [CollatzResearch.WordTrace]
  refine ⟨8004965589375992813255393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21346574905002647502014381 8004965589375992813255393)
  ·
    refine ⟨6003724192031994609941545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8004965589375992813255393 6003724192031994609941545)
    ·
      refine ⟨4502793144023995957456159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6003724192031994609941545 4502793144023995957456159)
      ·
        refine ⟨6754189716035993936184239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4502793144023995957456159 6754189716035993936184239)
        ·
          refine ⟨10131284574053990904276359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6754189716035993936184239 10131284574053990904276359)
          ·
            refine ⟨15196926861080986356414539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10131284574053990904276359 15196926861080986356414539)
            ·
              refine ⟨22795390291621479534621809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15196926861080986356414539 22795390291621479534621809)
              ·
                refine ⟨17096542718716109650966357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22795390291621479534621809 17096542718716109650966357)
                ·
                  refine ⟨100175054992477204986131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 17096542718716109650966357 100175054992477204986131)
                  ·
                    rfl

theorem cell22_877906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 9].length) (baseStart_877906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_877906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_877906 prefixEnd_877906 := by exact prefixLift 877906
  have htrace : WordTrace (prefixWord ++ tailWord_877906) baseStart_877906 baseEnd_877906 := by
    simpa [prefixWord, tailWord_877906, baseEnd_877906] using wordTrace_append hprefix tailTrace_877906
  have hstable : (prefixWord ++ tailWord_877906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877906).length < 2 ^ (prefixWord ++ tailWord_877906).sum := by decide
  have hdescent : baseEnd_877906 < baseStart_877906 := by decide
  rcases family_descends (prefixWord ++ tailWord_877906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877996 : List Nat := [2, 2, 1, 1, 1, 1, 14]
def baseStart_877996 : Nat := 118140960795 + 877996 * 2 ^ 59
def prefixEnd_877996 : Nat := 4983230072969 + 3 ^ 40 * 877996 * 2
def baseEnd_877996 : Nat := 11131702733951902970671

theorem tailTrace_877996 : CollatzResearch.WordTrace tailWord_877996 prefixEnd_877996 11131702733951902970671 := by
  unfold tailWord_877996
  simp only [CollatzResearch.WordTrace]
  refine ⟨16011572463588958311898921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21348763284785277749198561 16011572463588958311898921)
  ·
    refine ⟨12008679347691718733924191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16011572463588958311898921 12008679347691718733924191)
    ·
      refine ⟨18013019021537578100886287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12008679347691718733924191 18013019021537578100886287)
      ·
        refine ⟨27019528532306367151329431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18013019021537578100886287 27019528532306367151329431)
        ·
          refine ⟨40529292798459550726994147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27019528532306367151329431 40529292798459550726994147)
          ·
            refine ⟨60793939197689326090491221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40529292798459550726994147 60793939197689326090491221)
            ·
              refine ⟨11131702733951902970671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 60793939197689326090491221 11131702733951902970671)
              ·
                rfl

theorem cell22_877996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 14].length) (baseStart_877996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_877996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_877996 prefixEnd_877996 := by exact prefixLift 877996
  have htrace : WordTrace (prefixWord ++ tailWord_877996) baseStart_877996 baseEnd_877996 := by
    simpa [prefixWord, tailWord_877996, baseEnd_877996] using wordTrace_append hprefix tailTrace_877996
  have hstable : (prefixWord ++ tailWord_877996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877996).length < 2 ^ (prefixWord ++ tailWord_877996).sum := by decide
  have hdescent : baseEnd_877996 < baseStart_877996 := by decide
  rcases family_descends (prefixWord ++ tailWord_877996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878013 : List Nat := [1, 4, 1, 2, 2, 1, 4, 7]
def baseStart_878013 : Nat := 118140960795 + 878013 * 2 ^ 59
def prefixEnd_878013 : Nat := 4983230072969 + 3 ^ 40 * 878013 * 2
def baseEnd_878013 : Nat := 33395754807124333614785

theorem tailTrace_878013 : CollatzResearch.WordTrace tailWord_878013 prefixEnd_878013 33395754807124333614785 := by
  unfold tailWord_878013
  simp only [CollatzResearch.WordTrace]
  refine ⟨32023764968116328527166693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21349176645410885684777795 32023764968116328527166693)
  ·
    refine ⟨6004455931521811598843755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32023764968116328527166693 6004455931521811598843755)
    ·
      refine ⟨9006683897282717398265633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6004455931521811598843755 9006683897282717398265633)
      ·
        refine ⟨6755012922962038048699225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9006683897282717398265633 6755012922962038048699225)
        ·
          refine ⟨5066259692221528536524419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6755012922962038048699225 5066259692221528536524419)
          ·
            refine ⟨7599389538332292804786629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5066259692221528536524419 7599389538332292804786629)
            ·
              refine ⟨1424885538437304900897493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7599389538332292804786629 1424885538437304900897493)
              ·
                refine ⟨33395754807124333614785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1424885538437304900897493 33395754807124333614785)
                ·
                  rfl

theorem cell22_878013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 7].length) (baseStart_878013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_878013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_878013 prefixEnd_878013 := by exact prefixLift 878013
  have htrace : WordTrace (prefixWord ++ tailWord_878013) baseStart_878013 baseEnd_878013 := by
    simpa [prefixWord, tailWord_878013, baseEnd_878013] using wordTrace_append hprefix tailTrace_878013
  have hstable : (prefixWord ++ tailWord_878013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878013).length < 2 ^ (prefixWord ++ tailWord_878013).sum := by decide
  have hdescent : baseEnd_878013 < baseStart_878013 := by decide
  rcases family_descends (prefixWord ++ tailWord_878013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878135 : List Nat := [1, 1, 3, 1, 2, 4, 3, 1, 1, 5]
def baseStart_878135 : Nat := 118140960795 + 878135 * 2 ^ 59
def prefixEnd_878135 : Nat := 4983230072969 + 3 ^ 40 * 878135 * 2
def baseEnd_878135 : Nat := 300603556357351350982691

theorem tailTrace_878135 : CollatzResearch.WordTrace tailWord_878135 prefixEnd_878135 300603556357351350982691 := by
  unfold tailWord_878135
  simp only [CollatzResearch.WordTrace]
  refine ⟨32028214673674343363107859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21352143115782895575405239 32028214673674343363107859)
  ·
    refine ⟨48042322010511515044661789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32028214673674343363107859 48042322010511515044661789)
    ·
      refine ⟨18015870753941818141748171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48042322010511515044661789 18015870753941818141748171)
      ·
        refine ⟨27023806130912727212622257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18015870753941818141748171 27023806130912727212622257)
        ·
          refine ⟨20267854598184545409466693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27023806130912727212622257 20267854598184545409466693)
          ·
            refine ⟨3800222737159602264275005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20267854598184545409466693 3800222737159602264275005)
            ·
              refine ⟨1425083526434850849103127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3800222737159602264275005 1425083526434850849103127)
              ·
                refine ⟨2137625289652276273654691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1425083526434850849103127 2137625289652276273654691)
                ·
                  refine ⟨3206437934478414410482037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2137625289652276273654691 3206437934478414410482037)
                  ·
                    refine ⟨300603556357351350982691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3206437934478414410482037 300603556357351350982691)
                    ·
                      rfl

theorem cell22_878135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 1, 1, 5].length) (baseStart_878135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_878135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_878135 prefixEnd_878135 := by exact prefixLift 878135
  have htrace : WordTrace (prefixWord ++ tailWord_878135) baseStart_878135 baseEnd_878135 := by
    simpa [prefixWord, tailWord_878135, baseEnd_878135] using wordTrace_append hprefix tailTrace_878135
  have hstable : (prefixWord ++ tailWord_878135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878135).length < 2 ^ (prefixWord ++ tailWord_878135).sum := by decide
  have hdescent : baseEnd_878135 < baseStart_878135 := by decide
  rcases family_descends (prefixWord ++ tailWord_878135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878186 : List Nat := [3, 1, 3, 2, 1, 4, 2, 1, 2, 3]
def baseStart_878186 : Nat := 118140960795 + 878186 * 2 ^ 59
def prefixEnd_878186 : Nat := 4983230072969 + 3 ^ 40 * 878186 * 2
def baseEnd_878186 : Nat := 300621014699604217957535

theorem tailTrace_878186 : CollatzResearch.WordTrace tailWord_878186 prefixEnd_878186 300621014699604217957535 := by
  unfold tailWord_878186
  simp only [CollatzResearch.WordTrace]
  refine ⟨8007518699122394768303603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21353383197659719382142941 8007518699122394768303603)
  ·
    refine ⟨12011278048683592152455405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8007518699122394768303603 12011278048683592152455405)
    ·
      refine ⟨4504229268256347057170777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12011278048683592152455405 4504229268256347057170777)
      ·
        refine ⟨3378171951192260292878083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4504229268256347057170777 3378171951192260292878083)
        ·
          refine ⟨5067257926788390439317125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3378171951192260292878083 5067257926788390439317125)
          ·
            refine ⟨950110861272823207371961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5067257926788390439317125 950110861272823207371961)
            ·
              refine ⟨712583145954617405528971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 950110861272823207371961 712583145954617405528971)
              ·
                refine ⟨1068874718931926108293457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 712583145954617405528971 1068874718931926108293457)
                ·
                  refine ⟨801656039198944581220093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1068874718931926108293457 801656039198944581220093)
                  ·
                    refine ⟨300621014699604217957535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 801656039198944581220093 300621014699604217957535)
                    ·
                      rfl

theorem cell22_878186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 2, 1, 2, 3].length) (baseStart_878186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_878186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_878186 prefixEnd_878186 := by exact prefixLift 878186
  have htrace : WordTrace (prefixWord ++ tailWord_878186) baseStart_878186 baseEnd_878186 := by
    simpa [prefixWord, tailWord_878186, baseEnd_878186] using wordTrace_append hprefix tailTrace_878186
  have hstable : (prefixWord ++ tailWord_878186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878186).length < 2 ^ (prefixWord ++ tailWord_878186).sum := by decide
  have hdescent : baseEnd_878186 < baseStart_878186 := by decide
  rcases family_descends (prefixWord ++ tailWord_878186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878231 : List Nat := [1, 1, 3, 3, 2, 2, 4, 2, 1, 3]
def baseStart_878231 : Nat := 118140960795 + 878231 * 2 ^ 59
def prefixEnd_878231 : Nat := 4983230072969 + 3 ^ 40 * 878231 * 2
def baseEnd_878231 : Nat := 300636419119239100582397

theorem tailTrace_878231 : CollatzResearch.WordTrace tailWord_878231 prefixEnd_878231 300636419119239100582397 := by
  unfold tailWord_878231
  simp only [CollatzResearch.WordTrace]
  refine ⟨32031716081326551758602547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21354477387551034505735031 32031716081326551758602547)
  ·
    refine ⟨48047574121989827637903821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32031716081326551758602547 48047574121989827637903821)
    ·
      refine ⟨18017840295746185364213933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48047574121989827637903821 18017840295746185364213933)
      ·
        refine ⟨6756690110904819511580225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18017840295746185364213933 6756690110904819511580225)
        ·
          refine ⟨5067517583178614633685169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6756690110904819511580225 5067517583178614633685169)
          ·
            refine ⟨3800638187383960975263877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5067517583178614633685169 3800638187383960975263877)
            ·
              refine ⟨712619660134492682861977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3800638187383960975263877 712619660134492682861977)
              ·
                refine ⟨534464745100869512146483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 712619660134492682861977 534464745100869512146483)
                ·
                  refine ⟨801697117651304268219725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 534464745100869512146483 801697117651304268219725)
                  ·
                    refine ⟨300636419119239100582397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 801697117651304268219725 300636419119239100582397)
                    ·
                      rfl

theorem cell22_878231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 4, 2, 1, 3].length) (baseStart_878231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_878231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_878231 prefixEnd_878231 := by exact prefixLift 878231
  have htrace : WordTrace (prefixWord ++ tailWord_878231) baseStart_878231 baseEnd_878231 := by
    simpa [prefixWord, tailWord_878231, baseEnd_878231] using wordTrace_append hprefix tailTrace_878231
  have hstable : (prefixWord ++ tailWord_878231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878231).length < 2 ^ (prefixWord ++ tailWord_878231).sum := by decide
  have hdescent : baseEnd_878231 < baseStart_878231 := by decide
  rcases family_descends (prefixWord ++ tailWord_878231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878248 : List Nat := [2, 1, 7, 1, 1, 1, 1, 2, 3, 3]
def baseStart_878248 : Nat := 118140960795 + 878248 * 2 ^ 59
def prefixEnd_878248 : Nat := 4983230072969 + 3 ^ 40 * 878248 * 2
def baseEnd_878248 : Nat := 300642238566656722907345

theorem tailTrace_878248 : CollatzResearch.WordTrace tailWord_878248 prefixEnd_878248 300642238566656722907345 := by
  unfold tailWord_878248
  simp only [CollatzResearch.WordTrace]
  refine ⟨16016168061132481830985699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21354890748176642441314265 16016168061132481830985699)
  ·
    refine ⟨24024252091698722746478549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16016168061132481830985699 24024252091698722746478549)
    ·
      refine ⟨563068408399188814370591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 24024252091698722746478549 563068408399188814370591)
      ·
        refine ⟨844602612598783221555887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 563068408399188814370591 844602612598783221555887)
        ·
          refine ⟨1266903918898174832333831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 844602612598783221555887 1266903918898174832333831)
          ·
            refine ⟨1900355878347262248500747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1266903918898174832333831 1900355878347262248500747)
            ·
              refine ⟨2850533817520893372751121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1900355878347262248500747 2850533817520893372751121)
              ·
                refine ⟨2137900363140670029563341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2850533817520893372751121 2137900363140670029563341)
                ·
                  refine ⟨801712636177751261086253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2137900363140670029563341 801712636177751261086253)
                  ·
                    refine ⟨300642238566656722907345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 801712636177751261086253 300642238566656722907345)
                    ·
                      rfl

theorem cell22_878248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_878248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_878248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_878248 prefixEnd_878248 := by exact prefixLift 878248
  have htrace : WordTrace (prefixWord ++ tailWord_878248) baseStart_878248 baseEnd_878248 := by
    simpa [prefixWord, tailWord_878248, baseEnd_878248] using wordTrace_append hprefix tailTrace_878248
  have hstable : (prefixWord ++ tailWord_878248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878248).length < 2 ^ (prefixWord ++ tailWord_878248).sum := by decide
  have hdescent : baseEnd_878248 < baseStart_878248 := by decide
  rcases family_descends (prefixWord ++ tailWord_878248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878255 : List Nat := [1, 1, 2, 1, 2, 4, 3, 2, 6]
def baseStart_878255 : Nat := 118140960795 + 878255 * 2 ^ 59
def prefixEnd_878255 : Nat := 4983230072969 + 3 ^ 40 * 878255 * 2
def baseEnd_878255 : Nat := 100214878269903679327441

theorem tailTrace_878255 : CollatzResearch.WordTrace tailWord_878255 prefixEnd_878255 100214878269903679327441 := by
  unfold tailWord_878255
  simp only [CollatzResearch.WordTrace]
  refine ⟨32032591433239603857476219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21355060955493069238317479 32032591433239603857476219)
  ·
    refine ⟨48048887149859405786214329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32032591433239603857476219 48048887149859405786214329)
    ·
      refine ⟨36036665362394554339660747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48048887149859405786214329 36036665362394554339660747)
      ·
        refine ⟨54054998043591831509491121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36036665362394554339660747 54054998043591831509491121)
        ·
          refine ⟨40541248532693873632118341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54054998043591831509491121 40541248532693873632118341)
          ·
            refine ⟨7601484099880101306022189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40541248532693873632118341 7601484099880101306022189)
            ·
              refine ⟨2850556537455037989758321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7601484099880101306022189 2850556537455037989758321)
              ·
                refine ⟨2137917403091278492318741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2850556537455037989758321 2137917403091278492318741)
                ·
                  refine ⟨100214878269903679327441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2137917403091278492318741 100214878269903679327441)
                  ·
                    rfl

theorem cell22_878255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 2, 6].length) (baseStart_878255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_878255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_878255 prefixEnd_878255 := by exact prefixLift 878255
  have htrace : WordTrace (prefixWord ++ tailWord_878255) baseStart_878255 baseEnd_878255 := by
    simpa [prefixWord, tailWord_878255, baseEnd_878255] using wordTrace_append hprefix tailTrace_878255
  have hstable : (prefixWord ++ tailWord_878255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878255).length < 2 ^ (prefixWord ++ tailWord_878255).sum := by decide
  have hdescent : baseEnd_878255 < baseStart_878255 := by decide
  rcases family_descends (prefixWord ++ tailWord_878255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878278 : List Nat := [6, 1, 2, 1, 1, 3, 1, 2, 5]
def baseStart_878278 : Nat := 118140960795 + 878278 * 2 ^ 59
def prefixEnd_878278 : Nat := 4983230072969 + 3 ^ 40 * 878278 * 2
def baseEnd_878278 : Nat := 100217502726582214885751

theorem tailTrace_878278 : CollatzResearch.WordTrace tailWord_878278 prefixEnd_878278 100217502726582214885751 := by
  unfold tailWord_878278
  simp only [CollatzResearch.WordTrace]
  refine ⟨1001044697254883712048859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 21355620208104185857042325 1001044697254883712048859)
  ·
    refine ⟨1501567045882325568073289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1001044697254883712048859 1501567045882325568073289)
    ·
      refine ⟨1126175284411744176054967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1501567045882325568073289 1126175284411744176054967)
      ·
        refine ⟨1689262926617616264082451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1126175284411744176054967 1689262926617616264082451)
        ·
          refine ⟨2533894389926424396123677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1689262926617616264082451 2533894389926424396123677)
          ·
            refine ⟨950210396222409148546379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2533894389926424396123677 950210396222409148546379)
            ·
              refine ⟨1425315594333613722819569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 950210396222409148546379 1425315594333613722819569)
              ·
                refine ⟨1068986695750210292114677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1425315594333613722819569 1068986695750210292114677)
                ·
                  refine ⟨100217502726582214885751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1068986695750210292114677 100217502726582214885751)
                  ·
                    rfl

theorem cell22_878278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_878278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_878278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_878278 prefixEnd_878278 := by exact prefixLift 878278
  have htrace : WordTrace (prefixWord ++ tailWord_878278) baseStart_878278 baseEnd_878278 := by
    simpa [prefixWord, tailWord_878278, baseEnd_878278] using wordTrace_append hprefix tailTrace_878278
  have hstable : (prefixWord ++ tailWord_878278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878278).length < 2 ^ (prefixWord ++ tailWord_878278).sum := by decide
  have hdescent : baseEnd_878278 < baseStart_878278 := by decide
  rcases family_descends (prefixWord ++ tailWord_878278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878317 : List Nat := [1, 5, 1, 2, 1, 3, 1, 8]
def baseStart_878317 : Nat := 118140960795 + 878317 * 2 ^ 59
def prefixEnd_878317 : Nat := 4983230072969 + 3 ^ 40 * 878317 * 2
def baseEnd_878317 : Nat := 33407317630751504770237

theorem tailTrace_878317 : CollatzResearch.WordTrace tailWord_878317 prefixEnd_878317 33407317630751504770237 := by
  unfold tailWord_878317
  simp only [CollatzResearch.WordTrace]
  refine ⟨32034852759014988446233205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21356568506009992297488803 32034852759014988446233205)
  ·
    refine ⟨3003267446157655166834363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32034852759014988446233205 3003267446157655166834363)
    ·
      refine ⟨4504901169236482750251545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3003267446157655166834363 4504901169236482750251545)
      ·
        refine ⟨3378675876927362062688659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4504901169236482750251545 3378675876927362062688659)
        ·
          refine ⟨5068013815391043094032989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3378675876927362062688659 5068013815391043094032989)
          ·
            refine ⟨1900505180771641160262371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5068013815391043094032989 1900505180771641160262371)
            ·
              refine ⟨2850757771157461740393557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1900505180771641160262371 2850757771157461740393557)
              ·
                refine ⟨33407317630751504770237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2850757771157461740393557 33407317630751504770237)
                ·
                  rfl

theorem cell22_878317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 8].length) (baseStart_878317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_878317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_878317 prefixEnd_878317 := by exact prefixLift 878317
  have htrace : WordTrace (prefixWord ++ tailWord_878317) baseStart_878317 baseEnd_878317 := by
    simpa [prefixWord, tailWord_878317, baseEnd_878317] using wordTrace_append hprefix tailTrace_878317
  have hstable : (prefixWord ++ tailWord_878317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878317).length < 2 ^ (prefixWord ++ tailWord_878317).sum := by decide
  have hdescent : baseEnd_878317 < baseStart_878317 := by decide
  rcases family_descends (prefixWord ++ tailWord_878317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878330 : List Nat := [3, 1, 1, 1, 1, 3, 1, 2, 1, 8]
def baseStart_878330 : Nat := 118140960795 + 878330 * 2 ^ 59
def prefixEnd_878330 : Nat := 4983230072969 + 3 ^ 40 * 878330 * 2
def baseEnd_878330 : Nat := 300670308842435842357093

theorem tailTrace_878330 : CollatzResearch.WordTrace tailWord_878330 prefixEnd_878330 300670308842435842357093 := by
  unfold tailWord_878330
  simp only [CollatzResearch.WordTrace]
  refine ⟨8008831726991972916614111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21356884605311927777637629 8008831726991972916614111)
  ·
    refine ⟨12013247590487959374921167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8008831726991972916614111 12013247590487959374921167)
    ·
      refine ⟨18019871385731939062381751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12013247590487959374921167 18019871385731939062381751)
      ·
        refine ⟨27029807078597908593572627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18019871385731939062381751 27029807078597908593572627)
        ·
          refine ⟨40544710617896862890358941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27029807078597908593572627 40544710617896862890358941)
          ·
            refine ⟨15204266481711323583884603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40544710617896862890358941 15204266481711323583884603)
            ·
              refine ⟨22806399722566985375826905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15204266481711323583884603 22806399722566985375826905)
              ·
                refine ⟨17104799791925239031870179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22806399722566985375826905 17104799791925239031870179)
                ·
                  refine ⟨25657199687887858547805269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17104799791925239031870179 25657199687887858547805269)
                  ·
                    refine ⟨300670308842435842357093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 25657199687887858547805269 300670308842435842357093)
                    ·
                      rfl

theorem cell22_878330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 1, 8].length) (baseStart_878330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_878330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_878330 prefixEnd_878330 := by exact prefixLift 878330
  have htrace : WordTrace (prefixWord ++ tailWord_878330) baseStart_878330 baseEnd_878330 := by
    simpa [prefixWord, tailWord_878330, baseEnd_878330] using wordTrace_append hprefix tailTrace_878330
  have hstable : (prefixWord ++ tailWord_878330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878330).length < 2 ^ (prefixWord ++ tailWord_878330).sum := by decide
  have hdescent : baseEnd_878330 < baseStart_878330 := by decide
  rcases family_descends (prefixWord ++ tailWord_878330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878334 : List Nat := [4, 2, 2, 1, 3, 2, 8]
def baseStart_878334 : Nat := 118140960795 + 878334 * 2 ^ 59
def prefixEnd_878334 : Nat := 4983230072969 + 3 ^ 40 * 878334 * 2
def baseEnd_878334 : Nat := 11135988078673376491003

theorem tailTrace_878334 : CollatzResearch.WordTrace tailWord_878334 prefixEnd_878334 11135988078673376491003 := by
  unfold tailWord_878334
  simp only [CollatzResearch.WordTrace]
  refine ⟨4004434099994175043700257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21356981866635600233068037 4004434099994175043700257)
  ·
    refine ⟨3003325574995631282775193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4004434099994175043700257 3003325574995631282775193)
    ·
      refine ⟨2252494181246723462081395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3003325574995631282775193 2252494181246723462081395)
      ·
        refine ⟨3378741271870085193122093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2252494181246723462081395 3378741271870085193122093)
        ·
          refine ⟨1267027976951281947420785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3378741271870085193122093 1267027976951281947420785)
          ·
            refine ⟨950270982713461460565589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1267027976951281947420785 950270982713461460565589)
            ·
              refine ⟨11135988078673376491003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 950270982713461460565589 11135988078673376491003)
              ·
                rfl

theorem cell22_878334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 8].length) (baseStart_878334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_878334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_878334 prefixEnd_878334 := by exact prefixLift 878334
  have htrace : WordTrace (prefixWord ++ tailWord_878334) baseStart_878334 baseEnd_878334 := by
    simpa [prefixWord, tailWord_878334, baseEnd_878334] using wordTrace_append hprefix tailTrace_878334
  have hstable : (prefixWord ++ tailWord_878334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878334).length < 2 ^ (prefixWord ++ tailWord_878334).sum := by decide
  have hdescent : baseEnd_878334 < baseStart_878334 := by decide
  rcases family_descends (prefixWord ++ tailWord_878334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878439 : List Nat := [1, 1, 5, 1, 2, 1, 2, 2, 4, 3]
def baseStart_878439 : Nat := 118140960795 + 878439 * 2 ^ 59
def prefixEnd_878439 : Nat := 4983230072969 + 3 ^ 40 * 878439 * 2
def baseEnd_878439 : Nat := 300707621769995891381759

theorem tailTrace_878439 : CollatzResearch.WordTrace tailWord_878439 prefixEnd_878439 300707621769995891381759 := by
  unfold tailWord_878439
  simp only [CollatzResearch.WordTrace]
  refine ⟨32039302464573003282174371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21359534976382002188116247 32039302464573003282174371)
  ·
    refine ⟨48058953696859504923261557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32039302464573003282174371 48058953696859504923261557)
    ·
      refine ⟨4505526909080578586555771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48058953696859504923261557 4505526909080578586555771)
      ·
        refine ⟨6758290363620867879833657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4505526909080578586555771 6758290363620867879833657)
        ·
          refine ⟨5068717772715650909875243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6758290363620867879833657 5068717772715650909875243)
          ·
            refine ⟨7603076659073476364812865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5068717772715650909875243 7603076659073476364812865)
            ·
              refine ⟨5702307494305107273609649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7603076659073476364812865 5702307494305107273609649)
              ·
                refine ⟨4276730620728830455207237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5702307494305107273609649 4276730620728830455207237)
                ·
                  refine ⟨801886991386655710351357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4276730620728830455207237 801886991386655710351357)
                  ·
                    refine ⟨300707621769995891381759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 801886991386655710351357 300707621769995891381759)
                    ·
                      rfl

theorem cell22_878439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 2, 4, 3].length) (baseStart_878439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_878439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_878439 prefixEnd_878439 := by exact prefixLift 878439
  have htrace : WordTrace (prefixWord ++ tailWord_878439) baseStart_878439 baseEnd_878439 := by
    simpa [prefixWord, tailWord_878439, baseEnd_878439] using wordTrace_append hprefix tailTrace_878439
  have hstable : (prefixWord ++ tailWord_878439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878439).length < 2 ^ (prefixWord ++ tailWord_878439).sum := by decide
  have hdescent : baseEnd_878439 < baseStart_878439 := by decide
  rcases family_descends (prefixWord ++ tailWord_878439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878589 : List Nat := [1, 4, 1, 1, 1, 2, 2, 2, 4, 4]
def baseStart_878589 : Nat := 118140960795 + 878589 * 2 ^ 59
def prefixEnd_878589 : Nat := 4983230072969 + 3 ^ 40 * 878589 * 2
def baseEnd_878589 : Nat := 300758969835445500131299

theorem tailTrace_878589 : CollatzResearch.WordTrace tailWord_878589 prefixEnd_878589 300758969835445500131299 := by
  unfold tailWord_878589
  simp only [CollatzResearch.WordTrace]
  refine ⟨32044773414029578900134821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21363182276019719266756547 32044773414029578900134821)
  ·
    refine ⟨6008395015130546043775279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32044773414029578900134821 6008395015130546043775279)
    ·
      refine ⟨9012592522695819065662919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6008395015130546043775279 9012592522695819065662919)
      ·
        refine ⟨13518888784043728598494379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9012592522695819065662919 13518888784043728598494379)
        ·
          refine ⟨20278333176065592897741569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13518888784043728598494379 20278333176065592897741569)
          ·
            refine ⟨15208749882049194673306177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20278333176065592897741569 15208749882049194673306177)
            ·
              refine ⟨11406562411536896004979633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15208749882049194673306177 11406562411536896004979633)
              ·
                refine ⟨8554921808652672003734725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11406562411536896004979633 8554921808652672003734725)
                ·
                  refine ⟨1604047839122376000700261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8554921808652672003734725 1604047839122376000700261)
                  ·
                    refine ⟨300758969835445500131299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1604047839122376000700261 300758969835445500131299)
                    ·
                      rfl

theorem cell22_878589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 4, 4].length) (baseStart_878589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_878589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_878589 prefixEnd_878589 := by exact prefixLift 878589
  have htrace : WordTrace (prefixWord ++ tailWord_878589) baseStart_878589 baseEnd_878589 := by
    simpa [prefixWord, tailWord_878589, baseEnd_878589] using wordTrace_append hprefix tailTrace_878589
  have hstable : (prefixWord ++ tailWord_878589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878589).length < 2 ^ (prefixWord ++ tailWord_878589).sum := by decide
  have hdescent : baseEnd_878589 < baseStart_878589 := by decide
  rcases family_descends (prefixWord ++ tailWord_878589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
