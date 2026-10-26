import V185TrunkScan23Chunk1341

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7948080 : List Nat := [2, 1, 1, 1, 2, 2, 1, 1, 12]
def baseStart_7948080 : Nat := 118140960795 + 7948080 * 2 ^ 59
def prefixEnd_7948080 : Nat := 4983230072969 + 3 ^ 40 * 7948080 * 2
def baseEnd_7948080 : Nat := 453465035598596481571939

theorem tailTrace_7948080 : CollatzResearch.WordTrace tailWord_7948080 prefixEnd_7948080 453465035598596481571939 := by
  unfold tailWord_7948080
  simp only [CollatzResearch.WordTrace]
  refine ⟨144945146522735529419532847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193260195363647372559377129 144945146522735529419532847)
  ·
    refine ⟨217417719784103294129299271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144945146522735529419532847 217417719784103294129299271)
    ·
      refine ⟨326126579676154941193948907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217417719784103294129299271 326126579676154941193948907)
      ·
        refine ⟨489189869514232411790923361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326126579676154941193948907 489189869514232411790923361)
        ·
          refine ⟨366892402135674308843192521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 489189869514232411790923361 366892402135674308843192521)
          ·
            refine ⟨275169301601755731632394391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 366892402135674308843192521 275169301601755731632394391)
            ·
              refine ⟨412753952402633597448591587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275169301601755731632394391 412753952402633597448591587)
              ·
                refine ⟨619130928603950396172887381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 412753952402633597448591587 619130928603950396172887381)
                ·
                  refine ⟨453465035598596481571939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 619130928603950396172887381 453465035598596481571939)
                  ·
                    rfl

theorem cell23_7948080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 12].length) (baseStart_7948080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7948080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7948080 prefixEnd_7948080 := by exact prefixLift 7948080
  have htrace : WordTrace (prefixWord ++ tailWord_7948080) baseStart_7948080 baseEnd_7948080 := by
    simpa [prefixWord, tailWord_7948080, baseEnd_7948080] using wordTrace_append hprefix tailTrace_7948080
  have hstable : (prefixWord ++ tailWord_7948080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7948080).length < 2 ^ (prefixWord ++ tailWord_7948080).sum := by decide
  have hdescent : baseEnd_7948080 < baseStart_7948080 := by decide
  rcases family_descends (prefixWord ++ tailWord_7948080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7948101 : List Nat := [1, 3, 1, 1, 1, 2, 6, 3, 1, 4]
def baseStart_7948101 : Nat := 118140960795 + 7948101 * 2 ^ 59
def prefixEnd_7948101 : Nat := 4983230072969 + 3 ^ 40 * 7948101 * 2
def baseEnd_7948101 : Nat := 1360398701160370917328285

theorem tailTrace_7948101 : CollatzResearch.WordTrace tailWord_7948101 prefixEnd_7948101 1360398701160370917328285 := by
  unfold tailWord_7948101
  simp only [CollatzResearch.WordTrace]
  refine ⟨289891058978394979425580157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193260705985596652950386771 289891058978394979425580157)
  ·
    refine ⟨108709147116898117284592559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289891058978394979425580157 108709147116898117284592559)
    ·
      refine ⟨163063720675347175926888839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108709147116898117284592559 163063720675347175926888839)
      ·
        refine ⟨244595581013020763890333259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163063720675347175926888839 244595581013020763890333259)
        ·
          refine ⟨366893371519531145835499889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244595581013020763890333259 366893371519531145835499889)
          ·
            refine ⟨275170028639648359376624917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 366893371519531145835499889 275170028639648359376624917)
            ·
              refine ⟨12898595092483516845779293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 275170028639648359376624917 12898595092483516845779293)
              ·
                refine ⟨4836973159681318817167235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12898595092483516845779293 4836973159681318817167235)
                ·
                  refine ⟨7255459739521978225750853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4836973159681318817167235 7255459739521978225750853)
                  ·
                    refine ⟨1360398701160370917328285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7255459739521978225750853 1360398701160370917328285)
                    ·
                      rfl

theorem cell23_7948101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 3, 1, 4].length) (baseStart_7948101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7948101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7948101 prefixEnd_7948101 := by exact prefixLift 7948101
  have htrace : WordTrace (prefixWord ++ tailWord_7948101) baseStart_7948101 baseEnd_7948101 := by
    simpa [prefixWord, tailWord_7948101, baseEnd_7948101] using wordTrace_append hprefix tailTrace_7948101
  have hstable : (prefixWord ++ tailWord_7948101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7948101).length < 2 ^ (prefixWord ++ tailWord_7948101).sum := by decide
  have hdescent : baseEnd_7948101 < baseStart_7948101 := by decide
  rcases family_descends (prefixWord ++ tailWord_7948101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7948114 : List Nat := [3, 2, 2, 1, 1, 3, 3, 2, 6]
def baseStart_7948114 : Nat := 118140960795 + 7948114 * 2 ^ 59
def prefixEnd_7948114 : Nat := 4983230072969 + 3 ^ 40 * 7948114 * 2
def baseEnd_7948114 : Nat := 453466975414402355680255

theorem tailTrace_7948114 : CollatzResearch.WordTrace tailWord_7948114 prefixEnd_7948114 453466975414402355680255 := by
  unfold tailWord_7948114
  simp only [CollatzResearch.WordTrace]
  refine ⟨72472883281836970661450849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193261022084898588430535597 72472883281836970661450849)
  ·
    refine ⟨54354662461377727996088137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72472883281836970661450849 54354662461377727996088137)
    ·
      refine ⟨40765996846033295997066103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54354662461377727996088137 40765996846033295997066103)
      ·
        refine ⟨61148995269049943995599155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40765996846033295997066103 61148995269049943995599155)
        ·
          refine ⟨91723492903574915993398733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61148995269049943995599155 91723492903574915993398733)
          ·
            refine ⟨34396309838840593497524525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91723492903574915993398733 34396309838840593497524525)
            ·
              refine ⟨12898616189565222561571697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34396309838840593497524525 12898616189565222561571697)
              ·
                refine ⟨9673962142173916921178773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12898616189565222561571697 9673962142173916921178773)
                ·
                  refine ⟨453466975414402355680255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9673962142173916921178773 453466975414402355680255)
                  ·
                    rfl

theorem cell23_7948114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 2, 6].length) (baseStart_7948114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7948114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7948114 prefixEnd_7948114 := by exact prefixLift 7948114
  have htrace : WordTrace (prefixWord ++ tailWord_7948114) baseStart_7948114 baseEnd_7948114 := by
    simpa [prefixWord, tailWord_7948114, baseEnd_7948114] using wordTrace_append hprefix tailTrace_7948114
  have hstable : (prefixWord ++ tailWord_7948114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7948114).length < 2 ^ (prefixWord ++ tailWord_7948114).sum := by decide
  have hdescent : baseEnd_7948114 < baseStart_7948114 := by decide
  rcases family_descends (prefixWord ++ tailWord_7948114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7948117 : List Nat := [1, 3, 2, 2, 2, 2, 1, 1, 1, 2, 6]
def baseStart_7948117 : Nat := 118140960795 + 7948117 * 2 ^ 59
def prefixEnd_7948117 : Nat := 4983230072969 + 3 ^ 40 * 7948117 * 2
def baseEnd_7948117 : Nat := 4081204319171584689384781

theorem tailTrace_7948117 : CollatzResearch.WordTrace tailWord_7948117 prefixEnd_7948117 4081204319171584689384781 := by
  unfold tailWord_7948117
  simp only [CollatzResearch.WordTrace]
  refine ⟨289891642546337014158162605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193261095030891342772108403 289891642546337014158162605)
  ·
    refine ⟨108709365954876380309310977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289891642546337014158162605 108709365954876380309310977)
    ·
      refine ⟨81532024466157285231983233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108709365954876380309310977 81532024466157285231983233)
      ·
        refine ⟨61149018349617963923987425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81532024466157285231983233 61149018349617963923987425)
        ·
          refine ⟨45861763762213472942990569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61149018349617963923987425 45861763762213472942990569)
          ·
            refine ⟨34396322821660104707242927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45861763762213472942990569 34396322821660104707242927)
            ·
              refine ⟨51594484232490157060864391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34396322821660104707242927 51594484232490157060864391)
              ·
                refine ⟨77391726348735235591296587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51594484232490157060864391 77391726348735235591296587)
                ·
                  refine ⟨116087589523102853386944881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77391726348735235591296587 116087589523102853386944881)
                  ·
                    refine ⟨87065692142327140040208661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 116087589523102853386944881 87065692142327140040208661)
                    ·
                      refine ⟨4081204319171584689384781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87065692142327140040208661 4081204319171584689384781)
                      ·
                        rfl

theorem cell23_7948117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_7948117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7948117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7948117 prefixEnd_7948117 := by exact prefixLift 7948117
  have htrace : WordTrace (prefixWord ++ tailWord_7948117) baseStart_7948117 baseEnd_7948117 := by
    simpa [prefixWord, tailWord_7948117, baseEnd_7948117] using wordTrace_append hprefix tailTrace_7948117
  have hstable : (prefixWord ++ tailWord_7948117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7948117).length < 2 ^ (prefixWord ++ tailWord_7948117).sum := by decide
  have hdescent : baseEnd_7948117 < baseStart_7948117 := by decide
  rcases family_descends (prefixWord ++ tailWord_7948117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7948131 : List Nat := [1, 1, 1, 5, 4, 1, 3, 1, 6]
def baseStart_7948131 : Nat := 118140960795 + 7948131 * 2 ^ 59
def prefixEnd_7948131 : Nat := 4983230072969 + 3 ^ 40 * 7948131 * 2
def baseEnd_7948131 : Nat := 453467945322305292734413

theorem tailTrace_7948131 : CollatzResearch.WordTrace tailWord_7948131 prefixEnd_7948131 453467945322305292734413 := by
  unfold tailWord_7948131
  simp only [CollatzResearch.WordTrace]
  refine ⟨289892153168286294549172247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193261435445524196366114831 289892153168286294549172247)
  ·
    refine ⟨434838229752429441823758371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289892153168286294549172247 434838229752429441823758371)
    ·
      refine ⟨652257344628644162735637557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434838229752429441823758371 652257344628644162735637557)
      ·
        refine ⟨61149126058935390256466021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 652257344628644162735637557 61149126058935390256466021)
        ·
          refine ⟨11465461136050385673087379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61149126058935390256466021 11465461136050385673087379)
          ·
            refine ⟨17198191704075578509631069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11465461136050385673087379 17198191704075578509631069)
            ·
              refine ⟨6449321889028341941111651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17198191704075578509631069 6449321889028341941111651)
              ·
                refine ⟨9673982833542512911667477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6449321889028341941111651 9673982833542512911667477)
                ·
                  refine ⟨453467945322305292734413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9673982833542512911667477 453467945322305292734413)
                  ·
                    rfl

theorem cell23_7948131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 3, 1, 6].length) (baseStart_7948131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7948131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7948131 prefixEnd_7948131 := by exact prefixLift 7948131
  have htrace : WordTrace (prefixWord ++ tailWord_7948131) baseStart_7948131 baseEnd_7948131 := by
    simpa [prefixWord, tailWord_7948131, baseEnd_7948131] using wordTrace_append hprefix tailTrace_7948131
  have hstable : (prefixWord ++ tailWord_7948131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7948131).length < 2 ^ (prefixWord ++ tailWord_7948131).sum := by decide
  have hdescent : baseEnd_7948131 < baseStart_7948131 := by decide
  rcases family_descends (prefixWord ++ tailWord_7948131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7948141 : List Nat := [1, 5, 1, 1, 1, 1, 4, 2, 3, 1, 3]
def baseStart_7948141 : Nat := 118140960795 + 7948141 * 2 ^ 59
def prefixEnd_7948141 : Nat := 4983230072969 + 3 ^ 40 * 7948141 * 2
def baseEnd_7948141 : Nat := 4081216642707292595484671

theorem tailTrace_7948141 : CollatzResearch.WordTrace tailWord_7948141 prefixEnd_7948141 4081216642707292595484671 := by
  unfold tailWord_7948141
  simp only [CollatzResearch.WordTrace]
  refine ⟨289892517898250066257036277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193261678598833377504690851 289892517898250066257036277)
  ·
    refine ⟨27177423552960943711597151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 289892517898250066257036277 27177423552960943711597151)
    ·
      refine ⟨40766135329441415567395727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27177423552960943711597151 40766135329441415567395727)
      ·
        refine ⟨61149202994162123351093591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40766135329441415567395727 61149202994162123351093591)
        ·
          refine ⟨91723804491243185026640387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61149202994162123351093591 91723804491243185026640387)
          ·
            refine ⟨137585706736864777539960581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91723804491243185026640387 137585706736864777539960581)
            ·
              refine ⟨25797320013162145788742609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137585706736864777539960581 25797320013162145788742609)
              ·
                refine ⟨19347990009871609341556957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25797320013162145788742609 19347990009871609341556957)
                ·
                  refine ⟨7255496253701853503083859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19347990009871609341556957 7255496253701853503083859)
                  ·
                    refine ⟨10883244380552780254625789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7255496253701853503083859 10883244380552780254625789)
                    ·
                      refine ⟨4081216642707292595484671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10883244380552780254625789 4081216642707292595484671)
                      ·
                        rfl

theorem cell23_7948141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 2, 3, 1, 3].length) (baseStart_7948141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7948141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7948141 prefixEnd_7948141 := by exact prefixLift 7948141
  have htrace : WordTrace (prefixWord ++ tailWord_7948141) baseStart_7948141 baseEnd_7948141 := by
    simpa [prefixWord, tailWord_7948141, baseEnd_7948141] using wordTrace_append hprefix tailTrace_7948141
  have hstable : (prefixWord ++ tailWord_7948141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7948141).length < 2 ^ (prefixWord ++ tailWord_7948141).sum := by decide
  have hdescent : baseEnd_7948141 < baseStart_7948141 := by decide
  rcases family_descends (prefixWord ++ tailWord_7948141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7948157 : List Nat := [1, 4, 1, 1, 2, 1, 1, 3, 3, 6]
def baseStart_7948157 : Nat := 118140960795 + 7948157 * 2 ^ 59
def prefixEnd_7948157 : Nat := 4983230072969 + 3 ^ 40 * 7948157 * 2
def baseEnd_7948157 : Nat := 1360408286132588177628199

theorem tailTrace_7948157 : CollatzResearch.WordTrace tailWord_7948157 prefixEnd_7948157 1360408286132588177628199 := by
  unfold tailWord_7948157
  simp only [CollatzResearch.WordTrace]
  refine ⟨289893101466192100989618725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193262067644128067326412483 289893101466192100989618725)
  ·
    refine ⟨54354956524911018935553511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 289893101466192100989618725 54354956524911018935553511)
    ·
      refine ⟨81532434787366528403330267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54354956524911018935553511 81532434787366528403330267)
      ·
        refine ⟨122298652181049792604995401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81532434787366528403330267 122298652181049792604995401)
        ·
          refine ⟨91723989135787344453746551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122298652181049792604995401 91723989135787344453746551)
          ·
            refine ⟨137585983703681016680619827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91723989135787344453746551 137585983703681016680619827)
            ·
              refine ⟨206378975555521525020929741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137585983703681016680619827 206378975555521525020929741)
              ·
                refine ⟨77392115833320571882848653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 206378975555521525020929741 77392115833320571882848653)
                ·
                  refine ⟨29022043437495214456068245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77392115833320571882848653 29022043437495214456068245)
                  ·
                    refine ⟨1360408286132588177628199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29022043437495214456068245 1360408286132588177628199)
                    ·
                      rfl

theorem cell23_7948157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 3, 6].length) (baseStart_7948157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7948157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7948157 prefixEnd_7948157 := by exact prefixLift 7948157
  have htrace : WordTrace (prefixWord ++ tailWord_7948157) baseStart_7948157 baseEnd_7948157 := by
    simpa [prefixWord, tailWord_7948157, baseEnd_7948157] using wordTrace_append hprefix tailTrace_7948157
  have hstable : (prefixWord ++ tailWord_7948157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7948157).length < 2 ^ (prefixWord ++ tailWord_7948157).sum := by decide
  have hdescent : baseEnd_7948157 < baseStart_7948157 := by decide
  rcases family_descends (prefixWord ++ tailWord_7948157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7948168 : List Nat := [2, 1, 3, 3, 3, 1, 1, 2, 2, 3, 2]
def baseStart_7948168 : Nat := 118140960795 + 7948168 * 2 ^ 59
def prefixEnd_7948168 : Nat := 4983230072969 + 3 ^ 40 * 7948168 * 2
def baseEnd_7948168 : Nat := 4081230506684963989847047

theorem tailTrace_7948168 : CollatzResearch.WordTrace tailWord_7948168 prefixEnd_7948168 4081230506684963989847047 := by
  unfold tailWord_7948168
  simp only [CollatzResearch.WordTrace]
  refine ⟨144946751334576124934134579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193262335112768166578846105 144946751334576124934134579)
  ·
    refine ⟨217420127001864187401201869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144946751334576124934134579 217420127001864187401201869)
    ·
      refine ⟨81532547625699070275450701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217420127001864187401201869 81532547625699070275450701)
      ·
        refine ⟨30574705359637151353294013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81532547625699070275450701 30574705359637151353294013)
        ·
          refine ⟨11465514509863931757485255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30574705359637151353294013 11465514509863931757485255)
          ·
            refine ⟨17198271764795897636227883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11465514509863931757485255 17198271764795897636227883)
            ·
              refine ⟨25797407647193846454341825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17198271764795897636227883 25797407647193846454341825)
              ·
                refine ⟨19348055735395384840756369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25797407647193846454341825 19348055735395384840756369)
                ·
                  refine ⟨14511041801546538630567277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19348055735395384840756369 14511041801546538630567277)
                  ·
                    refine ⟨5441640675579951986462729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14511041801546538630567277 5441640675579951986462729)
                    ·
                      refine ⟨4081230506684963989847047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5441640675579951986462729 4081230506684963989847047)
                      ·
                        rfl

theorem cell23_7948168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 2, 2, 3, 2].length) (baseStart_7948168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7948168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7948168 prefixEnd_7948168 := by exact prefixLift 7948168
  have htrace : WordTrace (prefixWord ++ tailWord_7948168) baseStart_7948168 baseEnd_7948168 := by
    simpa [prefixWord, tailWord_7948168, baseEnd_7948168] using wordTrace_append hprefix tailTrace_7948168
  have hstable : (prefixWord ++ tailWord_7948168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7948168).length < 2 ^ (prefixWord ++ tailWord_7948168).sum := by decide
  have hdescent : baseEnd_7948168 < baseStart_7948168 := by decide
  rcases family_descends (prefixWord ++ tailWord_7948168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7948177 : List Nat := [1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 6]
def baseStart_7948177 : Nat := 118140960795 + 7948177 * 2 ^ 59
def prefixEnd_7948177 : Nat := 4983230072969 + 3 ^ 40 * 7948177 * 2
def baseEnd_7948177 : Nat := 4081235128010854454634505

theorem tailTrace_7948177 : CollatzResearch.WordTrace tailWord_7948177 prefixEnd_7948177 4081235128010854454634505 := by
  unfold tailWord_7948177
  simp only [CollatzResearch.WordTrace]
  refine ⟨289893830926119644405346785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193262553950746429603564523 289893830926119644405346785)
  ·
    refine ⟨217420373194589733304010089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289893830926119644405346785 217420373194589733304010089)
    ·
      refine ⟨163065279895942299978007567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217420373194589733304010089 163065279895942299978007567)
      ·
        refine ⟨244597919843913449967011351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163065279895942299978007567 244597919843913449967011351)
        ·
          refine ⟨366896879765870174950517027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244597919843913449967011351 366896879765870174950517027)
          ·
            refine ⟨550345319648805262425775541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366896879765870174950517027 550345319648805262425775541)
            ·
              refine ⟨51594873717075493352416457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 550345319648805262425775541 51594873717075493352416457)
              ·
                refine ⟨38696155287806620014312343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51594873717075493352416457 38696155287806620014312343)
                ·
                  refine ⟨58044232931709930021468515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38696155287806620014312343 58044232931709930021468515)
                  ·
                    refine ⟨87066349397564895032202773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58044232931709930021468515 87066349397564895032202773)
                    ·
                      refine ⟨4081235128010854454634505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87066349397564895032202773 4081235128010854454634505)
                      ·
                        rfl

theorem cell23_7948177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 6].length) (baseStart_7948177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7948177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7948177 prefixEnd_7948177 := by exact prefixLift 7948177
  have htrace : WordTrace (prefixWord ++ tailWord_7948177) baseStart_7948177 baseEnd_7948177 := by
    simpa [prefixWord, tailWord_7948177, baseEnd_7948177] using wordTrace_append hprefix tailTrace_7948177
  have hstable : (prefixWord ++ tailWord_7948177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7948177).length < 2 ^ (prefixWord ++ tailWord_7948177).sum := by decide
  have hdescent : baseEnd_7948177 < baseStart_7948177 := by decide
  rcases family_descends (prefixWord ++ tailWord_7948177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7948182 : List Nat := [5, 3, 1, 1, 2, 2, 2, 1, 6]
def baseStart_7948182 : Nat := 118140960795 + 7948182 * 2 ^ 59
def prefixEnd_7948182 : Nat := 4983230072969 + 3 ^ 40 * 7948182 * 2
def baseEnd_7948182 : Nat := 453470855046014103896887

theorem tailTrace_7948182 : CollatzResearch.WordTrace tailWord_7948182 prefixEnd_7948182 453470855046014103896887 := by
  unfold tailWord_7948182
  simp only [CollatzResearch.WordTrace]
  refine ⟨18118375830693845641204925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 193262675527401020172852533 18118375830693845641204925)
  ·
    refine ⟨6794390936510192115451847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18118375830693845641204925 6794390936510192115451847)
    ·
      refine ⟨10191586404765288173177771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6794390936510192115451847 10191586404765288173177771)
      ·
        refine ⟨15287379607147932259766657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10191586404765288173177771 15287379607147932259766657)
        ·
          refine ⟨11465534705360949194824993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15287379607147932259766657 11465534705360949194824993)
          ·
            refine ⟨8599151029020711896118745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11465534705360949194824993 8599151029020711896118745)
            ·
              refine ⟨6449363271765533922089059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8599151029020711896118745 6449363271765533922089059)
              ·
                refine ⟨9674044907648300883133589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6449363271765533922089059 9674044907648300883133589)
                ·
                  refine ⟨453470855046014103896887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9674044907648300883133589 453470855046014103896887)
                  ·
                    rfl

theorem cell23_7948182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_7948182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7948182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7948182 prefixEnd_7948182 := by exact prefixLift 7948182
  have htrace : WordTrace (prefixWord ++ tailWord_7948182) baseStart_7948182 baseEnd_7948182 := by
    simpa [prefixWord, tailWord_7948182, baseEnd_7948182] using wordTrace_append hprefix tailTrace_7948182
  have hstable : (prefixWord ++ tailWord_7948182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7948182).length < 2 ^ (prefixWord ++ tailWord_7948182).sum := by decide
  have hdescent : baseEnd_7948182 < baseStart_7948182 := by decide
  rcases family_descends (prefixWord ++ tailWord_7948182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7948232 : List Nat := [2, 1, 3, 1, 4, 1, 4, 2, 1, 2, 2]
def baseStart_7948232 : Nat := 118140960795 + 7948232 * 2 ^ 59
def prefixEnd_7948232 : Nat := 4983230072969 + 3 ^ 40 * 7948232 * 2
def baseEnd_7948232 : Nat := 4081263369446851739446753

theorem tailTrace_7948232 : CollatzResearch.WordTrace tailWord_7948232 prefixEnd_7948232 4081263369446851739446753 := by
  unfold tailWord_7948232
  simp only [CollatzResearch.WordTrace]
  refine ⟨144947918470460194399299475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193263891293946925865732633 144947918470460194399299475)
  ·
    refine ⟨217421877705690291598949213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144947918470460194399299475 217421877705690291598949213)
    ·
      refine ⟨81533204139633859349605955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217421877705690291598949213 81533204139633859349605955)
      ·
        refine ⟨122299806209450789024408933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81533204139633859349605955 122299806209450789024408933)
        ·
          refine ⟨22931213664272022942076675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122299806209450789024408933 22931213664272022942076675)
          ·
            refine ⟨34396820496408034413115013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22931213664272022942076675 34396820496408034413115013)
            ·
              refine ⟨6449403843076506452459065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34396820496408034413115013 6449403843076506452459065)
              ·
                refine ⟨4837052882307379839344299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6449403843076506452459065 4837052882307379839344299)
                ·
                  refine ⟨7255579323461069759016449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4837052882307379839344299 7255579323461069759016449)
                  ·
                    refine ⟨5441684492595802319262337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7255579323461069759016449 5441684492595802319262337)
                    ·
                      refine ⟨4081263369446851739446753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5441684492595802319262337 4081263369446851739446753)
                      ·
                        rfl

theorem cell23_7948232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 4, 2, 1, 2, 2].length) (baseStart_7948232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7948232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7948232 prefixEnd_7948232 := by exact prefixLift 7948232
  have htrace : WordTrace (prefixWord ++ tailWord_7948232) baseStart_7948232 baseEnd_7948232 := by
    simpa [prefixWord, tailWord_7948232, baseEnd_7948232] using wordTrace_append hprefix tailTrace_7948232
  have hstable : (prefixWord ++ tailWord_7948232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7948232).length < 2 ^ (prefixWord ++ tailWord_7948232).sum := by decide
  have hdescent : baseEnd_7948232 < baseStart_7948232 := by decide
  rcases family_descends (prefixWord ++ tailWord_7948232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7948269 : List Nat := [1, 5, 1, 4, 2, 1, 2, 1, 1, 2, 3]
def baseStart_7948269 : Nat := 118140960795 + 7948269 * 2 ^ 59
def prefixEnd_7948269 : Nat := 4983230072969 + 3 ^ 40 * 7948269 * 2
def baseEnd_7948269 : Nat := 4081282368231068094684083

theorem tailTrace_7948269 : CollatzResearch.WordTrace tailWord_7948269 prefixEnd_7948269 4081282368231068094684083 := by
  unfold tailWord_7948269
  simp only [CollatzResearch.WordTrace]
  refine ⟨289897186441786344117695861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193264790961190896078463907 289897186441786344117695861)
  ·
    refine ⟨27177861228917469761033987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 289897186441786344117695861 27177861228917469761033987)
    ·
      refine ⟨40766791843376204641550981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27177861228917469761033987 40766791843376204641550981)
      ·
        refine ⟨7643773470633038370290809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40766791843376204641550981 7643773470633038370290809)
        ·
          refine ⟨5732830102974778777718107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7643773470633038370290809 5732830102974778777718107)
          ·
            refine ⟨8599245154462168166577161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5732830102974778777718107 8599245154462168166577161)
            ·
              refine ⟨6449433865846626124932871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8599245154462168166577161 6449433865846626124932871)
              ·
                refine ⟨9674150798769939187399307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6449433865846626124932871 9674150798769939187399307)
                ·
                  refine ⟨14511226198154908781098961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9674150798769939187399307 14511226198154908781098961)
                  ·
                    refine ⟨10883419648616181585824221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14511226198154908781098961 10883419648616181585824221)
                    ·
                      refine ⟨4081282368231068094684083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10883419648616181585824221 4081282368231068094684083)
                      ·
                        rfl

theorem cell23_7948269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_7948269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7948269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7948269 prefixEnd_7948269 := by exact prefixLift 7948269
  have htrace : WordTrace (prefixWord ++ tailWord_7948269) baseStart_7948269 baseEnd_7948269 := by
    simpa [prefixWord, tailWord_7948269, baseEnd_7948269] using wordTrace_append hprefix tailTrace_7948269
  have hstable : (prefixWord ++ tailWord_7948269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7948269).length < 2 ^ (prefixWord ++ tailWord_7948269).sum := by decide
  have hdescent : baseEnd_7948269 < baseStart_7948269 := by decide
  rcases family_descends (prefixWord ++ tailWord_7948269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7948271 : List Nat := [1, 1, 2, 1, 4, 2, 1, 4, 1, 4, 2]
def baseStart_7948271 : Nat := 118140960795 + 7948271 * 2 ^ 59
def prefixEnd_7948271 : Nat := 4983230072969 + 3 ^ 40 * 7948271 * 2
def baseEnd_7948271 : Nat := 4081283395192377086859073

theorem tailTrace_7948271 : CollatzResearch.WordTrace tailWord_7948271 prefixEnd_7948271 4081283395192377086859073 := by
  unfold tailWord_7948271
  simp only [CollatzResearch.WordTrace]
  refine ⟨289897259387779098459268667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193264839591852732306179111 289897259387779098459268667)
  ·
    refine ⟨434845889081668647688903001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289897259387779098459268667 434845889081668647688903001)
    ·
      refine ⟨326134416811251485766677251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 434845889081668647688903001 326134416811251485766677251)
      ·
        refine ⟨489201625216877228650015877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326134416811251485766677251 489201625216877228650015877)
        ·
          refine ⟨91725304728164480371877977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 489201625216877228650015877 91725304728164480371877977)
          ·
            refine ⟨68793978546123360278908483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91725304728164480371877977 68793978546123360278908483)
            ·
              refine ⟨103190967819185040418362725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68793978546123360278908483 103190967819185040418362725)
              ·
                refine ⟨19348306466097195078443011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103190967819185040418362725 19348306466097195078443011)
                ·
                  refine ⟨29022459699145792617664517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19348306466097195078443011 29022459699145792617664517)
                  ·
                    refine ⟨5441711193589836115812097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29022459699145792617664517 5441711193589836115812097)
                    ·
                      refine ⟨4081283395192377086859073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5441711193589836115812097 4081283395192377086859073)
                      ·
                        rfl

theorem cell23_7948271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 4, 1, 4, 2].length) (baseStart_7948271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7948271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7948271 prefixEnd_7948271 := by exact prefixLift 7948271
  have htrace : WordTrace (prefixWord ++ tailWord_7948271) baseStart_7948271 baseEnd_7948271 := by
    simpa [prefixWord, tailWord_7948271, baseEnd_7948271] using wordTrace_append hprefix tailTrace_7948271
  have hstable : (prefixWord ++ tailWord_7948271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7948271).length < 2 ^ (prefixWord ++ tailWord_7948271).sum := by decide
  have hdescent : baseEnd_7948271 < baseStart_7948271 := by decide
  rcases family_descends (prefixWord ++ tailWord_7948271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7948284 : List Nat := [2, 2, 2, 1, 2, 2, 1, 1, 4, 2, 4]
def baseStart_7948284 : Nat := 118140960795 + 7948284 * 2 ^ 59
def prefixEnd_7948284 : Nat := 4983230072969 + 3 ^ 40 * 7948284 * 2
def baseEnd_7948284 : Nat := 4081290070440885535996513

theorem tailTrace_7948284 : CollatzResearch.WordTrace tailWord_7948284 prefixEnd_7948284 4081290070440885535996513 := by
  unfold tailWord_7948284
  simp only [CollatzResearch.WordTrace]
  refine ⟨144948866768366000839745953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193265155691154667786327937 144948866768366000839745953)
  ·
    refine ⟨108711650076274500629809465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144948866768366000839745953 108711650076274500629809465)
    ·
      refine ⟨81533737557205875472357099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108711650076274500629809465 81533737557205875472357099)
      ·
        refine ⟨122300606335808813208535649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81533737557205875472357099 122300606335808813208535649)
        ·
          refine ⟨91725454751856609906401737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122300606335808813208535649 91725454751856609906401737)
          ·
            refine ⟨68794091063892457429801303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91725454751856609906401737 68794091063892457429801303)
            ·
              refine ⟨103191136595838686144701955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68794091063892457429801303 103191136595838686144701955)
              ·
                refine ⟨154786704893758029217052933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103191136595838686144701955 154786704893758029217052933)
                ·
                  refine ⟨29022507167579630478197425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 154786704893758029217052933 29022507167579630478197425)
                  ·
                    refine ⟨21766880375684722858648069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29022507167579630478197425 21766880375684722858648069)
                    ·
                      refine ⟨4081290070440885535996513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21766880375684722858648069 4081290070440885535996513)
                      ·
                        rfl

theorem cell23_7948284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 4, 2, 4].length) (baseStart_7948284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7948284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7948284 prefixEnd_7948284 := by exact prefixLift 7948284
  have htrace : WordTrace (prefixWord ++ tailWord_7948284) baseStart_7948284 baseEnd_7948284 := by
    simpa [prefixWord, tailWord_7948284, baseEnd_7948284] using wordTrace_append hprefix tailTrace_7948284
  have hstable : (prefixWord ++ tailWord_7948284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7948284).length < 2 ^ (prefixWord ++ tailWord_7948284).sum := by decide
  have hdescent : baseEnd_7948284 < baseStart_7948284 := by decide
  rcases family_descends (prefixWord ++ tailWord_7948284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7948288 : List Nat := [2, 1, 1, 2, 1, 1, 1, 8, 2, 2, 2]
def baseStart_7948288 : Nat := 118140960795 + 7948288 * 2 ^ 59
def prefixEnd_7948288 : Nat := 4983230072969 + 3 ^ 40 * 7948288 * 2
def baseEnd_7948288 : Nat := 4081292124363503520346495

theorem tailTrace_7948288 : CollatzResearch.WordTrace tailWord_7948288 prefixEnd_7948288 4081292124363503520346495 := by
  unfold tailWord_7948288
  simp only [CollatzResearch.WordTrace]
  refine ⟨144948939714358755181318759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193265252952478340241758345 144948939714358755181318759)
  ·
    refine ⟨217423409571538132771978139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144948939714358755181318759 217423409571538132771978139)
    ·
      refine ⟨326135114357307199157967209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217423409571538132771978139 326135114357307199157967209)
      ·
        refine ⟨244601335767980399368475407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326135114357307199157967209 244601335767980399368475407)
        ·
          refine ⟨366902003651970599052713111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244601335767980399368475407 366902003651970599052713111)
          ·
            refine ⟨550353005477955898579069667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366902003651970599052713111 550353005477955898579069667)
            ·
              refine ⟨825529508216933847868604501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 550353005477955898579069667 825529508216933847868604501)
              ·
                refine ⟨9674173924417193529710209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 825529508216933847868604501 9674173924417193529710209)
                ·
                  refine ⟨7255630443312895147282657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9674173924417193529710209 7255630443312895147282657)
                  ·
                    refine ⟨5441722832484671360461993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7255630443312895147282657 5441722832484671360461993)
                    ·
                      refine ⟨4081292124363503520346495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5441722832484671360461993 4081292124363503520346495)
                      ·
                        rfl

theorem cell23_7948288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 8, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 8, 2, 2, 2].length) (baseStart_7948288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7948288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7948288 prefixEnd_7948288 := by exact prefixLift 7948288
  have htrace : WordTrace (prefixWord ++ tailWord_7948288) baseStart_7948288 baseEnd_7948288 := by
    simpa [prefixWord, tailWord_7948288, baseEnd_7948288] using wordTrace_append hprefix tailTrace_7948288
  have hstable : (prefixWord ++ tailWord_7948288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7948288).length < 2 ^ (prefixWord ++ tailWord_7948288).sum := by decide
  have hdescent : baseEnd_7948288 < baseStart_7948288 := by decide
  rcases family_descends (prefixWord ++ tailWord_7948288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7948345 : List Nat := [1, 2, 1, 5, 3, 1, 3, 2, 5]
def baseStart_7948345 : Nat := 118140960795 + 7948345 * 2 ^ 59
def prefixEnd_7948345 : Nat := 4983230072969 + 3 ^ 40 * 7948345 * 2
def baseEnd_7948345 : Nat := 453480154751201088592637

theorem tailTrace_7948345 : CollatzResearch.WordTrace tailWord_7948345 prefixEnd_7948345 453480154751201088592637 := by
  unfold tailWord_7948345
  simp only [CollatzResearch.WordTrace]
  refine ⟨289899958389511009097462489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193266638926340672731641659 289899958389511009097462489)
  ·
    refine ⟨217424968792133256823096867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289899958389511009097462489 217424968792133256823096867)
    ·
      refine ⟨326137453188199885234645301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217424968792133256823096867 326137453188199885234645301)
      ·
        refine ⟨30575386236393739240747997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 326137453188199885234645301 30575386236393739240747997)
        ·
          refine ⟨11465769838647652215280499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30575386236393739240747997 11465769838647652215280499)
          ·
            refine ⟨17198654757971478322920749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11465769838647652215280499 17198654757971478322920749)
            ·
              refine ⟨6449495534239304371095281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17198654757971478322920749 6449495534239304371095281)
              ·
                refine ⟨4837121650679478278321461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6449495534239304371095281 4837121650679478278321461)
                ·
                  refine ⟨453480154751201088592637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4837121650679478278321461 453480154751201088592637)
                  ·
                    rfl

theorem cell23_7948345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 3, 2, 5].length) (baseStart_7948345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7948345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7948345 prefixEnd_7948345 := by exact prefixLift 7948345
  have htrace : WordTrace (prefixWord ++ tailWord_7948345) baseStart_7948345 baseEnd_7948345 := by
    simpa [prefixWord, tailWord_7948345, baseEnd_7948345] using wordTrace_append hprefix tailTrace_7948345
  have hstable : (prefixWord ++ tailWord_7948345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7948345).length < 2 ^ (prefixWord ++ tailWord_7948345).sum := by decide
  have hdescent : baseEnd_7948345 < baseStart_7948345 := by decide
  rcases family_descends (prefixWord ++ tailWord_7948345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7948358 : List Nat := [6, 1, 1, 1, 1, 1, 1, 2, 4, 5]
def baseStart_7948358 : Nat := 118140960795 + 7948358 * 2 ^ 59
def prefixEnd_7948358 : Nat := 4983230072969 + 3 ^ 40 * 7948358 * 2
def baseEnd_7948358 : Nat := 1360442689336439415490391

theorem tailTrace_7948358 : CollatzResearch.WordTrace tailWord_7948358 prefixEnd_7948358 1360442689336439415490391 := by
  unfold tailWord_7948358
  simp only [CollatzResearch.WordTrace]
  refine ⟨9059388516826997259927679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 193266955025642608211790485 9059388516826997259927679)
  ·
    refine ⟨13589082775240495889891519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9059388516826997259927679 13589082775240495889891519)
    ·
      refine ⟨20383624162860743834837279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13589082775240495889891519 20383624162860743834837279)
      ·
        refine ⟨30575436244291115752255919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20383624162860743834837279 30575436244291115752255919)
        ·
          refine ⟨45863154366436673628383879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30575436244291115752255919 45863154366436673628383879)
          ·
            refine ⟨68794731549655010442575819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45863154366436673628383879 68794731549655010442575819)
            ·
              refine ⟨103192097324482515663863729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68794731549655010442575819 103192097324482515663863729)
              ·
                refine ⟨77394072993361886747897797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103192097324482515663863729 77394072993361886747897797)
                ·
                  refine ⟨14511388686255353765230837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77394072993361886747897797 14511388686255353765230837)
                  ·
                    refine ⟨1360442689336439415490391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14511388686255353765230837 1360442689336439415490391)
                    ·
                      rfl

theorem cell23_7948358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_7948358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7948358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7948358 prefixEnd_7948358 := by exact prefixLift 7948358
  have htrace : WordTrace (prefixWord ++ tailWord_7948358) baseStart_7948358 baseEnd_7948358 := by
    simpa [prefixWord, tailWord_7948358, baseEnd_7948358] using wordTrace_append hprefix tailTrace_7948358
  have hstable : (prefixWord ++ tailWord_7948358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7948358).length < 2 ^ (prefixWord ++ tailWord_7948358).sum := by decide
  have hdescent : baseEnd_7948358 < baseStart_7948358 := by decide
  rcases family_descends (prefixWord ++ tailWord_7948358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7948361 : List Nat := [1, 2, 1, 1, 2, 2, 4, 1, 1, 6, 2]
def baseStart_7948361 : Nat := 118140960795 + 7948361 * 2 ^ 59
def prefixEnd_7948361 : Nat := 4983230072969 + 3 ^ 40 * 7948361 * 2
def baseEnd_7948361 : Nat := 4081329608451281734733659

theorem tailTrace_7948361 : CollatzResearch.WordTrace tailWord_7948361 prefixEnd_7948361 4081329608451281734733659 := by
  unfold tailWord_7948361
  simp only [CollatzResearch.WordTrace]
  refine ⟨289900541957453043830044937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193267027971635362553363291 289900541957453043830044937)
  ·
    refine ⟨217425406468089782872533703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289900541957453043830044937 217425406468089782872533703)
    ·
      refine ⟨326138109702134674308800555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217425406468089782872533703 326138109702134674308800555)
      ·
        refine ⟨489207164553202011463200833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326138109702134674308800555 489207164553202011463200833)
        ·
          refine ⟨366905373414901508597400625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 489207164553202011463200833 366905373414901508597400625)
          ·
            refine ⟨275179030061176131448050469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 366905373414901508597400625 275179030061176131448050469)
            ·
              refine ⟨51596068136470524646509463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 275179030061176131448050469 51596068136470524646509463)
              ·
                refine ⟨77394102204705786969764195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51596068136470524646509463 77394102204705786969764195)
                ·
                  refine ⟨116091153307058680454646293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77394102204705786969764195 116091153307058680454646293)
                  ·
                    refine ⟨5441772811268375646311545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 116091153307058680454646293 5441772811268375646311545)
                    ·
                      refine ⟨4081329608451281734733659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5441772811268375646311545 4081329608451281734733659)
                      ·
                        rfl

theorem cell23_7948361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 6, 2].length) (baseStart_7948361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7948361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7948361 prefixEnd_7948361 := by exact prefixLift 7948361
  have htrace : WordTrace (prefixWord ++ tailWord_7948361) baseStart_7948361 baseEnd_7948361 := by
    simpa [prefixWord, tailWord_7948361, baseEnd_7948361] using wordTrace_append hprefix tailTrace_7948361
  have hstable : (prefixWord ++ tailWord_7948361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7948361).length < 2 ^ (prefixWord ++ tailWord_7948361).sum := by decide
  have hdescent : baseEnd_7948361 < baseStart_7948361 := by decide
  rcases family_descends (prefixWord ++ tailWord_7948361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7948398 : List Nat := [4, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3]
def baseStart_7948398 : Nat := 118140960795 + 7948398 * 2 ^ 59
def prefixEnd_7948398 : Nat := 4983230072969 + 3 ^ 40 * 7948398 * 2
def baseEnd_7948398 : Nat := 4081348607235498089970989

theorem tailTrace_7948398 : CollatzResearch.WordTrace tailWord_7948398 prefixEnd_7948398 4081348607235498089970989 := by
  unfold tailWord_7948398
  simp only [CollatzResearch.WordTrace]
  refine ⟨36237736432289874893642731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193267927638879332766094565 36237736432289874893642731)
  ·
    refine ⟨54356604648434812340464097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36237736432289874893642731 54356604648434812340464097)
    ·
      refine ⟨40767453486326109255348073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54356604648434812340464097 40767453486326109255348073)
      ·
        refine ⟨30575590114744581941511055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40767453486326109255348073 30575590114744581941511055)
        ·
          refine ⟨45863385172116872912266583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30575590114744581941511055 45863385172116872912266583)
          ·
            refine ⟨68795077758175309368399875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45863385172116872912266583 68795077758175309368399875)
            ·
              refine ⟨103192616637262964052599813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68795077758175309368399875 103192616637262964052599813)
              ·
                refine ⟨19348615619486805759862465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103192616637262964052599813 19348615619486805759862465)
                ·
                  refine ⟨14511461714615104319896849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19348615619486805759862465 14511461714615104319896849)
                  ·
                    refine ⟨10883596285961328239922637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14511461714615104319896849 10883596285961328239922637)
                    ·
                      refine ⟨4081348607235498089970989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10883596285961328239922637 4081348607235498089970989)
                      ·
                        rfl

theorem cell23_7948398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_7948398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7948398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7948398 prefixEnd_7948398 := by exact prefixLift 7948398
  have htrace : WordTrace (prefixWord ++ tailWord_7948398) baseStart_7948398 baseEnd_7948398 := by
    simpa [prefixWord, tailWord_7948398, baseEnd_7948398] using wordTrace_append hprefix tailTrace_7948398
  have hstable : (prefixWord ++ tailWord_7948398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7948398).length < 2 ^ (prefixWord ++ tailWord_7948398).sum := by decide
  have hdescent : baseEnd_7948398 < baseStart_7948398 := by decide
  rcases family_descends (prefixWord ++ tailWord_7948398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7948401 : List Nat := [1, 2, 2, 2, 1, 1, 6, 2, 6]
def baseStart_7948401 : Nat := 118140960795 + 7948401 * 2 ^ 59
def prefixEnd_7948401 : Nat := 4983230072969 + 3 ^ 40 * 7948401 * 2
def baseEnd_7948401 : Nat := 453483349741940175359275

theorem tailTrace_7948401 : CollatzResearch.WordTrace tailWord_7948401 prefixEnd_7948401 453483349741940175359275 := by
  unfold tailWord_7948401
  simp only [CollatzResearch.WordTrace]
  refine ⟨289902000877308130661501057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193268000584872087107667371 289902000877308130661501057)
  ·
    refine ⟨217426500657981097996125793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289902000877308130661501057 217426500657981097996125793)
    ·
      refine ⟨163069875493485823497094345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217426500657981097996125793 163069875493485823497094345)
      ·
        refine ⟨122302406620114367622820759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163069875493485823497094345 122302406620114367622820759)
        ·
          refine ⟨183453609930171551434231139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122302406620114367622820759 183453609930171551434231139)
          ·
            refine ⟨275180414895257327151346709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183453609930171551434231139 275180414895257327151346709)
            ·
              refine ⟨12899081948215187210219377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 275180414895257327151346709 12899081948215187210219377)
              ·
                refine ⟨9674311461161390407664533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12899081948215187210219377 9674311461161390407664533)
                ·
                  refine ⟨453483349741940175359275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9674311461161390407664533 453483349741940175359275)
                  ·
                    rfl

theorem cell23_7948401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 2, 6].length) (baseStart_7948401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7948401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7948401 prefixEnd_7948401 := by exact prefixLift 7948401
  have htrace : WordTrace (prefixWord ++ tailWord_7948401) baseStart_7948401 baseEnd_7948401 := by
    simpa [prefixWord, tailWord_7948401, baseEnd_7948401] using wordTrace_append hprefix tailTrace_7948401
  have hstable : (prefixWord ++ tailWord_7948401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7948401).length < 2 ^ (prefixWord ++ tailWord_7948401).sum := by decide
  have hdescent : baseEnd_7948401 < baseStart_7948401 := by decide
  rcases family_descends (prefixWord ++ tailWord_7948401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7948448 : List Nat := [2, 1, 1, 4, 2, 3, 1, 3, 1, 5]
def baseStart_7948448 : Nat := 118140960795 + 7948448 * 2 ^ 59
def prefixEnd_7948448 : Nat := 4983230072969 + 3 ^ 40 * 7948448 * 2
def baseEnd_7948448 : Nat := 1360458093756074298115253

theorem tailTrace_7948448 : CollatzResearch.WordTrace tailWord_7948448 prefixEnd_7948448 1360458093756074298115253 := by
  unfold tailWord_7948448
  simp only [CollatzResearch.WordTrace]
  refine ⟨144951857554068928844230999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193269143405425238458974665 144951857554068928844230999)
  ·
    refine ⟨217427786331103393266346499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144951857554068928844230999 217427786331103393266346499)
    ·
      refine ⟨326141679496655089899519749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217427786331103393266346499 326141679496655089899519749)
      ·
        refine ⟨61151564905622829356159953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 326141679496655089899519749 61151564905622829356159953)
        ·
          refine ⟨45863673679217122017119965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61151564905622829356159953 45863673679217122017119965)
          ·
            refine ⟨17198877629706420756419987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45863673679217122017119965 17198877629706420756419987)
            ·
              refine ⟨25798316444559631134629981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17198877629706420756419987 25798316444559631134629981)
              ·
                refine ⟨9674368666709861675486243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25798316444559631134629981 9674368666709861675486243)
                ·
                  refine ⟨14511553000064792513229365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9674368666709861675486243 14511553000064792513229365)
                  ·
                    refine ⟨1360458093756074298115253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14511553000064792513229365 1360458093756074298115253)
                    ·
                      rfl

theorem cell23_7948448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 3, 1, 5].length) (baseStart_7948448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7948448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7948448 prefixEnd_7948448 := by exact prefixLift 7948448
  have htrace : WordTrace (prefixWord ++ tailWord_7948448) baseStart_7948448 baseEnd_7948448 := by
    simpa [prefixWord, tailWord_7948448, baseEnd_7948448] using wordTrace_append hprefix tailTrace_7948448
  have hstable : (prefixWord ++ tailWord_7948448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7948448).length < 2 ^ (prefixWord ++ tailWord_7948448).sum := by decide
  have hdescent : baseEnd_7948448 < baseStart_7948448 := by decide
  rcases family_descends (prefixWord ++ tailWord_7948448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7948471 : List Nat := [1, 1, 3, 1, 4, 2, 1, 1, 3, 1, 5]
def baseStart_7948471 : Nat := 118140960795 + 7948471 * 2 ^ 59
def prefixEnd_7948471 : Nat := 4983230072969 + 3 ^ 40 * 7948471 * 2
def baseEnd_7948471 : Nat := 4081386091323276304358153

theorem tailTrace_7948471 : CollatzResearch.WordTrace tailWord_7948471 prefixEnd_7948471 4081386091323276304358153 := by
  unfold tailWord_7948471
  simp only [CollatzResearch.WordTrace]
  refine ⟨289904553987054532616549267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193269702658036355077699511 289904553987054532616549267)
  ·
    refine ⟨434856830980581798924823901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289904553987054532616549267 434856830980581798924823901)
    ·
      refine ⟨163071311617718174596808963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 434856830980581798924823901 163071311617718174596808963)
      ·
        refine ⟨244606967426577261895213445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163071311617718174596808963 244606967426577261895213445)
        ·
          refine ⟨45863806392483236605352521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 244606967426577261895213445 45863806392483236605352521)
          ·
            refine ⟨34397854794362427454014391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45863806392483236605352521 34397854794362427454014391)
            ·
              refine ⟨51596782191543641181021587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34397854794362427454014391 51596782191543641181021587)
              ·
                refine ⟨77395173287315461771532381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51596782191543641181021587 77395173287315461771532381)
                ·
                  refine ⟨29023189982743298164324643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77395173287315461771532381 29023189982743298164324643)
                  ·
                    refine ⟨43534784974114947246486965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29023189982743298164324643 43534784974114947246486965)
                    ·
                      refine ⟨4081386091323276304358153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43534784974114947246486965 4081386091323276304358153)
                      ·
                        rfl

theorem cell23_7948471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 3, 1, 5].length) (baseStart_7948471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7948471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7948471 prefixEnd_7948471 := by exact prefixLift 7948471
  have htrace : WordTrace (prefixWord ++ tailWord_7948471) baseStart_7948471 baseEnd_7948471 := by
    simpa [prefixWord, tailWord_7948471, baseEnd_7948471] using wordTrace_append hprefix tailTrace_7948471
  have hstable : (prefixWord ++ tailWord_7948471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7948471).length < 2 ^ (prefixWord ++ tailWord_7948471).sum := by decide
  have hdescent : baseEnd_7948471 < baseStart_7948471 := by decide
  rcases family_descends (prefixWord ++ tailWord_7948471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7948482 : List Nat := [3, 5, 1, 1, 1, 1, 1, 4, 1, 5]
def baseStart_7948482 : Nat := 118140960795 + 7948482 * 2 ^ 59
def prefixEnd_7948482 : Nat := 4983230072969 + 3 ^ 40 * 7948482 * 2
def baseEnd_7948482 : Nat := 1360463913203491920440201

theorem tailTrace_7948482 : CollatzResearch.WordTrace tailWord_7948482 prefixEnd_7948482 1360463913203491920440201 := by
  unfold tailWord_7948482
  simp only [CollatzResearch.WordTrace]
  refine ⟨72476238797503670373799925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193269970126676454330133133 72476238797503670373799925)
  ·
    refine ⟨6794647387265969097543743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72476238797503670373799925 6794647387265969097543743)
    ·
      refine ⟨10191971080898953646315615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6794647387265969097543743 10191971080898953646315615)
      ·
        refine ⟨15287956621348430469473423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10191971080898953646315615 15287956621348430469473423)
        ·
          refine ⟨22931934932022645704210135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15287956621348430469473423 22931934932022645704210135)
          ·
            refine ⟨34397902398033968556315203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22931934932022645704210135 34397902398033968556315203)
            ·
              refine ⟨51596853597050952834472805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34397902398033968556315203 51596853597050952834472805)
              ·
                refine ⟨9674410049447053656463651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51596853597050952834472805 9674410049447053656463651)
                ·
                  refine ⟨14511615074170580484695477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9674410049447053656463651 14511615074170580484695477)
                  ·
                    refine ⟨1360463913203491920440201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14511615074170580484695477 1360463913203491920440201)
                    ·
                      rfl

theorem cell23_7948482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_7948482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7948482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7948482 prefixEnd_7948482 := by exact prefixLift 7948482
  have htrace : WordTrace (prefixWord ++ tailWord_7948482) baseStart_7948482 baseEnd_7948482 := by
    simpa [prefixWord, tailWord_7948482, baseEnd_7948482] using wordTrace_append hprefix tailTrace_7948482
  have hstable : (prefixWord ++ tailWord_7948482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7948482).length < 2 ^ (prefixWord ++ tailWord_7948482).sum := by decide
  have hdescent : baseEnd_7948482 < baseStart_7948482 := by decide
  rcases family_descends (prefixWord ++ tailWord_7948482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7948485 : List Nat := [1, 3, 1, 1, 1, 1, 6, 2, 3, 2, 2]
def baseStart_7948485 : Nat := 118140960795 + 7948485 * 2 ^ 59
def prefixEnd_7948485 : Nat := 4983230072969 + 3 ^ 40 * 7948485 * 2
def baseEnd_7948485 : Nat := 4081393280052439249583089

theorem tailTrace_7948485 : CollatzResearch.WordTrace tailWord_7948485 prefixEnd_7948485 4081393280052439249583089 := by
  unfold tailWord_7948485
  simp only [CollatzResearch.WordTrace]
  refine ⟨289905064609003813007558909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193270043072669208671705939 289905064609003813007558909)
  ·
    refine ⟨108714399228376429877834591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289905064609003813007558909 108714399228376429877834591)
    ·
      refine ⟨163071598842564644816751887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108714399228376429877834591 163071598842564644816751887)
      ·
        refine ⟨244607398263846967225127831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163071598842564644816751887 244607398263846967225127831)
        ·
          refine ⟨366911097395770450837691747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244607398263846967225127831 366911097395770450837691747)
          ·
            refine ⟨550366646093655676256537621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366911097395770450837691747 550366646093655676256537621)
            ·
              refine ⟨25798436535640109824525201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 550366646093655676256537621 25798436535640109824525201)
              ·
                refine ⟨19348827401730082368393901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25798436535640109824525201 19348827401730082368393901)
                ·
                  refine ⟨7255810275648780888147713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19348827401730082368393901 7255810275648780888147713)
                  ·
                    refine ⟨5441857706736585666110785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7255810275648780888147713 5441857706736585666110785)
                    ·
                      refine ⟨4081393280052439249583089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5441857706736585666110785 4081393280052439249583089)
                      ·
                        rfl

theorem cell23_7948485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 2, 3, 2, 2].length) (baseStart_7948485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7948485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7948485 prefixEnd_7948485 := by exact prefixLift 7948485
  have htrace : WordTrace (prefixWord ++ tailWord_7948485) baseStart_7948485 baseEnd_7948485 := by
    simpa [prefixWord, tailWord_7948485, baseEnd_7948485] using wordTrace_append hprefix tailTrace_7948485
  have hstable : (prefixWord ++ tailWord_7948485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7948485).length < 2 ^ (prefixWord ++ tailWord_7948485).sum := by decide
  have hdescent : baseEnd_7948485 < baseStart_7948485 := by decide
  rcases family_descends (prefixWord ++ tailWord_7948485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7948502 : List Nat := [5, 2, 1, 2, 1, 1, 2, 3, 1, 1, 4]
def baseStart_7948502 : Nat := 118140960795 + 7948502 * 2 ^ 59
def prefixEnd_7948502 : Nat := 4983230072969 + 3 ^ 40 * 7948502 * 2
def baseEnd_7948502 : Nat := 4081402009223565683070511

theorem tailTrace_7948502 : CollatzResearch.WordTrace tailWord_7948502 prefixEnd_7948502 4081402009223565683070511 := by
  unfold tailWord_7948502
  simp only [CollatzResearch.WordTrace]
  refine ⟨18119105290621389056932985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 193270456433294816607285173 18119105290621389056932985)
  ·
    refine ⟨13589328967966041792699739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18119105290621389056932985 13589328967966041792699739)
    ·
      refine ⟨20383993451949062689049609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13589328967966041792699739 20383993451949062689049609)
      ·
        refine ⟨15287995088961797016787207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20383993451949062689049609 15287995088961797016787207)
        ·
          refine ⟨22931992633442695525180811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15287995088961797016787207 22931992633442695525180811)
          ·
            refine ⟨34397988950164043287771217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22931992633442695525180811 34397988950164043287771217)
            ·
              refine ⟨25798491712623032465828413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34397988950164043287771217 25798491712623032465828413)
              ·
                refine ⟨9674434392233637174685655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25798491712623032465828413 9674434392233637174685655)
                ·
                  refine ⟨14511651588350455762028483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9674434392233637174685655 14511651588350455762028483)
                  ·
                    refine ⟨21767477382525683643042725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14511651588350455762028483 21767477382525683643042725)
                    ·
                      refine ⟨4081402009223565683070511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21767477382525683643042725 4081402009223565683070511)
                      ·
                        rfl

theorem cell23_7948502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_7948502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7948502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7948502 prefixEnd_7948502 := by exact prefixLift 7948502
  have htrace : WordTrace (prefixWord ++ tailWord_7948502) baseStart_7948502 baseEnd_7948502 := by
    simpa [prefixWord, tailWord_7948502, baseEnd_7948502] using wordTrace_append hprefix tailTrace_7948502
  have hstable : (prefixWord ++ tailWord_7948502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7948502).length < 2 ^ (prefixWord ++ tailWord_7948502).sum := by decide
  have hdescent : baseEnd_7948502 < baseStart_7948502 := by decide
  rcases family_descends (prefixWord ++ tailWord_7948502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7948519 : List Nat := [1, 1, 5, 3, 1, 3, 1, 1, 3, 2, 2]
def baseStart_7948519 : Nat := 118140960795 + 7948519 * 2 ^ 59
def prefixEnd_7948519 : Nat := 4983230072969 + 3 ^ 40 * 7948519 * 2
def baseEnd_7948519 : Nat := 4081410738394692116557933

theorem tailTrace_7948519 : CollatzResearch.WordTrace tailWord_7948519 prefixEnd_7948519 4081410738394692116557933 := by
  unfold tailWord_7948519
  simp only [CollatzResearch.WordTrace]
  refine ⟨289906304690880636814296611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193270869793920424542864407 289906304690880636814296611)
  ·
    refine ⟨434859457036320955221444917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289906304690880636814296611 434859457036320955221444917)
    ·
      refine ⟨40768074097155089552010461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 434859457036320955221444917 40768074097155089552010461)
      ·
        refine ⟨15288027786433158582003923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40768074097155089552010461 15288027786433158582003923)
        ·
          refine ⟨22932041679649737873005885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15288027786433158582003923 22932041679649737873005885)
          ·
            refine ⟨8599515629868651702377207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22932041679649737873005885 8599515629868651702377207)
            ·
              refine ⟨12899273444802977553565811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8599515629868651702377207 12899273444802977553565811)
              ·
                refine ⟨19348910167204466330348717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12899273444802977553565811 19348910167204466330348717)
                ·
                  refine ⟨7255841312701674873880769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19348910167204466330348717 7255841312701674873880769)
                  ·
                    refine ⟨5441880984526256155410577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7255841312701674873880769 5441880984526256155410577)
                    ·
                      refine ⟨4081410738394692116557933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5441880984526256155410577 4081410738394692116557933)
                      ·
                        rfl

theorem cell23_7948519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_7948519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7948519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7948519 prefixEnd_7948519 := by exact prefixLift 7948519
  have htrace : WordTrace (prefixWord ++ tailWord_7948519) baseStart_7948519 baseEnd_7948519 := by
    simpa [prefixWord, tailWord_7948519, baseEnd_7948519] using wordTrace_append hprefix tailTrace_7948519
  have hstable : (prefixWord ++ tailWord_7948519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7948519).length < 2 ^ (prefixWord ++ tailWord_7948519).sum := by decide
  have hdescent : baseEnd_7948519 < baseStart_7948519 := by decide
  rcases family_descends (prefixWord ++ tailWord_7948519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7948545 : List Nat := [1, 2, 4, 1, 1, 2, 3, 1, 3, 3, 2]
def baseStart_7948545 : Nat := 118140960795 + 7948545 * 2 ^ 59
def prefixEnd_7948545 : Nat := 4983230072969 + 3 ^ 40 * 7948545 * 2
def baseEnd_7948545 : Nat := 4081424088891709014832813

theorem tailTrace_7948545 : CollatzResearch.WordTrace tailWord_7948545 prefixEnd_7948545 4081424088891709014832813 := by
  unfold tailWord_7948545
  simp only [CollatzResearch.WordTrace]
  refine ⟨289907252988786443254743089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193271501992524295503162059 289907252988786443254743089)
  ·
    refine ⟨217430439741589832441057317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289907252988786443254743089 217430439741589832441057317)
    ·
      refine ⟨40768207451548093582698247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 217430439741589832441057317 40768207451548093582698247)
      ·
        refine ⟨61152311177322140374047371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40768207451548093582698247 61152311177322140374047371)
        ·
          refine ⟨91728466765983210561071057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61152311177322140374047371 91728466765983210561071057)
          ·
            refine ⟨68796350074487407920803293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91728466765983210561071057 68796350074487407920803293)
            ·
              refine ⟨25798631277932777970301235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68796350074487407920803293 25798631277932777970301235)
              ·
                refine ⟨38697946916899166955451853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25798631277932777970301235 38697946916899166955451853)
                ·
                  refine ⟨14511730093837187608294445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38697946916899166955451853 14511730093837187608294445)
                  ·
                    refine ⟨5441898785188945353110417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14511730093837187608294445 5441898785188945353110417)
                    ·
                      refine ⟨4081424088891709014832813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5441898785188945353110417 4081424088891709014832813)
                      ·
                        rfl

theorem cell23_7948545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 1, 3, 3, 2].length) (baseStart_7948545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7948545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7948545 prefixEnd_7948545 := by exact prefixLift 7948545
  have htrace : WordTrace (prefixWord ++ tailWord_7948545) baseStart_7948545 baseEnd_7948545 := by
    simpa [prefixWord, tailWord_7948545, baseEnd_7948545] using wordTrace_append hprefix tailTrace_7948545
  have hstable : (prefixWord ++ tailWord_7948545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7948545).length < 2 ^ (prefixWord ++ tailWord_7948545).sum := by decide
  have hdescent : baseEnd_7948545 < baseStart_7948545 := by decide
  rcases family_descends (prefixWord ++ tailWord_7948545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7948615 : List Nat := [1, 1, 4, 1, 2, 2, 4, 3, 5]
def baseStart_7948615 : Nat := 118140960795 + 7948615 * 2 ^ 59
def prefixEnd_7948615 : Nat := 4983230072969 + 3 ^ 40 * 7948615 * 2
def baseEnd_7948615 : Nat := 453495559170835971217499

theorem tailTrace_7948615 : CollatzResearch.WordTrace tailWord_7948615 prefixEnd_7948615 453495559170835971217499 := by
  unfold tailWord_7948615
  simp only [CollatzResearch.WordTrace]
  refine ⟨289909806098532845209791299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193273204065688563473194199 289909806098532845209791299)
  ·
    refine ⟨434864709147799267814686949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289909806098532845209791299 434864709147799267814686949)
    ·
      refine ⟨81537132965212362715253803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 434864709147799267814686949 81537132965212362715253803)
      ·
        refine ⟨122305699447818544072880705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81537132965212362715253803 122305699447818544072880705)
        ·
          refine ⟨91729274585863908054660529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122305699447818544072880705 91729274585863908054660529)
          ·
            refine ⟨68796955939397931040995397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91729274585863908054660529 68796955939397931040995397)
            ·
              refine ⟨12899429238637112070186637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68796955939397931040995397 12899429238637112070186637)
              ·
                refine ⟨4837285964488917026319989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12899429238637112070186637 4837285964488917026319989)
                ·
                  refine ⟨453495559170835971217499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4837285964488917026319989 453495559170835971217499)
                  ·
                    rfl

theorem cell23_7948615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 3, 5].length) (baseStart_7948615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7948615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7948615 prefixEnd_7948615 := by exact prefixLift 7948615
  have htrace : WordTrace (prefixWord ++ tailWord_7948615) baseStart_7948615 baseEnd_7948615 := by
    simpa [prefixWord, tailWord_7948615, baseEnd_7948615] using wordTrace_append hprefix tailTrace_7948615
  have hstable : (prefixWord ++ tailWord_7948615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7948615).length < 2 ^ (prefixWord ++ tailWord_7948615).sum := by decide
  have hdescent : baseEnd_7948615 < baseStart_7948615 := by decide
  rcases family_descends (prefixWord ++ tailWord_7948615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7948694 : List Nat := [5, 3, 1, 2, 2, 1, 2, 1, 2, 2, 2]
def baseStart_7948694 : Nat := 118140960795 + 7948694 * 2 ^ 59
def prefixEnd_7948694 : Nat := 4983230072969 + 3 ^ 40 * 7948694 * 2
def baseEnd_7948694 : Nat := 4081500597509228931869629

theorem tailTrace_7948694 : CollatzResearch.WordTrace tailWord_7948694 prefixEnd_7948694 4081500597509228931869629 := by
  unfold tailWord_7948694
  simp only [CollatzResearch.WordTrace]
  refine ⟨18119542966577915106369821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 193275124976831094467944757 18119542966577915106369821)
  ·
    refine ⟨6794828612466718164888683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18119542966577915106369821 6794828612466718164888683)
    ·
      refine ⟨10192242918700077247333025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6794828612466718164888683 10192242918700077247333025)
      ·
        refine ⟨7644182189025057935499769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10192242918700077247333025 7644182189025057935499769)
        ·
          refine ⟨5733136641768793451624827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7644182189025057935499769 5733136641768793451624827)
          ·
            refine ⟨8599704962653190177437241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5733136641768793451624827 8599704962653190177437241)
            ·
              refine ⟨6449778721989892633077931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8599704962653190177437241 6449778721989892633077931)
              ·
                refine ⟨9674668082984838949616897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6449778721989892633077931 9674668082984838949616897)
                ·
                  refine ⟨7256001062238629212212673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9674668082984838949616897 7256001062238629212212673)
                  ·
                    refine ⟨5442000796678971909159505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7256001062238629212212673 5442000796678971909159505)
                    ·
                      refine ⟨4081500597509228931869629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5442000796678971909159505 4081500597509228931869629)
                      ·
                        rfl

theorem cell23_7948694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_7948694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7948694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7948694 prefixEnd_7948694 := by exact prefixLift 7948694
  have htrace : WordTrace (prefixWord ++ tailWord_7948694) baseStart_7948694 baseEnd_7948694 := by
    simpa [prefixWord, tailWord_7948694, baseEnd_7948694] using wordTrace_append hprefix tailTrace_7948694
  have hstable : (prefixWord ++ tailWord_7948694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7948694).length < 2 ^ (prefixWord ++ tailWord_7948694).sum := by decide
  have hdescent : baseEnd_7948694 < baseStart_7948694 := by decide
  rcases family_descends (prefixWord ++ tailWord_7948694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7948708 : List Nat := [2, 3, 1, 2, 1, 1, 2, 2, 1, 2, 6]
def baseStart_7948708 : Nat := 118140960795 + 7948708 * 2 ^ 59
def prefixEnd_7948708 : Nat := 4983230072969 + 3 ^ 40 * 7948708 * 2
def baseEnd_7948708 : Nat := 4081507786238391877094563

theorem tailTrace_7948708 : CollatzResearch.WordTrace tailWord_7948708 prefixEnd_7948708 4081507786238391877094563 := by
  unfold tailWord_7948708
  simp only [CollatzResearch.WordTrace]
  refine ⟨144956599043597961046463389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193275465391463948061951185 144956599043597961046463389)
  ·
    refine ⟨54358724641349235392423771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144956599043597961046463389 54358724641349235392423771)
    ·
      refine ⟨81538086962023853088635657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54358724641349235392423771 81538086962023853088635657)
      ·
        refine ⟨61153565221517889816476743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81538086962023853088635657 61153565221517889816476743)
        ·
          refine ⟨91730347832276834724715115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61153565221517889816476743 91730347832276834724715115)
          ·
            refine ⟨137595521748415252087072673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91730347832276834724715115 137595521748415252087072673)
            ·
              refine ⟨103196641311311439065304505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137595521748415252087072673 103196641311311439065304505)
              ·
                refine ⟨77397480983483579298978379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103196641311311439065304505 77397480983483579298978379)
                ·
                  refine ⟨116096221475225368948467569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77397480983483579298978379 116096221475225368948467569)
                  ·
                    refine ⟨87072166106419026711350677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 116096221475225368948467569 87072166106419026711350677)
                    ·
                      refine ⟨4081507786238391877094563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87072166106419026711350677 4081507786238391877094563)
                      ·
                        rfl

theorem cell23_7948708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_7948708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7948708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7948708 prefixEnd_7948708 := by exact prefixLift 7948708
  have htrace : WordTrace (prefixWord ++ tailWord_7948708) baseStart_7948708 baseEnd_7948708 := by
    simpa [prefixWord, tailWord_7948708, baseEnd_7948708] using wordTrace_append hprefix tailTrace_7948708
  have hstable : (prefixWord ++ tailWord_7948708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7948708).length < 2 ^ (prefixWord ++ tailWord_7948708).sum := by decide
  have hdescent : baseEnd_7948708 < baseStart_7948708 := by decide
  rcases family_descends (prefixWord ++ tailWord_7948708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7948785 : List Nat := [1, 2, 2, 2, 3, 1, 1, 4, 1, 2, 4]
def baseStart_7948785 : Nat := 118140960795 + 7948785 * 2 ^ 59
def prefixEnd_7948785 : Nat := 4983230072969 + 3 ^ 40 * 7948785 * 2
def baseEnd_7948785 : Nat := 4081547324248788075831709

theorem tailTrace_7948785 : CollatzResearch.WordTrace tailWord_7948785 prefixEnd_7948785 4081547324248788075831709 := by
  unfold tailWord_7948785
  simp only [CollatzResearch.WordTrace]
  refine ⟨289916006507916964243479809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193277337671944642828986539 289916006507916964243479809)
  ·
    refine ⟨217437004880937723182609857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289916006507916964243479809 217437004880937723182609857)
    ·
      refine ⟨163077753660703292386957393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217437004880937723182609857 163077753660703292386957393)
      ·
        refine ⟨122308315245527469290218045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163077753660703292386957393 122308315245527469290218045)
        ·
          refine ⟨45865618217072800983831767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122308315245527469290218045 45865618217072800983831767)
          ·
            refine ⟨68798427325609201475747651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45865618217072800983831767 68798427325609201475747651)
            ·
              refine ⟨103197640988413802213621477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68798427325609201475747651 103197640988413802213621477)
              ·
                refine ⟨19349557685327587915054027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103197640988413802213621477 19349557685327587915054027)
                ·
                  refine ⟨29024336527991381872581041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19349557685327587915054027 29024336527991381872581041)
                  ·
                    refine ⟨21768252395993536404435781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29024336527991381872581041 21768252395993536404435781)
                    ·
                      refine ⟨4081547324248788075831709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21768252395993536404435781 4081547324248788075831709)
                      ·
                        rfl

theorem cell23_7948785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 4, 1, 2, 4].length) (baseStart_7948785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7948785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7948785 prefixEnd_7948785 := by exact prefixLift 7948785
  have htrace : WordTrace (prefixWord ++ tailWord_7948785) baseStart_7948785 baseEnd_7948785 := by
    simpa [prefixWord, tailWord_7948785, baseEnd_7948785] using wordTrace_append hprefix tailTrace_7948785
  have hstable : (prefixWord ++ tailWord_7948785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7948785).length < 2 ^ (prefixWord ++ tailWord_7948785).sum := by decide
  have hdescent : baseEnd_7948785 < baseStart_7948785 := by decide
  rcases family_descends (prefixWord ++ tailWord_7948785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7948786 : List Nat := [3, 2, 1, 4, 2, 2, 2, 1, 1, 5]
def baseStart_7948786 : Nat := 118140960795 + 7948786 * 2 ^ 59
def prefixEnd_7948786 : Nat := 4983230072969 + 3 ^ 40 * 7948786 * 2
def baseEnd_7948786 : Nat := 1360515945909814190639735

theorem tailTrace_7948786 : CollatzResearch.WordTrace tailWord_7948786 prefixEnd_7948786 1360515945909814190639735 := by
  unfold tailWord_7948786
  simp only [CollatzResearch.WordTrace]
  refine ⟨72479010745228335353566553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193277361987275560942844141 72479010745228335353566553)
  ·
    refine ⟨54359258058921251515174915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72479010745228335353566553 54359258058921251515174915)
    ·
      refine ⟨81538887088381877272762373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54359258058921251515174915 81538887088381877272762373)
      ·
        refine ⟨15288541329071601988642945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81538887088381877272762373 15288541329071601988642945)
        ·
          refine ⟨11466405996803701491482209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15288541329071601988642945 11466405996803701491482209)
          ·
            refine ⟨8599804497602776118611657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11466405996803701491482209 8599804497602776118611657)
            ·
              refine ⟨6449853373202082088958743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8599804497602776118611657 6449853373202082088958743)
              ·
                refine ⟨9674780059803123133438115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6449853373202082088958743 9674780059803123133438115)
                ·
                  refine ⟨14512170089704684700157173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9674780059803123133438115 14512170089704684700157173)
                  ·
                    refine ⟨1360515945909814190639735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14512170089704684700157173 1360515945909814190639735)
                    ·
                      rfl

theorem cell23_7948786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 2, 1, 1, 5].length) (baseStart_7948786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7948786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7948786 prefixEnd_7948786 := by exact prefixLift 7948786
  have htrace : WordTrace (prefixWord ++ tailWord_7948786) baseStart_7948786 baseEnd_7948786 := by
    simpa [prefixWord, tailWord_7948786, baseEnd_7948786] using wordTrace_append hprefix tailTrace_7948786
  have hstable : (prefixWord ++ tailWord_7948786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7948786).length < 2 ^ (prefixWord ++ tailWord_7948786).sum := by decide
  have hdescent : baseEnd_7948786 < baseStart_7948786 := by decide
  rcases family_descends (prefixWord ++ tailWord_7948786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7948792 : List Nat := [2, 1, 2, 1, 1, 4, 3, 3, 1, 2, 3]
def baseStart_7948792 : Nat := 118140960795 + 7948792 * 2 ^ 59
def prefixEnd_7948792 : Nat := 4983230072969 + 3 ^ 40 * 7948792 * 2
def baseEnd_7948792 : Nat := 4081550918613369548444177

theorem tailTrace_7948792 : CollatzResearch.WordTrace tailWord_7948792 prefixEnd_7948792 4081550918613369548444177 := by
  unfold tailWord_7948792
  simp only [CollatzResearch.WordTrace]
  refine ⟨144958130909445802219492315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193277507879261069625989753 144958130909445802219492315)
  ·
    refine ⟨217437196364168703329238473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144958130909445802219492315 217437196364168703329238473)
    ·
      refine ⟨163077897273126527496928855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217437196364168703329238473 163077897273126527496928855)
      ·
        refine ⟨244616845909689791245393283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163077897273126527496928855 244616845909689791245393283)
        ·
          refine ⟨366925268864534686868089925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244616845909689791245393283 366925268864534686868089925)
          ·
            refine ⟨68798487912100253787766861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 366925268864534686868089925 68798487912100253787766861)
            ·
              refine ⟨25799432967037595170412573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68798487912100253787766861 25799432967037595170412573)
              ·
                refine ⟨9674787362639098188904715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25799432967037595170412573 9674787362639098188904715)
                ·
                  refine ⟨14512181043958647283357073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9674787362639098188904715 14512181043958647283357073)
                  ·
                    refine ⟨10884135782968985462517805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14512181043958647283357073 10884135782968985462517805)
                    ·
                      refine ⟨4081550918613369548444177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10884135782968985462517805 4081550918613369548444177)
                      ·
                        rfl

theorem cell23_7948792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 3, 1, 2, 3].length) (baseStart_7948792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7948792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7948792 prefixEnd_7948792 := by exact prefixLift 7948792
  have htrace : WordTrace (prefixWord ++ tailWord_7948792) baseStart_7948792 baseEnd_7948792 := by
    simpa [prefixWord, tailWord_7948792, baseEnd_7948792] using wordTrace_append hprefix tailTrace_7948792
  have hstable : (prefixWord ++ tailWord_7948792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7948792).length < 2 ^ (prefixWord ++ tailWord_7948792).sum := by decide
  have hdescent : baseEnd_7948792 < baseStart_7948792 := by decide
  rcases family_descends (prefixWord ++ tailWord_7948792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7948805 : List Nat := [1, 3, 1, 1, 2, 2, 2, 2, 3, 3, 3]
def baseStart_7948805 : Nat := 118140960795 + 7948805 * 2 ^ 59
def prefixEnd_7948805 : Nat := 4983230072969 + 3 ^ 40 * 7948805 * 2
def baseEnd_7948805 : Nat := 4081557593861877997581617

theorem tailTrace_7948805 : CollatzResearch.WordTrace tailWord_7948805 prefixEnd_7948805 4081557593861877997581617 := by
  unfold tailWord_7948805
  simp only [CollatzResearch.WordTrace]
  refine ⟨289916735967844507659207869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193277823978563005106138579 289916735967844507659207869)
  ·
    refine ⟨108718775987941690372202951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289916735967844507659207869 108718775987941690372202951)
    ·
      refine ⟨163078163981912535558304427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108718775987941690372202951 163078163981912535558304427)
      ·
        refine ⟨244617245972868803337456641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163078163981912535558304427 244617245972868803337456641)
        ·
          refine ⟨183462934479651602503092481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244617245972868803337456641 183462934479651602503092481)
          ·
            refine ⟨137597200859738701877319361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183462934479651602503092481 137597200859738701877319361)
            ·
              refine ⟨103197900644804026407989521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137597200859738701877319361 103197900644804026407989521)
              ·
                refine ⟨77398425483603019805992141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103197900644804026407989521 77398425483603019805992141)
                ·
                  refine ⟨29024409556351132427247053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77398425483603019805992141 29024409556351132427247053)
                  ·
                    refine ⟨10884153583631674660217645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29024409556351132427247053 10884153583631674660217645)
                    ·
                      refine ⟨4081557593861877997581617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10884153583631674660217645 4081557593861877997581617)
                      ·
                        rfl

theorem cell23_7948805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 3, 3, 3].length) (baseStart_7948805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7948805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7948805 prefixEnd_7948805 := by exact prefixLift 7948805
  have htrace : WordTrace (prefixWord ++ tailWord_7948805) baseStart_7948805 baseEnd_7948805 := by
    simpa [prefixWord, tailWord_7948805, baseEnd_7948805] using wordTrace_append hprefix tailTrace_7948805
  have hstable : (prefixWord ++ tailWord_7948805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7948805).length < 2 ^ (prefixWord ++ tailWord_7948805).sum := by decide
  have hdescent : baseEnd_7948805 < baseStart_7948805 := by decide
  rcases family_descends (prefixWord ++ tailWord_7948805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7948835 : List Nat := [1, 1, 1, 4, 4, 1, 1, 1, 2, 2, 5]
def baseStart_7948835 : Nat := 118140960795 + 7948835 * 2 ^ 59
def prefixEnd_7948835 : Nat := 4983230072969 + 3 ^ 40 * 7948835 * 2
def baseEnd_7948835 : Nat := 4081572998281512880206479

theorem tailTrace_7948835 : CollatzResearch.WordTrace tailWord_7948835 prefixEnd_7948835 4081572998281512880206479 := by
  unfold tailWord_7948835
  simp only [CollatzResearch.WordTrace]
  refine ⟨289917830157735822782799959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193278553438490548521866639 289917830157735822782799959)
  ·
    refine ⟨434876745236603734174199939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289917830157735822782799959 434876745236603734174199939)
    ·
      refine ⟨652315117854905601261299909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434876745236603734174199939 652315117854905601261299909)
      ·
        refine ⟨122309084597794800236493733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 652315117854905601261299909 122309084597794800236493733)
        ·
          refine ⟨22932953362086525044342575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122309084597794800236493733 22932953362086525044342575)
          ·
            refine ⟨34399430043129787566513863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22932953362086525044342575 34399430043129787566513863)
            ·
              refine ⟨51599145064694681349770795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34399430043129787566513863 51599145064694681349770795)
              ·
                refine ⟨77398717597042022024656193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51599145064694681349770795 77398717597042022024656193)
                ·
                  refine ⟨58049038197781516518492145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77398717597042022024656193 58049038197781516518492145)
                  ·
                    refine ⟨43536778648336137388869109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58049038197781516518492145 43536778648336137388869109)
                    ·
                      refine ⟨4081572998281512880206479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43536778648336137388869109 4081572998281512880206479)
                      ·
                        rfl

theorem cell23_7948835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 2, 2, 5].length) (baseStart_7948835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7948835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7948835 prefixEnd_7948835 := by exact prefixLift 7948835
  have htrace : WordTrace (prefixWord ++ tailWord_7948835) baseStart_7948835 baseEnd_7948835 := by
    simpa [prefixWord, tailWord_7948835, baseEnd_7948835] using wordTrace_append hprefix tailTrace_7948835
  have hstable : (prefixWord ++ tailWord_7948835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7948835).length < 2 ^ (prefixWord ++ tailWord_7948835).sum := by decide
  have hdescent : baseEnd_7948835 < baseStart_7948835 := by decide
  rcases family_descends (prefixWord ++ tailWord_7948835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7948840 : List Nat := [2, 1, 5, 2, 1, 3, 1, 3, 1, 2, 2]
def baseStart_7948840 : Nat := 118140960795 + 7948840 * 2 ^ 59
def prefixEnd_7948840 : Nat := 4983230072969 + 3 ^ 40 * 7948840 * 2
def baseEnd_7948840 : Nat := 4081575565684785360643957

theorem tailTrace_7948840 : CollatzResearch.WordTrace tailWord_7948840 prefixEnd_7948840 4081575565684785360643957 := by
  unfold tailWord_7948840
  simp only [CollatzResearch.WordTrace]
  refine ⟨144959006261358854318365987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193278675015145139091154649 144959006261358854318365987)
  ·
    refine ⟨217438509392038281477548981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144959006261358854318365987 217438509392038281477548981)
    ·
      refine ⟨20384860255503588888520217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 217438509392038281477548981 20384860255503588888520217)
      ·
        refine ⟨15288645191627691666390163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20384860255503588888520217 15288645191627691666390163)
        ·
          refine ⟨22932967787441537499585245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15288645191627691666390163 22932967787441537499585245)
          ·
            refine ⟨8599862920290576562344467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22932967787441537499585245 8599862920290576562344467)
            ·
              refine ⟨12899794380435864843516701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8599862920290576562344467 12899794380435864843516701)
              ·
                refine ⟨4837422892663449316318763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12899794380435864843516701 4837422892663449316318763)
                ·
                  refine ⟨7256134338995173974478145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4837422892663449316318763 7256134338995173974478145)
                  ·
                    refine ⟨5442100754246380480858609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7256134338995173974478145 5442100754246380480858609)
                    ·
                      refine ⟨4081575565684785360643957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5442100754246380480858609 4081575565684785360643957)
                      ·
                        rfl

theorem cell23_7948840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_7948840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7948840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7948840 prefixEnd_7948840 := by exact prefixLift 7948840
  have htrace : WordTrace (prefixWord ++ tailWord_7948840) baseStart_7948840 baseEnd_7948840 := by
    simpa [prefixWord, tailWord_7948840, baseEnd_7948840] using wordTrace_append hprefix tailTrace_7948840
  have hstable : (prefixWord ++ tailWord_7948840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7948840).length < 2 ^ (prefixWord ++ tailWord_7948840).sum := by decide
  have hdescent : baseEnd_7948840 < baseStart_7948840 := by decide
  rcases family_descends (prefixWord ++ tailWord_7948840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7948849 : List Nat := [1, 2, 2, 3, 1, 1, 4, 3, 1, 3, 2]
def baseStart_7948849 : Nat := 118140960795 + 7948849 * 2 ^ 59
def prefixEnd_7948849 : Nat := 4983230072969 + 3 ^ 40 * 7948849 * 2
def baseEnd_7948849 : Nat := 4081580187010675825431415

theorem tailTrace_7948849 : CollatzResearch.WordTrace tailWord_7948849 prefixEnd_7948849 4081580187010675825431415 := by
  unfold tailWord_7948849
  simp only [CollatzResearch.WordTrace]
  refine ⟨289918340779685103173809601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193278893853123402115873067 289918340779685103173809601)
  ·
    refine ⟨217438755584763827380357201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289918340779685103173809601 217438755584763827380357201)
    ·
      refine ⟨163079066688572870535267901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217438755584763827380357201 163079066688572870535267901)
      ·
        refine ⟨61154650008214826450725463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163079066688572870535267901 61154650008214826450725463)
        ·
          refine ⟨91731975012322239676088195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61154650008214826450725463 91731975012322239676088195)
          ·
            refine ⟨137597962518483359514132293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91731975012322239676088195 137597962518483359514132293)
            ·
              refine ⟨25799617972215629908899805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137597962518483359514132293 25799617972215629908899805)
              ·
                refine ⟨9674856739580861215837427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25799617972215629908899805 9674856739580861215837427)
                ·
                  refine ⟨14512285109371291823756141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9674856739580861215837427 14512285109371291823756141)
                  ·
                    refine ⟨5442106916014234433908553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14512285109371291823756141 5442106916014234433908553)
                    ·
                      refine ⟨4081580187010675825431415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5442106916014234433908553 4081580187010675825431415)
                      ·
                        rfl

theorem cell23_7948849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 3, 1, 3, 2].length) (baseStart_7948849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7948849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7948849 prefixEnd_7948849 := by exact prefixLift 7948849
  have htrace : WordTrace (prefixWord ++ tailWord_7948849) baseStart_7948849 baseEnd_7948849 := by
    simpa [prefixWord, tailWord_7948849, baseEnd_7948849] using wordTrace_append hprefix tailTrace_7948849
  have hstable : (prefixWord ++ tailWord_7948849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7948849).length < 2 ^ (prefixWord ++ tailWord_7948849).sum := by decide
  have hdescent : baseEnd_7948849 < baseStart_7948849 := by decide
  rcases family_descends (prefixWord ++ tailWord_7948849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7948875 : List Nat := [1, 1, 1, 1, 3, 1, 4, 3, 2, 2, 4]
def baseStart_7948875 : Nat := 118140960795 + 7948875 * 2 ^ 59
def prefixEnd_7948875 : Nat := 4983230072969 + 3 ^ 40 * 7948875 * 2
def baseEnd_7948875 : Nat := 4081593537507692723706295

theorem tailTrace_7948875 : CollatzResearch.WordTrace tailWord_7948875 prefixEnd_7948875 4081593537507692723706295 := by
  unfold tailWord_7948875
  simp only [CollatzResearch.WordTrace]
  refine ⟨289919289077590909614256079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193279526051727273076170719 289919289077590909614256079)
  ·
    refine ⟨434878933616386364421384119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289919289077590909614256079 434878933616386364421384119)
    ·
      refine ⟨652318400424579546632076179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434878933616386364421384119 652318400424579546632076179)
      ·
        refine ⟨978477600636869319948114269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 652318400424579546632076179 978477600636869319948114269)
        ·
          refine ⟨366929100238825994980542851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 978477600636869319948114269 366929100238825994980542851)
          ·
            refine ⟨550393650358238992470814277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366929100238825994980542851 550393650358238992470814277)
            ·
              refine ⟨103198809442169811088277677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 550393650358238992470814277 103198809442169811088277677)
              ·
                refine ⟨38699553540813679158104129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103198809442169811088277677 38699553540813679158104129)
                ·
                  refine ⟨29024665155610259368578097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38699553540813679158104129 29024665155610259368578097)
                  ·
                    refine ⟨21768498866707694526433573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29024665155610259368578097 21768498866707694526433573)
                    ·
                      refine ⟨4081593537507692723706295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21768498866707694526433573 4081593537507692723706295)
                      ·
                        rfl

theorem cell23_7948875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 2, 2, 4].length) (baseStart_7948875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7948875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7948875 prefixEnd_7948875 := by exact prefixLift 7948875
  have htrace : WordTrace (prefixWord ++ tailWord_7948875) baseStart_7948875 baseEnd_7948875 := by
    simpa [prefixWord, tailWord_7948875, baseEnd_7948875] using wordTrace_append hprefix tailTrace_7948875
  have hstable : (prefixWord ++ tailWord_7948875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7948875).length < 2 ^ (prefixWord ++ tailWord_7948875).sum := by decide
  have hdescent : baseEnd_7948875 < baseStart_7948875 := by decide
  rcases family_descends (prefixWord ++ tailWord_7948875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7948885 : List Nat := [1, 3, 2, 2, 1, 1, 2, 4, 7]
def baseStart_7948885 : Nat := 118140960795 + 7948885 * 2 ^ 59
def prefixEnd_7948885 : Nat := 4983230072969 + 3 ^ 40 * 7948885 * 2
def baseEnd_7948885 : Nat := 453510963590470853842361

theorem tailTrace_7948885 : CollatzResearch.WordTrace tailWord_7948885 prefixEnd_7948885 453510963590470853842361 := by
  unfold tailWord_7948885
  simp only [CollatzResearch.WordTrace]
  refine ⟨289919653807554681322120109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193279769205036454214746739 289919653807554681322120109)
  ·
    refine ⟨108719870177833005495795041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289919653807554681322120109 108719870177833005495795041)
    ·
      refine ⟨81539902633374754121846281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108719870177833005495795041 81539902633374754121846281)
      ·
        refine ⟨61154926975031065591384711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81539902633374754121846281 61154926975031065591384711)
        ·
          refine ⟨91732390462546598387077067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61154926975031065591384711 91732390462546598387077067)
          ·
            refine ⟨137598585693819897580615601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91732390462546598387077067 137598585693819897580615601)
            ·
              refine ⟨103198939270364923185461701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137598585693819897580615601 103198939270364923185461701)
              ·
                refine ⟨19349801113193423097274069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103198939270364923185461701 19349801113193423097274069)
                ·
                  refine ⟨453510963590470853842361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19349801113193423097274069 453510963590470853842361)
                  ·
                    rfl

theorem cell23_7948885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 4, 7].length) (baseStart_7948885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7948885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7948885 prefixEnd_7948885 := by exact prefixLift 7948885
  have htrace : WordTrace (prefixWord ++ tailWord_7948885) baseStart_7948885 baseEnd_7948885 := by
    simpa [prefixWord, tailWord_7948885, baseEnd_7948885] using wordTrace_append hprefix tailTrace_7948885
  have hstable : (prefixWord ++ tailWord_7948885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7948885).length < 2 ^ (prefixWord ++ tailWord_7948885).sum := by decide
  have hdescent : baseEnd_7948885 < baseStart_7948885 := by decide
  rcases family_descends (prefixWord ++ tailWord_7948885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7948915 : List Nat := [1, 1, 1, 2, 2, 1, 1, 5, 4, 5]
def baseStart_7948915 : Nat := 118140960795 + 7948915 * 2 ^ 59
def prefixEnd_7948915 : Nat := 4983230072969 + 3 ^ 40 * 7948915 * 2
def baseEnd_7948915 : Nat := 1360538025577957522402037

theorem tailTrace_7948915 : CollatzResearch.WordTrace tailWord_7948915 prefixEnd_7948915 1360538025577957522402037 := by
  unfold tailWord_7948915
  simp only [CollatzResearch.WordTrace]
  refine ⟨289920747997445996445712199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193280498664963997630474799 289920747997445996445712199)
  ·
    refine ⟨434881121996168994668568299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289920747997445996445712199 434881121996168994668568299)
    ·
      refine ⟨652321682994253492002852449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434881121996168994668568299 652321682994253492002852449)
      ·
        refine ⟨489241262245690119002139337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 652321682994253492002852449 489241262245690119002139337)
        ·
          refine ⟨366930946684267589251604503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 489241262245690119002139337 366930946684267589251604503)
          ·
            refine ⟨550396420026401383877406755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366930946684267589251604503 550396420026401383877406755)
            ·
              refine ⟨825594630039602075816110133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 550396420026401383877406755 825594630039602075816110133)
              ·
                refine ⟨77399496566212694607760325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 825594630039602075816110133 77399496566212694607760325)
                ·
                  refine ⟨14512405606164880238955061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77399496566212694607760325 14512405606164880238955061)
                  ·
                    refine ⟨1360538025577957522402037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14512405606164880238955061 1360538025577957522402037)
                    ·
                      rfl

theorem cell23_7948915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 4, 5].length) (baseStart_7948915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7948915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7948915 prefixEnd_7948915 := by exact prefixLift 7948915
  have htrace : WordTrace (prefixWord ++ tailWord_7948915) baseStart_7948915 baseEnd_7948915 := by
    simpa [prefixWord, tailWord_7948915, baseEnd_7948915] using wordTrace_append hprefix tailTrace_7948915
  have hstable : (prefixWord ++ tailWord_7948915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7948915).length < 2 ^ (prefixWord ++ tailWord_7948915).sum := by decide
  have hdescent : baseEnd_7948915 < baseStart_7948915 := by decide
  rcases family_descends (prefixWord ++ tailWord_7948915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7948919 : List Nat := [1, 1, 3, 1, 1, 3, 6, 2, 5]
def baseStart_7948919 : Nat := 118140960795 + 7948919 * 2 ^ 59
def prefixEnd_7948919 : Nat := 4983230072969 + 3 ^ 40 * 7948919 * 2
def baseEnd_7948919 : Nat := 453512903406276727950677

theorem tailTrace_7948919 : CollatzResearch.WordTrace tailWord_7948919 prefixEnd_7948919 453512903406276727950677 := by
  unfold tailWord_7948919
  simp only [CollatzResearch.WordTrace]
  refine ⟨289920893889431505128857811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193280595926287670085905207 289920893889431505128857811)
  ·
    refine ⟨434881340834147257693286717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289920893889431505128857811 434881340834147257693286717)
    ·
      refine ⟨163080502812805221634982519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 434881340834147257693286717 163080502812805221634982519)
      ·
        refine ⟨244620754219207832452473779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163080502812805221634982519 244620754219207832452473779)
        ·
          refine ⟨366931131328811748678710669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244620754219207832452473779 366931131328811748678710669)
          ·
            refine ⟨137599174248304405754516501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 366931131328811748678710669 137599174248304405754516501)
            ·
              refine ⟨6449961292889269019742961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 137599174248304405754516501 6449961292889269019742961)
              ·
                refine ⟨4837470969666951764807221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6449961292889269019742961 4837470969666951764807221)
                ·
                  refine ⟨453512903406276727950677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4837470969666951764807221 453512903406276727950677)
                  ·
                    rfl

theorem cell23_7948919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 6, 2, 5].length) (baseStart_7948919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7948919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7948919 prefixEnd_7948919 := by exact prefixLift 7948919
  have htrace : WordTrace (prefixWord ++ tailWord_7948919) baseStart_7948919 baseEnd_7948919 := by
    simpa [prefixWord, tailWord_7948919, baseEnd_7948919] using wordTrace_append hprefix tailTrace_7948919
  have hstable : (prefixWord ++ tailWord_7948919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7948919).length < 2 ^ (prefixWord ++ tailWord_7948919).sum := by decide
  have hdescent : baseEnd_7948919 < baseStart_7948919 := by decide
  rcases family_descends (prefixWord ++ tailWord_7948919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7948952 : List Nat := [2, 1, 2, 4, 1, 1, 3, 1, 1, 3, 4]
def baseStart_7948952 : Nat := 118140960795 + 7948952 * 2 ^ 59
def prefixEnd_7948952 : Nat := 4983230072969 + 3 ^ 40 * 7948952 * 2
def baseEnd_7948952 : Nat := 4081633075518088922443441

theorem tailTrace_7948952 : CollatzResearch.WordTrace tailWord_7948952 prefixEnd_7948952 4081633075518088922443441 := by
  unfold tailWord_7948952
  simp only [CollatzResearch.WordTrace]
  refine ⟨144961048749155975882404555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193281398332207967843206073 144961048749155975882404555)
  ·
    refine ⟨217441573123733963823606833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144961048749155975882404555 217441573123733963823606833)
    ·
      refine ⟨163081179842800472867705125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217441573123733963823606833 163081179842800472867705125)
      ·
        refine ⟨30577721220525088662694711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163081179842800472867705125 30577721220525088662694711)
        ·
          refine ⟨45866581830787632994042067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30577721220525088662694711 45866581830787632994042067)
          ·
            refine ⟨68799872746181449491063101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45866581830787632994042067 68799872746181449491063101)
            ·
              refine ⟨25799952279818043559148663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68799872746181449491063101 25799952279818043559148663)
              ·
                refine ⟨38699928419727065338722995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25799952279818043559148663 38699928419727065338722995)
                ·
                  refine ⟨58049892629590598008084493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38699928419727065338722995 58049892629590598008084493)
                  ·
                    refine ⟨21768709736096474253031685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58049892629590598008084493 21768709736096474253031685)
                    ·
                      refine ⟨4081633075518088922443441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21768709736096474253031685 4081633075518088922443441)
                      ·
                        rfl

theorem cell23_7948952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_7948952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7948952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7948952 prefixEnd_7948952 := by exact prefixLift 7948952
  have htrace : WordTrace (prefixWord ++ tailWord_7948952) baseStart_7948952 baseEnd_7948952 := by
    simpa [prefixWord, tailWord_7948952, baseEnd_7948952] using wordTrace_append hprefix tailTrace_7948952
  have hstable : (prefixWord ++ tailWord_7948952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7948952).length < 2 ^ (prefixWord ++ tailWord_7948952).sum := by decide
  have hdescent : baseEnd_7948952 < baseStart_7948952 := by decide
  rcases family_descends (prefixWord ++ tailWord_7948952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7948979 : List Nat := [1, 1, 1, 2, 3, 5, 2, 1, 3, 4]
def baseStart_7948979 : Nat := 118140960795 + 7948979 * 2 ^ 59
def prefixEnd_7948979 : Nat := 4983230072969 + 3 ^ 40 * 7948979 * 2
def baseEnd_7948979 : Nat := 1360548979831920105601939

theorem tailTrace_7948979 : CollatzResearch.WordTrace tailWord_7948979 prefixEnd_7948979 1360548979831920105601939 := by
  unfold tailWord_7948979
  simp only [CollatzResearch.WordTrace]
  refine ⟨289923082269214135376041991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193282054846142756917361327 289923082269214135376041991)
  ·
    refine ⟨434884623403821203064062987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289923082269214135376041991 434884623403821203064062987)
    ·
      refine ⟨652326935105731804596094481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434884623403821203064062987 652326935105731804596094481)
      ·
        refine ⟨489245201329298853447070861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 652326935105731804596094481 489245201329298853447070861)
        ·
          refine ⟨183466950498487070042651573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 489245201329298853447070861 183466950498487070042651573)
          ·
            refine ⟨17200026609233162816498585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 183466950498487070042651573 17200026609233162816498585)
            ·
              refine ⟨12900019956924872112373939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17200026609233162816498585 12900019956924872112373939)
              ·
                refine ⟨19350029935387308168560909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12900019956924872112373939 19350029935387308168560909)
                ·
                  refine ⟨7256261225770240563210341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19350029935387308168560909 7256261225770240563210341)
                  ·
                    refine ⟨1360548979831920105601939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7256261225770240563210341 1360548979831920105601939)
                    ·
                      rfl

theorem cell23_7948979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 1, 3, 4].length) (baseStart_7948979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7948979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7948979 prefixEnd_7948979 := by exact prefixLift 7948979
  have htrace : WordTrace (prefixWord ++ tailWord_7948979) baseStart_7948979 baseEnd_7948979 := by
    simpa [prefixWord, tailWord_7948979, baseEnd_7948979] using wordTrace_append hprefix tailTrace_7948979
  have hstable : (prefixWord ++ tailWord_7948979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7948979).length < 2 ^ (prefixWord ++ tailWord_7948979).sum := by decide
  have hdescent : baseEnd_7948979 < baseStart_7948979 := by decide
  rcases family_descends (prefixWord ++ tailWord_7948979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7949046 : List Nat := [5, 1, 1, 1, 1, 2, 1, 2, 4, 3, 2]
def baseStart_7949046 : Nat := 118140960795 + 7949046 * 2 ^ 59
def prefixEnd_7949046 : Nat := 4983230072969 + 3 ^ 40 * 7949046 * 2
def baseEnd_7949046 : Nat := 4081681342699611554668009

theorem tailTrace_7949046 : CollatzResearch.WordTrace tailWord_7949046 prefixEnd_7949046 4081681342699611554668009 := by
  unfold tailWord_7949046
  simp only [CollatzResearch.WordTrace]
  refine ⟨18120345372498212863670687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 193283683973314270545820661 18120345372498212863670687)
  ·
    refine ⟨27180518058747319295506031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18120345372498212863670687 27180518058747319295506031)
    ·
      refine ⟨40770777088120978943259047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27180518058747319295506031 40770777088120978943259047)
      ·
        refine ⟨61156165632181468414888571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40770777088120978943259047 61156165632181468414888571)
        ·
          refine ⟨91734248448272202622332857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61156165632181468414888571 91734248448272202622332857)
          ·
            refine ⟨68800686336204151966749643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91734248448272202622332857 68800686336204151966749643)
            ·
              refine ⟨103201029504306227950124465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68800686336204151966749643 103201029504306227950124465)
              ·
                refine ⟨77400772128229670962593349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103201029504306227950124465 77400772128229670962593349)
                ·
                  refine ⟨14512644774043063305486253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77400772128229670962593349 14512644774043063305486253)
                  ·
                    refine ⟨5442241790266148739557345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14512644774043063305486253 5442241790266148739557345)
                    ·
                      refine ⟨4081681342699611554668009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5442241790266148739557345 4081681342699611554668009)
                      ·
                        rfl

theorem cell23_7949046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 4, 3, 2].length) (baseStart_7949046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7949046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7949046 prefixEnd_7949046 := by exact prefixLift 7949046
  have htrace : WordTrace (prefixWord ++ tailWord_7949046) baseStart_7949046 baseEnd_7949046 := by
    simpa [prefixWord, tailWord_7949046, baseEnd_7949046] using wordTrace_append hprefix tailTrace_7949046
  have hstable : (prefixWord ++ tailWord_7949046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7949046).length < 2 ^ (prefixWord ++ tailWord_7949046).sum := by decide
  have hdescent : baseEnd_7949046 < baseStart_7949046 := by decide
  rcases family_descends (prefixWord ++ tailWord_7949046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7949063 : List Nat := [1, 1, 4, 4, 1, 2, 2, 1, 2, 3, 2]
def baseStart_7949063 : Nat := 118140960795 + 7949063 * 2 ^ 59
def prefixEnd_7949063 : Nat := 4983230072969 + 3 ^ 40 * 7949063 * 2
def baseEnd_7949063 : Nat := 4081690071870737988155431

theorem tailTrace_7949063 : CollatzResearch.WordTrace tailWord_7949063 prefixEnd_7949063 4081690071870737988155431 := by
  unfold tailWord_7949063
  simp only [CollatzResearch.WordTrace]
  refine ⟨289926146000909817722099843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193284097333939878481399895 289926146000909817722099843)
  ·
    refine ⟨434889219001364726583149765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289926146000909817722099843 434889219001364726583149765)
    ·
      refine ⟨81541728562755886234340581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 434889219001364726583149765 81541728562755886234340581)
      ·
        refine ⟨15289074105516728668938859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81541728562755886234340581 15289074105516728668938859)
        ·
          refine ⟨22933611158275093003408289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15289074105516728668938859 22933611158275093003408289)
          ·
            refine ⟨17200208368706319752556217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22933611158275093003408289 17200208368706319752556217)
            ·
              refine ⟨12900156276529739814417163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17200208368706319752556217 12900156276529739814417163)
              ·
                refine ⟨19350234414794609721625745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12900156276529739814417163 19350234414794609721625745)
                ·
                  refine ⟨14512675811095957291219309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19350234414794609721625745 14512675811095957291219309)
                  ·
                    refine ⟨5442253429160983984207241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14512675811095957291219309 5442253429160983984207241)
                    ·
                      refine ⟨4081690071870737988155431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5442253429160983984207241 4081690071870737988155431)
                      ·
                        rfl

theorem cell23_7949063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_7949063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7949063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7949063 prefixEnd_7949063 := by exact prefixLift 7949063
  have htrace : WordTrace (prefixWord ++ tailWord_7949063) baseStart_7949063 baseEnd_7949063 := by
    simpa [prefixWord, tailWord_7949063, baseEnd_7949063] using wordTrace_append hprefix tailTrace_7949063
  have hstable : (prefixWord ++ tailWord_7949063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7949063).length < 2 ^ (prefixWord ++ tailWord_7949063).sum := by decide
  have hdescent : baseEnd_7949063 < baseStart_7949063 := by decide
  rcases family_descends (prefixWord ++ tailWord_7949063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7949112 : List Nat := [2, 1, 2, 1, 3, 2, 1, 2, 2, 7]
def baseStart_7949112 : Nat := 118140960795 + 7949112 * 2 ^ 59
def prefixEnd_7949112 : Nat := 4983230072969 + 3 ^ 40 * 7949112 * 2
def baseEnd_7949112 : Nat := 1360571744140936098814235

theorem tailTrace_7949112 : CollatzResearch.WordTrace tailWord_7949112 prefixEnd_7949112 1360571744140936098814235 := by
  unfold tailWord_7949112
  simp only [CollatzResearch.WordTrace]
  refine ⟨144963966588866149545316795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193285288785154866060422393 144963966588866149545316795)
  ·
    refine ⟨217445949883299224317975193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144963966588866149545316795 217445949883299224317975193)
    ·
      refine ⟨163084462412474418238481395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217445949883299224317975193 163084462412474418238481395)
      ·
        refine ⟨244626693618711627357722093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163084462412474418238481395 244626693618711627357722093)
        ·
          refine ⟨91735010107016860259145785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 244626693618711627357722093 91735010107016860259145785)
          ·
            refine ⟨68801257580262645194359339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91735010107016860259145785 68801257580262645194359339)
            ·
              refine ⟨103201886370393967791539009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68801257580262645194359339 103201886370393967791539009)
              ·
                refine ⟨77401414777795475843654257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103201886370393967791539009 77401414777795475843654257)
                ·
                  refine ⟨58051061083346606882740693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77401414777795475843654257 58051061083346606882740693)
                  ·
                    refine ⟨1360571744140936098814235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58051061083346606882740693 1360571744140936098814235)
                    ·
                      rfl

theorem cell23_7949112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 2, 7].length) (baseStart_7949112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7949112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7949112 prefixEnd_7949112 := by exact prefixLift 7949112
  have htrace : WordTrace (prefixWord ++ tailWord_7949112) baseStart_7949112 baseEnd_7949112 := by
    simpa [prefixWord, tailWord_7949112, baseEnd_7949112] using wordTrace_append hprefix tailTrace_7949112
  have hstable : (prefixWord ++ tailWord_7949112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7949112).length < 2 ^ (prefixWord ++ tailWord_7949112).sum := by decide
  have hdescent : baseEnd_7949112 < baseStart_7949112 := by decide
  rcases family_descends (prefixWord ++ tailWord_7949112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7949143 : List Nat := [1, 1, 3, 2, 4, 1, 3, 2, 2, 1, 3]
def baseStart_7949143 : Nat := 118140960795 + 7949143 * 2 ^ 59
def prefixEnd_7949143 : Nat := 4983230072969 + 3 ^ 40 * 7949143 * 2
def baseEnd_7949143 : Nat := 4081731150323097675155063

theorem tailTrace_7949143 : CollatzResearch.WordTrace tailWord_7949143 prefixEnd_7949143 4081731150323097675155063 := by
  unfold tailWord_7949143
  simp only [CollatzResearch.WordTrace]
  refine ⟨289929063840619991385012083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193286042560413327590008055 289929063840619991385012083)
  ·
    refine ⟨434893595760929987077518125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289929063840619991385012083 434893595760929987077518125)
    ·
      refine ⟨163085098410348745154069297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 434893595760929987077518125 163085098410348745154069297)
      ·
        refine ⟨122313823807761558865551973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163085098410348745154069297 122313823807761558865551973)
        ·
          refine ⟨22933841963955292287290995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122313823807761558865551973 22933841963955292287290995)
          ·
            refine ⟨34400762945932938430936493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22933841963955292287290995 34400762945932938430936493)
            ·
              refine ⟨12900286104724851911601185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34400762945932938430936493 12900286104724851911601185)
              ·
                refine ⟨9675214578543638933700889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12900286104724851911601185 9675214578543638933700889)
                ·
                  refine ⟨7256410933907729200275667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9675214578543638933700889 7256410933907729200275667)
                  ·
                    refine ⟨10884616400861593800413501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7256410933907729200275667 10884616400861593800413501)
                    ·
                      refine ⟨4081731150323097675155063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10884616400861593800413501 4081731150323097675155063)
                      ·
                        rfl

theorem cell23_7949143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 2, 2, 1, 3].length) (baseStart_7949143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7949143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7949143 prefixEnd_7949143 := by exact prefixLift 7949143
  have htrace : WordTrace (prefixWord ++ tailWord_7949143) baseStart_7949143 baseEnd_7949143 := by
    simpa [prefixWord, tailWord_7949143, baseEnd_7949143] using wordTrace_append hprefix tailTrace_7949143
  have hstable : (prefixWord ++ tailWord_7949143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7949143).length < 2 ^ (prefixWord ++ tailWord_7949143).sum := by decide
  have hdescent : baseEnd_7949143 < baseStart_7949143 := by decide
  rcases family_descends (prefixWord ++ tailWord_7949143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7949159 : List Nat := [1, 1, 5, 1, 2, 2, 2, 1, 2, 6]
def baseStart_7949159 : Nat := 118140960795 + 7949159 * 2 ^ 59
def prefixEnd_7949159 : Nat := 4983230072969 + 3 ^ 40 * 7949159 * 2
def baseEnd_7949159 : Nat := 1360579788671189870851663

theorem tailTrace_7949159 : CollatzResearch.WordTrace tailWord_7949159 prefixEnd_7949159 1360579788671189870851663 := by
  unfold tailWord_7949159
  simp only [CollatzResearch.WordTrace]
  refine ⟨289929647408562026117594531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193286431605708017411729687 289929647408562026117594531)
  ·
    refine ⟨434894471112843039176391797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289929647408562026117594531 434894471112843039176391797)
    ·
      refine ⟨40771356666829034922786731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 434894471112843039176391797 40771356666829034922786731)
      ·
        refine ⟨61157035000243552384180097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40771356666829034922786731 61157035000243552384180097)
        ·
          refine ⟨45867776250182664288135073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61157035000243552384180097 45867776250182664288135073)
          ·
            refine ⟨34400832187636998216101305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45867776250182664288135073 34400832187636998216101305)
            ·
              refine ⟨25800624140727748662075979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34400832187636998216101305 25800624140727748662075979)
              ·
                refine ⟨38700936211091622993113969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25800624140727748662075979 38700936211091622993113969)
                ·
                  refine ⟨29025702158318717244835477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38700936211091622993113969 29025702158318717244835477)
                  ·
                    refine ⟨1360579788671189870851663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29025702158318717244835477 1360579788671189870851663)
                    ·
                      rfl

theorem cell23_7949159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 1, 2, 6].length) (baseStart_7949159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7949159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7949159 prefixEnd_7949159 := by exact prefixLift 7949159
  have htrace : WordTrace (prefixWord ++ tailWord_7949159) baseStart_7949159 baseEnd_7949159 := by
    simpa [prefixWord, tailWord_7949159, baseEnd_7949159] using wordTrace_append hprefix tailTrace_7949159
  have hstable : (prefixWord ++ tailWord_7949159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7949159).length < 2 ^ (prefixWord ++ tailWord_7949159).sum := by decide
  have hdescent : baseEnd_7949159 < baseStart_7949159 := by decide
  rcases family_descends (prefixWord ++ tailWord_7949159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7949160 : List Nat := [2, 1, 4, 2, 1, 3, 3, 1, 2, 1, 3]
def baseStart_7949160 : Nat := 118140960795 + 7949160 * 2 ^ 59
def prefixEnd_7949160 : Nat := 4983230072969 + 3 ^ 40 * 7949160 * 2
def baseEnd_7949160 : Nat := 4081739879494224108642485

theorem tailTrace_7949160 : CollatzResearch.WordTrace tailWord_7949160 prefixEnd_7949160 4081739879494224108642485 := by
  unfold tailWord_7949160
  simp only [CollatzResearch.WordTrace]
  refine ⟨144964841940779201644190467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193286455921038935525587289 144964841940779201644190467)
  ·
    refine ⟨217447262911168802466285701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144964841940779201644190467 217447262911168802466285701)
    ·
      refine ⟨40771361795844150462428569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 217447262911168802466285701 40771361795844150462428569)
      ·
        refine ⟨30578521346883112846821427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40771361795844150462428569 30578521346883112846821427)
        ·
          refine ⟨45867782020324669270232141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30578521346883112846821427 45867782020324669270232141)
          ·
            refine ⟨17200418257621750976337053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45867782020324669270232141 17200418257621750976337053)
            ·
              refine ⟨6450156846608156616126395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17200418257621750976337053 6450156846608156616126395)
              ·
                refine ⟨9675235269912234924189593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6450156846608156616126395 9675235269912234924189593)
                ·
                  refine ⟨7256426452434176193142195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9675235269912234924189593 7256426452434176193142195)
                  ·
                    refine ⟨10884639678651264289713293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7256426452434176193142195 10884639678651264289713293)
                    ·
                      refine ⟨4081739879494224108642485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10884639678651264289713293 4081739879494224108642485)
                      ·
                        rfl

theorem cell23_7949160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 3, 1, 2, 1, 3].length) (baseStart_7949160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7949160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7949160 prefixEnd_7949160 := by exact prefixLift 7949160
  have htrace : WordTrace (prefixWord ++ tailWord_7949160) baseStart_7949160 baseEnd_7949160 := by
    simpa [prefixWord, tailWord_7949160, baseEnd_7949160] using wordTrace_append hprefix tailTrace_7949160
  have hstable : (prefixWord ++ tailWord_7949160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7949160).length < 2 ^ (prefixWord ++ tailWord_7949160).sum := by decide
  have hdescent : baseEnd_7949160 < baseStart_7949160 := by decide
  rcases family_descends (prefixWord ++ tailWord_7949160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7949217 : List Nat := [1, 2, 3, 4, 1, 1, 4, 1, 2, 2, 2]
def baseStart_7949217 : Nat := 118140960795 + 7949217 * 2 ^ 59
def prefixEnd_7949217 : Nat := 4983230072969 + 3 ^ 40 * 7949217 * 2
def baseEnd_7949217 : Nat := 4081769147891530385629723

theorem tailTrace_7949217 : CollatzResearch.WordTrace tailWord_7949217 prefixEnd_7949217 4081769147891530385629723 := by
  unfold tailWord_7949217
  simp only [CollatzResearch.WordTrace]
  refine ⟨289931762842351902023205905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193287841894901268015470603 289931762842351902023205905)
  ·
    refine ⟨217448822131763926517404429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289931762842351902023205905 217448822131763926517404429)
    ·
      refine ⟨81543308299411472444026661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217448822131763926517404429 81543308299411472444026661)
      ·
        refine ⟨15289370306139651083254999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81543308299411472444026661 15289370306139651083254999)
        ·
          refine ⟨22934055459209476624882499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15289370306139651083254999 22934055459209476624882499)
          ·
            refine ⟨34401083188814214937323749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22934055459209476624882499 34401083188814214937323749)
            ·
              refine ⟨6450203097902665300748203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34401083188814214937323749 6450203097902665300748203)
              ·
                refine ⟨9675304646853997951122305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6450203097902665300748203 9675304646853997951122305)
                ·
                  refine ⟨7256478485140498463341729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9675304646853997951122305 7256478485140498463341729)
                  ·
                    refine ⟨5442358863855373847506297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7256478485140498463341729 5442358863855373847506297)
                    ·
                      refine ⟨4081769147891530385629723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5442358863855373847506297 4081769147891530385629723)
                      ·
                        rfl

theorem cell23_7949217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_7949217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7949217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7949217 prefixEnd_7949217 := by exact prefixLift 7949217
  have htrace : WordTrace (prefixWord ++ tailWord_7949217) baseStart_7949217 baseEnd_7949217 := by
    simpa [prefixWord, tailWord_7949217, baseEnd_7949217] using wordTrace_append hprefix tailTrace_7949217
  have hstable : (prefixWord ++ tailWord_7949217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7949217).length < 2 ^ (prefixWord ++ tailWord_7949217).sum := by decide
  have hdescent : baseEnd_7949217 < baseStart_7949217 := by decide
  rcases family_descends (prefixWord ++ tailWord_7949217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7949239 : List Nat := [1, 1, 3, 1, 3, 1, 2, 3, 1, 3, 4]
def baseStart_7949239 : Nat := 118140960795 + 7949239 * 2 ^ 59
def prefixEnd_7949239 : Nat := 4983230072969 + 3 ^ 40 * 7949239 * 2
def baseEnd_7949239 : Nat := 4081780444465929299554621

theorem tailTrace_7949239 : CollatzResearch.WordTrace tailWord_7949239 prefixEnd_7949239 4081780444465929299554621 := by
  unfold tailWord_7949239
  simp only [CollatzResearch.WordTrace]
  refine ⟨289932565248272199780506771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193288376832181466520337847 289932565248272199780506771)
  ·
    refine ⟨434898847872408299670760157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289932565248272199780506771 434898847872408299670760157)
    ·
      refine ⟨163087067952153112376535059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 434898847872408299670760157 163087067952153112376535059)
      ·
        refine ⟨244630601928229668564802589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163087067952153112376535059 244630601928229668564802589)
        ·
          refine ⟨91736475723086125711800971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 244630601928229668564802589 91736475723086125711800971)
          ·
            refine ⟨137604713584629188567701457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91736475723086125711800971 137604713584629188567701457)
            ·
              refine ⟨103203535188471891425776093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137604713584629188567701457 103203535188471891425776093)
              ·
                refine ⟨38701325695676959284666035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103203535188471891425776093 38701325695676959284666035)
                ·
                  refine ⟨58051988543515438926999053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38701325695676959284666035 58051988543515438926999053)
                  ·
                    refine ⟨21769495703818289597624645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58051988543515438926999053 21769495703818289597624645)
                    ·
                      refine ⟨4081780444465929299554621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21769495703818289597624645 4081780444465929299554621)
                      ·
                        rfl

theorem cell23_7949239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3, 1, 3, 4].length) (baseStart_7949239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7949239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7949239 prefixEnd_7949239 := by exact prefixLift 7949239
  have htrace : WordTrace (prefixWord ++ tailWord_7949239) baseStart_7949239 baseEnd_7949239 := by
    simpa [prefixWord, tailWord_7949239, baseEnd_7949239] using wordTrace_append hprefix tailTrace_7949239
  have hstable : (prefixWord ++ tailWord_7949239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7949239).length < 2 ^ (prefixWord ++ tailWord_7949239).sum := by decide
  have hdescent : baseEnd_7949239 < baseStart_7949239 := by decide
  rcases family_descends (prefixWord ++ tailWord_7949239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7949273 : List Nat := [1, 2, 1, 2, 5, 2, 1, 1, 2, 4, 2]
def baseStart_7949273 : Nat := 118140960795 + 7949273 * 2 ^ 59
def prefixEnd_7949273 : Nat := 4983230072969 + 3 ^ 40 * 7949273 * 2
def baseEnd_7949273 : Nat := 4081797902808182166529465

theorem tailTrace_7949273 : CollatzResearch.WordTrace tailWord_7949273 prefixEnd_7949273 4081797902808182166529465 := by
  unfold tailWord_7949273
  simp only [CollatzResearch.WordTrace]
  refine ⟨289933805330149023587244473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193289203553432682391496315 289933805330149023587244473)
  ·
    refine ⟨217450353997611767690433355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289933805330149023587244473 217450353997611767690433355)
    ·
      refine ⟨326175530996417651535650033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217450353997611767690433355 326175530996417651535650033)
      ·
        refine ⟨244631648247313238651737525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326175530996417651535650033 244631648247313238651737525)
        ·
          refine ⟨22934217023185616123600393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 244631648247313238651737525 22934217023185616123600393)
          ·
            refine ⟨17200662767389212092700295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22934217023185616123600393 17200662767389212092700295)
            ·
              refine ⟨25800994151083818139050443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17200662767389212092700295 25800994151083818139050443)
              ·
                refine ⟨38701491226625727208575665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25800994151083818139050443 38701491226625727208575665)
                ·
                  refine ⟨29026118419969295406431749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38701491226625727208575665 29026118419969295406431749)
                  ·
                    refine ⟨5442397203744242888705953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29026118419969295406431749 5442397203744242888705953)
                    ·
                      refine ⟨4081797902808182166529465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5442397203744242888705953 4081797902808182166529465)
                      ·
                        rfl

theorem cell23_7949273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 1, 2, 4, 2].length) (baseStart_7949273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7949273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7949273 prefixEnd_7949273 := by exact prefixLift 7949273
  have htrace : WordTrace (prefixWord ++ tailWord_7949273) baseStart_7949273 baseEnd_7949273 := by
    simpa [prefixWord, tailWord_7949273, baseEnd_7949273] using wordTrace_append hprefix tailTrace_7949273
  have hstable : (prefixWord ++ tailWord_7949273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7949273).length < 2 ^ (prefixWord ++ tailWord_7949273).sum := by decide
  have hdescent : baseEnd_7949273 < baseStart_7949273 := by decide
  rcases family_descends (prefixWord ++ tailWord_7949273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7949313 : List Nat := [1, 2, 4, 1, 2, 4, 1, 2, 6]
def baseStart_7949313 : Nat := 118140960795 + 7949313 * 2 ^ 59
def prefixEnd_7949313 : Nat := 4983230072969 + 3 ^ 40 * 7949313 * 2
def baseEnd_7949313 : Nat := 453535382448262445558809

theorem tailTrace_7949313 : CollatzResearch.WordTrace tailWord_7949313 prefixEnd_7949313 453535382448262445558809 := by
  unfold tailWord_7949313
  simp only [CollatzResearch.WordTrace]
  refine ⟨289935264250004110418700593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193290176166669406945800395 289935264250004110418700593)
  ·
    refine ⟨217451448187503082814025445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289935264250004110418700593 217451448187503082814025445)
    ·
      refine ⟨40772146535156828027629771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 217451448187503082814025445 40772146535156828027629771)
      ·
        refine ⟨61158219802735242041444657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40772146535156828027629771 61158219802735242041444657)
        ·
          refine ⟨45868664852051431531083493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61158219802735242041444657 45868664852051431531083493)
          ·
            refine ⟨8600374659759643412078155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45868664852051431531083493 8600374659759643412078155)
            ·
              refine ⟨12900561989639465118117233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8600374659759643412078155 12900561989639465118117233)
              ·
                refine ⟨9675421492229598838587925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12900561989639465118117233 9675421492229598838587925)
                ·
                  refine ⟨453535382448262445558809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9675421492229598838587925 453535382448262445558809)
                  ·
                    rfl

theorem cell23_7949313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 2, 6].length) (baseStart_7949313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7949313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7949313 prefixEnd_7949313 := by exact prefixLift 7949313
  have htrace : WordTrace (prefixWord ++ tailWord_7949313) baseStart_7949313 baseEnd_7949313 := by
    simpa [prefixWord, tailWord_7949313, baseEnd_7949313] using wordTrace_append hprefix tailTrace_7949313
  have hstable : (prefixWord ++ tailWord_7949313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7949313).length < 2 ^ (prefixWord ++ tailWord_7949313).sum := by decide
  have hdescent : baseEnd_7949313 < baseStart_7949313 := by decide
  rcases family_descends (prefixWord ++ tailWord_7949313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7949323 : List Nat := [1, 1, 1, 1, 6, 2, 1, 3, 3, 1, 3]
def baseStart_7949323 : Nat := 118140960795 + 7949323 * 2 ^ 59
def prefixEnd_7949323 : Nat := 4983230072969 + 3 ^ 40 * 7949323 * 2
def baseEnd_7949323 : Nat := 4081823576840906970904235

theorem tailTrace_7949323 : CollatzResearch.WordTrace tailWord_7949323 prefixEnd_7949323 4081823576840906970904235 := by
  unfold tailWord_7949323
  simp only [CollatzResearch.WordTrace]
  refine ⟨289935628979967882126564623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193290419319978588084376415 289935628979967882126564623)
  ·
    refine ⟨434903443469951823189846935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289935628979967882126564623 434903443469951823189846935)
    ·
      refine ⟨652355165204927734784770403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434903443469951823189846935 652355165204927734784770403)
      ·
        refine ⟨978532747807391602177155605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 652355165204927734784770403 978532747807391602177155605)
        ·
          refine ⟨45868722553471481352054169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 978532747807391602177155605 45868722553471481352054169)
          ·
            refine ⟨34401541915103611014040627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45868722553471481352054169 34401541915103611014040627)
            ·
              refine ⟨51602312872655416521060941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34401541915103611014040627 51602312872655416521060941)
              ·
                refine ⟨19350867327245781195397853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51602312872655416521060941 19350867327245781195397853)
                ·
                  refine ⟨7256575247717167948274195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19350867327245781195397853 7256575247717167948274195)
                  ·
                    refine ⟨10884862871575751922411293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7256575247717167948274195 10884862871575751922411293)
                    ·
                      refine ⟨4081823576840906970904235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10884862871575751922411293 4081823576840906970904235)
                      ·
                        rfl

theorem cell23_7949323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 3, 3, 1, 3].length) (baseStart_7949323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7949323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7949323 prefixEnd_7949323 := by exact prefixLift 7949323
  have htrace : WordTrace (prefixWord ++ tailWord_7949323) baseStart_7949323 baseEnd_7949323 := by
    simpa [prefixWord, tailWord_7949323, baseEnd_7949323] using wordTrace_append hprefix tailTrace_7949323
  have hstable : (prefixWord ++ tailWord_7949323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7949323).length < 2 ^ (prefixWord ++ tailWord_7949323).sum := by decide
  have hdescent : baseEnd_7949323 < baseStart_7949323 := by decide
  rcases family_descends (prefixWord ++ tailWord_7949323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7949333 : List Nat := [1, 3, 2, 1, 4, 1, 1, 2, 1, 5, 2]
def baseStart_7949333 : Nat := 118140960795 + 7949333 * 2 ^ 59
def prefixEnd_7949333 : Nat := 4983230072969 + 3 ^ 40 * 7949333 * 2
def baseEnd_7949333 : Nat := 4081828711647451931779189

theorem tailTrace_7949333 : CollatzResearch.WordTrace tailWord_7949333 prefixEnd_7949333 4081828711647451931779189 := by
  unfold tailWord_7949333
  simp only [CollatzResearch.WordTrace]
  refine ⟨289935993709931653834428653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193290662473287769222952435 289935993709931653834428653)
  ·
    refine ⟨108725997641224370187910745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289935993709931653834428653 108725997641224370187910745)
    ·
      refine ⟨81544498230918277640933059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108725997641224370187910745 81544498230918277640933059)
      ·
        refine ⟨122316747346377416461399589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81544498230918277640933059 122316747346377416461399589)
        ·
          refine ⟨22934390127445765586512423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122316747346377416461399589 22934390127445765586512423)
          ·
            refine ⟨34401585191168648379768635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22934390127445765586512423 34401585191168648379768635)
            ·
              refine ⟨51602377786752972569652953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34401585191168648379768635 51602377786752972569652953)
              ·
                refine ⟨38701783340064729427239715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51602377786752972569652953 38701783340064729427239715)
                ·
                  refine ⟨58052675010097094140859573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38701783340064729427239715 58052675010097094140859573)
                  ·
                    refine ⟨5442438282196602575705585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58052675010097094140859573 5442438282196602575705585)
                    ·
                      refine ⟨4081828711647451931779189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5442438282196602575705585 4081828711647451931779189)
                      ·
                        rfl

theorem cell23_7949333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 2, 1, 5, 2].length) (baseStart_7949333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7949333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7949333 prefixEnd_7949333 := by exact prefixLift 7949333
  have htrace : WordTrace (prefixWord ++ tailWord_7949333) baseStart_7949333 baseEnd_7949333 := by
    simpa [prefixWord, tailWord_7949333, baseEnd_7949333] using wordTrace_append hprefix tailTrace_7949333
  have hstable : (prefixWord ++ tailWord_7949333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7949333).length < 2 ^ (prefixWord ++ tailWord_7949333).sum := by decide
  have hdescent : baseEnd_7949333 < baseStart_7949333 := by decide
  rcases family_descends (prefixWord ++ tailWord_7949333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7949343 : List Nat := [1, 1, 2, 4, 1, 4, 2, 2, 1, 5]
def baseStart_7949343 : Nat := 118140960795 + 7949343 * 2 ^ 59
def prefixEnd_7949343 : Nat := 4983230072969 + 3 ^ 40 * 7949343 * 2
def baseEnd_7949343 : Nat := 1360611282151332297551381

theorem tailTrace_7949343 : CollatzResearch.WordTrace tailWord_7949343 prefixEnd_7949343 1360611282151332297551381 := by
  unfold tailWord_7949343
  simp only [CollatzResearch.WordTrace]
  refine ⟨289936358439895425542292683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193290905626596950361528455 289936358439895425542292683)
  ·
    refine ⟨434904537659843138313439025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289936358439895425542292683 434904537659843138313439025)
    ·
      refine ⟨326178403244882353735079269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 434904537659843138313439025 326178403244882353735079269)
      ·
        refine ⟨61158450608415441325327363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 326178403244882353735079269 61158450608415441325327363)
        ·
          refine ⟨91737675912623161987991045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61158450608415441325327363 91737675912623161987991045)
          ·
            refine ⟨17200814233616842872748321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91737675912623161987991045 17200814233616842872748321)
            ·
              refine ⟨12900610675212632154561241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17200814233616842872748321 12900610675212632154561241)
              ·
                refine ⟨9675458006409474115920931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12900610675212632154561241 9675458006409474115920931)
                ·
                  refine ⟨14513187009614211173881397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9675458006409474115920931 14513187009614211173881397)
                  ·
                    refine ⟨1360611282151332297551381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14513187009614211173881397 1360611282151332297551381)
                    ·
                      rfl

theorem cell23_7949343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 2, 1, 5].length) (baseStart_7949343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7949343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7949343 prefixEnd_7949343 := by exact prefixLift 7949343
  have htrace : WordTrace (prefixWord ++ tailWord_7949343) baseStart_7949343 baseEnd_7949343 := by
    simpa [prefixWord, tailWord_7949343, baseEnd_7949343] using wordTrace_append hprefix tailTrace_7949343
  have hstable : (prefixWord ++ tailWord_7949343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7949343).length < 2 ^ (prefixWord ++ tailWord_7949343).sum := by decide
  have hdescent : baseEnd_7949343 < baseStart_7949343 := by decide
  rcases family_descends (prefixWord ++ tailWord_7949343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7949356 : List Nat := [2, 2, 1, 1, 1, 2, 3, 1, 6, 4]
def baseStart_7949356 : Nat := 118140960795 + 7949356 * 2 ^ 59
def prefixEnd_7949356 : Nat := 4983230072969 + 3 ^ 40 * 7949356 * 2
def baseEnd_7949356 : Nat := 1360613507234168447263861

theorem tailTrace_7949356 : CollatzResearch.WordTrace tailWord_7949356 prefixEnd_7949356 1360613507234168447263861 := by
  unfold tailWord_7949356
  simp only [CollatzResearch.WordTrace]
  refine ⟨144968416294424164381257961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193291221725898885841677281 144968416294424164381257961)
  ·
    refine ⟨108726312220818123285943471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144968416294424164381257961 108726312220818123285943471)
    ·
      refine ⟨163089468331227184928915207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108726312220818123285943471 163089468331227184928915207)
      ·
        refine ⟨244634202496840777393372811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163089468331227184928915207 244634202496840777393372811)
        ·
          refine ⟨366951303745261166090059217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244634202496840777393372811 366951303745261166090059217)
          ·
            refine ⟨275213477808945874567544413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 366951303745261166090059217 275213477808945874567544413)
            ·
              refine ⟨103205054178354702962829155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 275213477808945874567544413 103205054178354702962829155)
              ·
                refine ⟨154807581267532054444243733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103205054178354702962829155 154807581267532054444243733)
                ·
                  refine ⟨7256605371915565052073925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 154807581267532054444243733 7256605371915565052073925)
                  ·
                    refine ⟨1360613507234168447263861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7256605371915565052073925 1360613507234168447263861)
                    ·
                      rfl

theorem cell23_7949356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 4].length) (baseStart_7949356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7949356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7949356 prefixEnd_7949356 := by exact prefixLift 7949356
  have htrace : WordTrace (prefixWord ++ tailWord_7949356) baseStart_7949356 baseEnd_7949356 := by
    simpa [prefixWord, tailWord_7949356, baseEnd_7949356] using wordTrace_append hprefix tailTrace_7949356
  have hstable : (prefixWord ++ tailWord_7949356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7949356).length < 2 ^ (prefixWord ++ tailWord_7949356).sum := by decide
  have hdescent : baseEnd_7949356 < baseStart_7949356 := by decide
  rcases family_descends (prefixWord ++ tailWord_7949356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7949373 : List Nat := [1, 4, 1, 3, 1, 2, 2, 1, 4, 4]
def baseStart_7949373 : Nat := 118140960795 + 7949373 * 2 ^ 59
def prefixEnd_7949373 : Nat := 4983230072969 + 3 ^ 40 * 7949373 * 2
def baseEnd_7949373 : Nat := 1360616416957877258426335

theorem tailTrace_7949373 : CollatzResearch.WordTrace tailWord_7949373 prefixEnd_7949373 1360616416957877258426335 := by
  unfold tailWord_7949373
  simp only [CollatzResearch.WordTrace]
  refine ⟨289937452629786740665884773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193291635086524493777256515 289937452629786740665884773)
  ·
    refine ⟨54363272368085013874853395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 289937452629786740665884773 54363272368085013874853395)
    ·
      refine ⟨81544908552127520812280093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54363272368085013874853395 81544908552127520812280093)
      ·
        refine ⟨30579340707047820304605035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81544908552127520812280093 30579340707047820304605035)
        ·
          refine ⟨45869011060571730456907553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30579340707047820304605035 45869011060571730456907553)
          ·
            refine ⟨34401758295428797842680665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45869011060571730456907553 34401758295428797842680665)
            ·
              refine ⟨25801318721571598382010499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34401758295428797842680665 25801318721571598382010499)
              ·
                refine ⟨38701978082357397573015749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25801318721571598382010499 38701978082357397573015749)
                ·
                  refine ⟨7256620890442012044940453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38701978082357397573015749 7256620890442012044940453)
                  ·
                    refine ⟨1360616416957877258426335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7256620890442012044940453 1360616416957877258426335)
                    ·
                      rfl

theorem cell23_7949373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 1, 4, 4].length) (baseStart_7949373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7949373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7949373 prefixEnd_7949373 := by exact prefixLift 7949373
  have htrace : WordTrace (prefixWord ++ tailWord_7949373) baseStart_7949373 baseEnd_7949373 := by
    simpa [prefixWord, tailWord_7949373, baseEnd_7949373] using wordTrace_append hprefix tailTrace_7949373
  have hstable : (prefixWord ++ tailWord_7949373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7949373).length < 2 ^ (prefixWord ++ tailWord_7949373).sum := by decide
  have hdescent : baseEnd_7949373 < baseStart_7949373 := by decide
  rcases family_descends (prefixWord ++ tailWord_7949373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7949410 : List Nat := [3, 3, 2, 2, 1, 2, 1, 2, 1, 2, 4]
def baseStart_7949410 : Nat := 118140960795 + 7949410 * 2 ^ 59
def prefixEnd_7949410 : Nat := 4983230072969 + 3 ^ 40 * 7949410 * 2
def baseEnd_7949410 : Nat := 4081868249657848130516335

theorem tailTrace_7949410 : CollatzResearch.WordTrace tailWord_7949410 prefixEnd_7949410 4081868249657848130516335 := by
  unfold tailWord_7949410
  simp only [CollatzResearch.WordTrace]
  refine ⟨72484700532663173996245421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193292534753768463989987789 72484700532663173996245421)
  ·
    refine ⟨27181762699748690248592033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72484700532663173996245421 27181762699748690248592033)
    ·
      refine ⟨20386322024811517686444025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27181762699748690248592033 20386322024811517686444025)
      ·
        refine ⟨15289741518608638264833019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20386322024811517686444025 15289741518608638264833019)
        ·
          refine ⟨22934612277912957397249529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15289741518608638264833019 22934612277912957397249529)
          ·
            refine ⟨17200959208434718047937147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22934612277912957397249529 17200959208434718047937147)
            ·
              refine ⟨25801438812652077071905721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17200959208434718047937147 25801438812652077071905721)
              ·
                refine ⟨19351079109489057803929291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25801438812652077071905721 19351079109489057803929291)
                ·
                  refine ⟨29026618664233586705893937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19351079109489057803929291 29026618664233586705893937)
                  ·
                    refine ⟨21769963998175190029420453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29026618664233586705893937 21769963998175190029420453)
                    ·
                      refine ⟨4081868249657848130516335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21769963998175190029420453 4081868249657848130516335)
                      ·
                        rfl

theorem cell23_7949410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_7949410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7949410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7949410 prefixEnd_7949410 := by exact prefixLift 7949410
  have htrace : WordTrace (prefixWord ++ tailWord_7949410) baseStart_7949410 baseEnd_7949410 := by
    simpa [prefixWord, tailWord_7949410, baseEnd_7949410] using wordTrace_append hprefix tailTrace_7949410
  have hstable : (prefixWord ++ tailWord_7949410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7949410).length < 2 ^ (prefixWord ++ tailWord_7949410).sum := by decide
  have hdescent : baseEnd_7949410 < baseStart_7949410 := by decide
  rcases family_descends (prefixWord ++ tailWord_7949410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7949413 : List Nat := [1, 3, 1, 3, 2, 1, 3, 2, 1, 3, 3]
def baseStart_7949413 : Nat := 118140960795 + 7949413 * 2 ^ 59
def prefixEnd_7949413 : Nat := 4983230072969 + 3 ^ 40 * 7949413 * 2
def baseEnd_7949413 : Nat := 4081869790099811618778821

theorem tailTrace_7949413 : CollatzResearch.WordTrace tailWord_7949413 prefixEnd_7949413 4081869790099811618778821 := by
  unfold tailWord_7949413
  simp only [CollatzResearch.WordTrace]
  refine ⟨289938911549641827497340893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193292607699761218331560595 289938911549641827497340893)
  ·
    refine ⟨108727091831115685311502835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289938911549641827497340893 108727091831115685311502835)
    ·
      refine ⟨163090637746673527967254253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108727091831115685311502835 163090637746673527967254253)
      ·
        refine ⟨61158989155002572987720345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163090637746673527967254253 61158989155002572987720345)
        ·
          refine ⟨45869241866251929740790259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61158989155002572987720345 45869241866251929740790259)
          ·
            refine ⟨68803862799377894611185389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45869241866251929740790259 68803862799377894611185389)
            ·
              refine ⟨25801448549766710479194521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68803862799377894611185389 25801448549766710479194521)
              ·
                refine ⟨19351086412325032859395891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25801448549766710479194521 19351086412325032859395891)
                ·
                  refine ⟨29026629618487549289093837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19351086412325032859395891 29026629618487549289093837)
                  ·
                    refine ⟨10884986106932830983410189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29026629618487549289093837 10884986106932830983410189)
                    ·
                      refine ⟨4081869790099811618778821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10884986106932830983410189 4081869790099811618778821)
                      ·
                        rfl

theorem cell23_7949413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 2, 1, 3, 3].length) (baseStart_7949413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7949413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7949413 prefixEnd_7949413 := by exact prefixLift 7949413
  have htrace : WordTrace (prefixWord ++ tailWord_7949413) baseStart_7949413 baseEnd_7949413 := by
    simpa [prefixWord, tailWord_7949413, baseEnd_7949413] using wordTrace_append hprefix tailTrace_7949413
  have hstable : (prefixWord ++ tailWord_7949413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7949413).length < 2 ^ (prefixWord ++ tailWord_7949413).sum := by decide
  have hdescent : baseEnd_7949413 < baseStart_7949413 := by decide
  rcases family_descends (prefixWord ++ tailWord_7949413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7949436 : List Nat := [2, 2, 2, 1, 1, 3, 1, 1, 1, 5, 4]
def baseStart_7949436 : Nat := 118140960795 + 7949436 * 2 ^ 59
def prefixEnd_7949436 : Nat := 4983230072969 + 3 ^ 40 * 7949436 * 2
def baseEnd_7949436 : Nat := 4081881600154865028791215

theorem tailTrace_7949436 : CollatzResearch.WordTrace tailWord_7949436 prefixEnd_7949436 4081881600154865028791215 := by
  unfold tailWord_7949436
  simp only [CollatzResearch.WordTrace]
  refine ⟨144969875214279251212714081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193293166952372334950285441 144969875214279251212714081)
  ·
    refine ⟨108727406410709438409535561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144969875214279251212714081 108727406410709438409535561)
    ·
      refine ⟨81545554808032078807151671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108727406410709438409535561 81545554808032078807151671)
      ·
        refine ⟨122318332212048118210727507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81545554808032078807151671 122318332212048118210727507)
        ·
          refine ⟨183477498318072177316091261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122318332212048118210727507 183477498318072177316091261)
          ·
            refine ⟨68804061869277066493534223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183477498318072177316091261 68804061869277066493534223)
            ·
              refine ⟨103206092803915599740301335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68804061869277066493534223 103206092803915599740301335)
              ·
                refine ⟨154809139205873399610452003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103206092803915599740301335 154809139205873399610452003)
                ·
                  refine ⟨232213708808810099415678005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 154809139205873399610452003 232213708808810099415678005)
                  ·
                    refine ⟨21770035200825946820219813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 232213708808810099415678005 21770035200825946820219813)
                    ·
                      refine ⟨4081881600154865028791215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21770035200825946820219813 4081881600154865028791215)
                      ·
                        rfl

theorem cell23_7949436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 1, 5, 4].length) (baseStart_7949436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7949436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7949436 prefixEnd_7949436 := by exact prefixLift 7949436
  have htrace : WordTrace (prefixWord ++ tailWord_7949436) baseStart_7949436 baseEnd_7949436 := by
    simpa [prefixWord, tailWord_7949436, baseEnd_7949436] using wordTrace_append hprefix tailTrace_7949436
  have hstable : (prefixWord ++ tailWord_7949436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7949436).length < 2 ^ (prefixWord ++ tailWord_7949436).sum := by decide
  have hdescent : baseEnd_7949436 < baseStart_7949436 := by decide
  rcases family_descends (prefixWord ++ tailWord_7949436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7949456 : List Nat := [2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 5]
def baseStart_7949456 : Nat := 118140960795 + 7949456 * 2 ^ 59
def prefixEnd_7949456 : Nat := 4983230072969 + 3 ^ 40 * 7949456 * 2
def baseEnd_7949456 : Nat := 4081891869767954950541123

theorem tailTrace_7949456 : CollatzResearch.WordTrace tailWord_7949456 prefixEnd_7949456 4081891869767954950541123 := by
  unfold tailWord_7949456
  simp only [CollatzResearch.WordTrace]
  refine ⟨144970239944243022920578111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193293653258990697227437481 144970239944243022920578111)
  ·
    refine ⟨217455359916364534380867167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144970239944243022920578111 217455359916364534380867167)
    ·
      refine ⟨326183039874546801571300751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217455359916364534380867167 326183039874546801571300751)
      ·
        refine ⟨489274559811820202356951127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326183039874546801571300751 489274559811820202356951127)
        ·
          refine ⟨733911839717730303535426691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 489274559811820202356951127 733911839717730303535426691)
          ·
            refine ⟨1100867759576595455303140037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 733911839717730303535426691 1100867759576595455303140037)
            ·
              refine ⟨206412704920611647869338757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1100867759576595455303140037 206412704920611647869338757)
              ·
                refine ⟨38702382172614683975501017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 206412704920611647869338757 38702382172614683975501017)
                ·
                  refine ⟨29026786629461012981625763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38702382172614683975501017 29026786629461012981625763)
                  ·
                    refine ⟨43540179944191519472438645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29026786629461012981625763 43540179944191519472438645)
                    ·
                      refine ⟨4081891869767954950541123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43540179944191519472438645 4081891869767954950541123)
                      ·
                        rfl

theorem cell23_7949456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 5].length) (baseStart_7949456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7949456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7949456 prefixEnd_7949456 := by exact prefixLift 7949456
  have htrace : WordTrace (prefixWord ++ tailWord_7949456) baseStart_7949456 baseEnd_7949456 := by
    simpa [prefixWord, tailWord_7949456, baseEnd_7949456] using wordTrace_append hprefix tailTrace_7949456
  have hstable : (prefixWord ++ tailWord_7949456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7949456).length < 2 ^ (prefixWord ++ tailWord_7949456).sum := by decide
  have hdescent : baseEnd_7949456 < baseStart_7949456 := by decide
  rcases family_descends (prefixWord ++ tailWord_7949456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7949474 : List Nat := [3, 3, 1, 3, 2, 1, 1, 3, 1, 3, 2]
def baseStart_7949474 : Nat := 118140960795 + 7949474 * 2 ^ 59
def prefixEnd_7949474 : Nat := 4983230072969 + 3 ^ 40 * 7949474 * 2
def baseEnd_7949474 : Nat := 4081901112419735880116041

theorem tailTrace_7949474 : CollatzResearch.WordTrace tailWord_7949474 prefixEnd_7949474 4081901112419735880116041 := by
  unfold tailWord_7949474
  simp only [CollatzResearch.WordTrace]
  refine ⟨72485284100605208728827869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193294090934947223276874317 72485284100605208728827869)
  ·
    refine ⟨27181981537726953273310451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72485284100605208728827869 27181981537726953273310451)
    ·
      refine ⟨40772972306590429909965677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27181981537726953273310451 40772972306590429909965677)
      ·
        refine ⟨15289864614971411216237129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40772972306590429909965677 15289864614971411216237129)
        ·
          refine ⟨11467398461228558412177847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15289864614971411216237129 11467398461228558412177847)
          ·
            refine ⟨17201097691842837618266771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11467398461228558412177847 17201097691842837618266771)
            ·
              refine ⟨25801646537764256427400157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17201097691842837618266771 25801646537764256427400157)
              ·
                refine ⟨9675617451661596160275059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25801646537764256427400157 9675617451661596160275059)
                ·
                  refine ⟨14513426177492394240412589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9675617451661596160275059 14513426177492394240412589)
                  ·
                    refine ⟨5442534816559647840154721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14513426177492394240412589 5442534816559647840154721)
                    ·
                      refine ⟨4081901112419735880116041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5442534816559647840154721 4081901112419735880116041)
                      ·
                        rfl

theorem cell23_7949474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_7949474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7949474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7949474 prefixEnd_7949474 := by exact prefixLift 7949474
  have htrace : WordTrace (prefixWord ++ tailWord_7949474) baseStart_7949474 baseEnd_7949474 := by
    simpa [prefixWord, tailWord_7949474, baseEnd_7949474] using wordTrace_append hprefix tailTrace_7949474
  have hstable : (prefixWord ++ tailWord_7949474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7949474).length < 2 ^ (prefixWord ++ tailWord_7949474).sum := by decide
  have hdescent : baseEnd_7949474 < baseStart_7949474 := by decide
  rcases family_descends (prefixWord ++ tailWord_7949474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7949487 : List Nat := [1, 1, 2, 1, 2, 3, 5, 2, 2, 2, 2]
def baseStart_7949487 : Nat := 118140960795 + 7949487 * 2 ^ 59
def prefixEnd_7949487 : Nat := 4983230072969 + 3 ^ 40 * 7949487 * 2
def baseEnd_7949487 : Nat := 4081907787668244329253481

theorem tailTrace_7949487 : CollatzResearch.WordTrace tailWord_7949487 prefixEnd_7949487 4081907787668244329253481 := by
  unfold tailWord_7949487
  simp only [CollatzResearch.WordTrace]
  refine ⟨289941610551373738135534715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193294407034249158757023143 289941610551373738135534715)
  ·
    refine ⟨434912415827060607203302073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289941610551373738135534715 434912415827060607203302073)
    ·
      refine ⟨326184311870295455402476555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 434912415827060607203302073 326184311870295455402476555)
      ·
        refine ⟨489276467805443183103714833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326184311870295455402476555 489276467805443183103714833)
        ·
          refine ⟨366957350854082387327786125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 489276467805443183103714833 366957350854082387327786125)
          ·
            refine ⟨137609006570280895247919797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 366957350854082387327786125 137609006570280895247919797)
            ·
              refine ⟨12900844365963833929492481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 137609006570280895247919797 12900844365963833929492481)
              ·
                refine ⟨9675633274472875447119361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12900844365963833929492481 9675633274472875447119361)
                ·
                  refine ⟨7256724955854656585339521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9675633274472875447119361 7256724955854656585339521)
                  ·
                    refine ⟨5442543716890992439004641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7256724955854656585339521 5442543716890992439004641)
                    ·
                      refine ⟨4081907787668244329253481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5442543716890992439004641 4081907787668244329253481)
                      ·
                        rfl

theorem cell23_7949487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 2, 2, 2, 2].length) (baseStart_7949487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7949487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7949487 prefixEnd_7949487 := by exact prefixLift 7949487
  have htrace : WordTrace (prefixWord ++ tailWord_7949487) baseStart_7949487 baseEnd_7949487 := by
    simpa [prefixWord, tailWord_7949487, baseEnd_7949487] using wordTrace_append hprefix tailTrace_7949487
  have hstable : (prefixWord ++ tailWord_7949487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7949487).length < 2 ^ (prefixWord ++ tailWord_7949487).sum := by decide
  have hdescent : baseEnd_7949487 < baseStart_7949487 := by decide
  rcases family_descends (prefixWord ++ tailWord_7949487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7949503 : List Nat := [1, 1, 2, 2, 2, 2, 4, 1, 2, 3, 3]
def baseStart_7949503 : Nat := 118140960795 + 7949503 * 2 ^ 59
def prefixEnd_7949503 : Nat := 4983230072969 + 3 ^ 40 * 7949503 * 2
def baseEnd_7949503 : Nat := 4081916003358716266653407

theorem tailTrace_7949503 : CollatzResearch.WordTrace tailWord_7949503 prefixEnd_7949503 4081916003358716266653407 := by
  unfold tailWord_7949503
  simp only [CollatzResearch.WordTrace]
  refine ⟨289942194119315772868117163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193294796079543848578744775 289942194119315772868117163)
  ·
    refine ⟨434913291178973659302175745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289942194119315772868117163 434913291178973659302175745)
    ·
      refine ⟨326184968384230244476631809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 434913291178973659302175745 326184968384230244476631809)
      ·
        refine ⟨244638726288172683357473857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326184968384230244476631809 244638726288172683357473857)
        ·
          refine ⟨183479044716129512518105393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244638726288172683357473857 183479044716129512518105393)
          ·
            refine ⟨137609283537097134388579045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183479044716129512518105393 137609283537097134388579045)
            ·
              refine ⟨25801740663205712697858571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137609283537097134388579045 25801740663205712697858571)
              ·
                refine ⟨38702610994808569046787857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25801740663205712697858571 38702610994808569046787857)
                ·
                  refine ⟨29026958246106426785090893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38702610994808569046787857 29026958246106426785090893)
                  ·
                    refine ⟨10885109342289910044409085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29026958246106426785090893 10885109342289910044409085)
                    ·
                      refine ⟨4081916003358716266653407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10885109342289910044409085 4081916003358716266653407)
                      ·
                        rfl

theorem cell23_7949503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 1, 2, 3, 3].length) (baseStart_7949503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7949503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7949503 prefixEnd_7949503 := by exact prefixLift 7949503
  have htrace : WordTrace (prefixWord ++ tailWord_7949503) baseStart_7949503 baseEnd_7949503 := by
    simpa [prefixWord, tailWord_7949503, baseEnd_7949503] using wordTrace_append hprefix tailTrace_7949503
  have hstable : (prefixWord ++ tailWord_7949503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7949503).length < 2 ^ (prefixWord ++ tailWord_7949503).sum := by decide
  have hdescent : baseEnd_7949503 < baseStart_7949503 := by decide
  rcases family_descends (prefixWord ++ tailWord_7949503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7949504 : List Nat := [2, 1, 1, 2, 7, 1, 1, 1, 1, 4, 2]
def baseStart_7949504 : Nat := 118140960795 + 7949504 * 2 ^ 59
def prefixEnd_7949504 : Nat := 4983230072969 + 3 ^ 40 * 7949504 * 2
def baseEnd_7949504 : Nat := 4081916516839370762740903

theorem tailTrace_7949504 : CollatzResearch.WordTrace tailWord_7949504 prefixEnd_7949504 4081916516839370762740903 := by
  unfold tailWord_7949504
  simp only [CollatzResearch.WordTrace]
  refine ⟨144971115296156075019451783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193294820394874766692602377 144971115296156075019451783)
  ·
    refine ⟨217456672944234112529177675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144971115296156075019451783 217456672944234112529177675)
    ·
      refine ⟨326185009416351168793766513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217456672944234112529177675 326185009416351168793766513)
      ·
        refine ⟨244638757062263376595324885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326185009416351168793766513 244638757062263376595324885)
        ·
          refine ⟨5733720868646797888952927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 244638757062263376595324885 5733720868646797888952927)
          ·
            refine ⟨8600581302970196833429391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5733720868646797888952927 8600581302970196833429391)
            ·
              refine ⟨12900871954455295250144087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8600581302970196833429391 12900871954455295250144087)
              ·
                refine ⟨19351307931682942875216131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12900871954455295250144087 19351307931682942875216131)
                ·
                  refine ⟨29026961897524414312824197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19351307931682942875216131 29026961897524414312824197)
                  ·
                    refine ⟨5442555355785827683654537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29026961897524414312824197 5442555355785827683654537)
                    ·
                      refine ⟨4081916516839370762740903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5442555355785827683654537 4081916516839370762740903)
                      ·
                        rfl

theorem cell23_7949504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 1, 1, 4, 2].length) (baseStart_7949504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7949504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7949504 prefixEnd_7949504 := by exact prefixLift 7949504
  have htrace : WordTrace (prefixWord ++ tailWord_7949504) baseStart_7949504 baseEnd_7949504 := by
    simpa [prefixWord, tailWord_7949504, baseEnd_7949504] using wordTrace_append hprefix tailTrace_7949504
  have hstable : (prefixWord ++ tailWord_7949504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7949504).length < 2 ^ (prefixWord ++ tailWord_7949504).sum := by decide
  have hdescent : baseEnd_7949504 < baseStart_7949504 := by decide
  rcases family_descends (prefixWord ++ tailWord_7949504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7949513 : List Nat := [1, 2, 1, 1, 2, 1, 1, 2, 3, 7, 2]
def baseStart_7949513 : Nat := 118140960795 + 7949513 * 2 ^ 59
def prefixEnd_7949513 : Nat := 4983230072969 + 3 ^ 40 * 7949513 * 2
def baseEnd_7949513 : Nat := 4081921138165261227528361

theorem tailTrace_7949513 : CollatzResearch.WordTrace tailWord_7949513 prefixEnd_7949513 4081921138165261227528361 := by
  unfold tailWord_7949513
  simp only [CollatzResearch.WordTrace]
  refine ⟨289942558849279544575981193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193295039232853029717320795 289942558849279544575981193)
  ·
    refine ⟨217456919136959658431985895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289942558849279544575981193 217456919136959658431985895)
    ·
      refine ⟨326185378705439487647978843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217456919136959658431985895 326185378705439487647978843)
      ·
        refine ⟨489278068058159231471968265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326185378705439487647978843 489278068058159231471968265)
        ·
          refine ⟨366958551043619423603976199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 489278068058159231471968265 366958551043619423603976199)
          ·
            refine ⟨550437826565429135405964299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366958551043619423603976199 550437826565429135405964299)
            ·
              refine ⟨825656739848143703108946449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 550437826565429135405964299 825656739848143703108946449)
              ·
                refine ⟨619242554886107777331709837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 825656739848143703108946449 619242554886107777331709837)
                ·
                  refine ⟨232215958082290416499391189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 619242554886107777331709837 232215958082290416499391189)
                  ·
                    refine ⟨5442561517553681636704481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 232215958082290416499391189 5442561517553681636704481)
                    ·
                      refine ⟨4081921138165261227528361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5442561517553681636704481 4081921138165261227528361)
                      ·
                        rfl

theorem cell23_7949513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 7, 2].length) (baseStart_7949513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7949513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7949513 prefixEnd_7949513 := by exact prefixLift 7949513
  have htrace : WordTrace (prefixWord ++ tailWord_7949513) baseStart_7949513 baseEnd_7949513 := by
    simpa [prefixWord, tailWord_7949513, baseEnd_7949513] using wordTrace_append hprefix tailTrace_7949513
  have hstable : (prefixWord ++ tailWord_7949513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7949513).length < 2 ^ (prefixWord ++ tailWord_7949513).sum := by decide
  have hdescent : baseEnd_7949513 < baseStart_7949513 := by decide
  rcases family_descends (prefixWord ++ tailWord_7949513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7949580 : List Nat := [2, 2, 1, 2, 2, 3, 1, 3, 2, 2, 3]
def baseStart_7949580 : Nat := 118140960795 + 7949580 * 2 ^ 59
def prefixEnd_7949580 : Nat := 4983230072969 + 3 ^ 40 * 7949580 * 2
def baseEnd_7949580 : Nat := 4081955541369112465390553

theorem tailTrace_7949580 : CollatzResearch.WordTrace tailWord_7949580 prefixEnd_7949580 4081955541369112465390553 := by
  unfold tailWord_7949580
  simp only [CollatzResearch.WordTrace]
  refine ⟨144972501270018407509335097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193296668360024543345780129 144972501270018407509335097)
  ·
    refine ⟨108729375952513805632001323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144972501270018407509335097 108729375952513805632001323)
    ·
      refine ⟨163094063928770708448001985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108729375952513805632001323 163094063928770708448001985)
      ·
        refine ⟨122320547946578031336001489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163094063928770708448001985 122320547946578031336001489)
        ·
          refine ⟨91740410959933523502001117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122320547946578031336001489 91740410959933523502001117)
          ·
            refine ⟨34402654109975071313250419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91740410959933523502001117 34402654109975071313250419)
            ·
              refine ⟨51603981164962606969875629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34402654109975071313250419 51603981164962606969875629)
              ·
                refine ⟨19351492936860977613703361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51603981164962606969875629 19351492936860977613703361)
                ·
                  refine ⟨14513619702645733210277521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19351492936860977613703361 14513619702645733210277521)
                  ·
                    refine ⟨10885214776984299907708141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14513619702645733210277521 10885214776984299907708141)
                    ·
                      refine ⟨4081955541369112465390553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10885214776984299907708141 4081955541369112465390553)
                      ·
                        rfl

theorem cell23_7949580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 3, 2, 2, 3].length) (baseStart_7949580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7949580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7949580 prefixEnd_7949580 := by exact prefixLift 7949580
  have htrace : WordTrace (prefixWord ++ tailWord_7949580) baseStart_7949580 baseEnd_7949580 := by
    simpa [prefixWord, tailWord_7949580, baseEnd_7949580] using wordTrace_append hprefix tailTrace_7949580
  have hstable : (prefixWord ++ tailWord_7949580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7949580).length < 2 ^ (prefixWord ++ tailWord_7949580).sum := by decide
  have hdescent : baseEnd_7949580 < baseStart_7949580 := by decide
  rcases family_descends (prefixWord ++ tailWord_7949580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7949597 : List Nat := [1, 4, 2, 3, 1, 1, 2, 2, 2, 2, 3]
def baseStart_7949597 : Nat := 118140960795 + 7949597 * 2 ^ 59
def prefixEnd_7949597 : Nat := 4983230072969 + 3 ^ 40 * 7949597 * 2
def baseEnd_7949597 : Nat := 4081964270540238898877975

theorem tailTrace_7949597 : CollatzResearch.WordTrace tailWord_7949597 prefixEnd_7949597 4081964270540238898877975 := by
  unfold tailWord_7949597
  simp only [CollatzResearch.WordTrace]
  refine ⟨289945622580975226922039045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193297081720650151281359363 289945622580975226922039045)
  ·
    refine ⟨54364804233932855047882321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 289945622580975226922039045 54364804233932855047882321)
    ·
      refine ⟨40773603175449641285911741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54364804233932855047882321 40773603175449641285911741)
      ·
        refine ⟨15290101190793615482216903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40773603175449641285911741 15290101190793615482216903)
        ·
          refine ⟨22935151786190423223325355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15290101190793615482216903 22935151786190423223325355)
          ·
            refine ⟨34402727679285634834988033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22935151786190423223325355 34402727679285634834988033)
            ·
              refine ⟨25802045759464226126241025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34402727679285634834988033 25802045759464226126241025)
              ·
                refine ⟨19351534319598169594680769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25802045759464226126241025 19351534319598169594680769)
                ·
                  refine ⟨14513650739698627196010577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19351534319598169594680769 14513650739698627196010577)
                  ·
                    refine ⟨10885238054773970397007933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14513650739698627196010577 10885238054773970397007933)
                    ·
                      refine ⟨4081964270540238898877975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10885238054773970397007933 4081964270540238898877975)
                      ·
                        rfl

theorem cell23_7949597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_7949597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7949597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7949597 prefixEnd_7949597 := by exact prefixLift 7949597
  have htrace : WordTrace (prefixWord ++ tailWord_7949597) baseStart_7949597 baseEnd_7949597 := by
    simpa [prefixWord, tailWord_7949597, baseEnd_7949597] using wordTrace_append hprefix tailTrace_7949597
  have hstable : (prefixWord ++ tailWord_7949597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7949597).length < 2 ^ (prefixWord ++ tailWord_7949597).sum := by decide
  have hdescent : baseEnd_7949597 < baseStart_7949597 := by decide
  rcases family_descends (prefixWord ++ tailWord_7949597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7949630 : List Nat := [4, 2, 1, 2, 1, 1, 1, 3, 3, 5]
def baseStart_7949630 : Nat := 118140960795 + 7949630 * 2 ^ 59
def prefixEnd_7949630 : Nat := 4983230072969 + 3 ^ 40 * 7949630 * 2
def baseEnd_7949630 : Nat := 1360660405133945756588441

theorem tailTrace_7949630 : CollatzResearch.WordTrace tailWord_7949630 prefixEnd_7949630 1360660405133945756588441 := by
  unfold tailWord_7949630
  simp only [CollatzResearch.WordTrace]
  refine ⟨36243353273731959194748793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193297884126570449038660229 36243353273731959194748793)
  ·
    refine ⟨27182514955298969396061595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36243353273731959194748793 27182514955298969396061595)
    ·
      refine ⟨40773772432948454094092393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27182514955298969396061595 40773772432948454094092393)
      ·
        refine ⟨30580329324711340570569295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40773772432948454094092393 30580329324711340570569295)
        ·
          refine ⟨45870493987067010855853943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30580329324711340570569295 45870493987067010855853943)
          ·
            refine ⟨68805740980600516283780915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45870493987067010855853943 68805740980600516283780915)
            ·
              refine ⟨103208611470900774425671373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68805740980600516283780915 103208611470900774425671373)
              ·
                refine ⟨38703229301587790409626765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103208611470900774425671373 38703229301587790409626765)
                ·
                  refine ⟨14513710988095421403610037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38703229301587790409626765 14513710988095421403610037)
                  ·
                    refine ⟨1360660405133945756588441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14513710988095421403610037 1360660405133945756588441)
                    ·
                      rfl

theorem cell23_7949630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 3, 3, 5].length) (baseStart_7949630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7949630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7949630 prefixEnd_7949630 := by exact prefixLift 7949630
  have htrace : WordTrace (prefixWord ++ tailWord_7949630) baseStart_7949630 baseEnd_7949630 := by
    simpa [prefixWord, tailWord_7949630, baseEnd_7949630] using wordTrace_append hprefix tailTrace_7949630
  have hstable : (prefixWord ++ tailWord_7949630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7949630).length < 2 ^ (prefixWord ++ tailWord_7949630).sum := by decide
  have hdescent : baseEnd_7949630 < baseStart_7949630 := by decide
  rcases family_descends (prefixWord ++ tailWord_7949630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7949644 : List Nat := [2, 2, 1, 3, 2, 2, 1, 5, 1, 1, 3]
def baseStart_7949644 : Nat := 118140960795 + 7949644 * 2 ^ 59
def prefixEnd_7949644 : Nat := 4983230072969 + 3 ^ 40 * 7949644 * 2
def baseEnd_7949644 : Nat := 4081988404131000214990259

theorem tailTrace_7949644 : CollatzResearch.WordTrace tailWord_7949644 prefixEnd_7949644 4081988404131000214990259 := by
  unfold tailWord_7949644
  simp only [CollatzResearch.WordTrace]
  refine ⟨144973668405902476974499993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193298224541203302632666657 144973668405902476974499993)
  ·
    refine ⟨108730251304426857730874995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144973668405902476974499993 108730251304426857730874995)
    ·
      refine ⟨163095376956640286596312493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108730251304426857730874995 163095376956640286596312493)
      ·
        refine ⟨61160766358740107473617185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163095376956640286596312493 61160766358740107473617185)
        ·
          refine ⟨45870574769055080605212889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61160766358740107473617185 45870574769055080605212889)
          ·
            refine ⟨34402931076791310453909667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45870574769055080605212889 34402931076791310453909667)
            ·
              refine ⟨51604396615186965680864501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34402931076791310453909667 51604396615186965680864501)
              ·
                refine ⟨4837912182673778032581047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51604396615186965680864501 4837912182673778032581047)
                ·
                  refine ⟨7256868274010667048871571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4837912182673778032581047 7256868274010667048871571)
                  ·
                    refine ⟨10885302411016000573307357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7256868274010667048871571 10885302411016000573307357)
                    ·
                      refine ⟨4081988404131000214990259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10885302411016000573307357 4081988404131000214990259)
                      ·
                        rfl

theorem cell23_7949644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 5, 1, 1, 3].length) (baseStart_7949644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7949644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7949644 prefixEnd_7949644 := by exact prefixLift 7949644
  have htrace : WordTrace (prefixWord ++ tailWord_7949644) baseStart_7949644 baseEnd_7949644 := by
    simpa [prefixWord, tailWord_7949644, baseEnd_7949644] using wordTrace_append hprefix tailTrace_7949644
  have hstable : (prefixWord ++ tailWord_7949644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7949644).length < 2 ^ (prefixWord ++ tailWord_7949644).sum := by decide
  have hdescent : baseEnd_7949644 < baseStart_7949644 := by decide
  rcases family_descends (prefixWord ++ tailWord_7949644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7949663 : List Nat := [1, 1, 2, 3, 1, 2, 1, 4, 1, 1, 6]
def baseStart_7949663 : Nat := 118140960795 + 7949663 * 2 ^ 59
def prefixEnd_7949663 : Nat := 4983230072969 + 3 ^ 40 * 7949663 * 2
def baseEnd_7949663 : Nat := 4081998160263435640652671

theorem tailTrace_7949663 : CollatzResearch.WordTrace tailWord_7949663 prefixEnd_7949663 4081998160263435640652671 := by
  unfold tailWord_7949663
  simp only [CollatzResearch.WordTrace]
  refine ⟨289948029798736120193941643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193298686532490746795961095 289948029798736120193941643)
  ·
    refine ⟨434922044698104180290912465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289948029798736120193941643 434922044698104180290912465)
    ·
      refine ⟨326191533523578135218184349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 434922044698104180290912465 326191533523578135218184349)
      ·
        refine ⟨122321825071341800706819131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 326191533523578135218184349 122321825071341800706819131)
        ·
          refine ⟨183482737607012701060228697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122321825071341800706819131 183482737607012701060228697)
          ·
            refine ⟨137612053205259525795171523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183482737607012701060228697 137612053205259525795171523)
            ·
              refine ⟨206418079807889288692757285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137612053205259525795171523 206418079807889288692757285)
              ·
                refine ⟨38703389963979241629891991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 206418079807889288692757285 38703389963979241629891991)
                ·
                  refine ⟨58055084945968862444837987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38703389963979241629891991 58055084945968862444837987)
                  ·
                    refine ⟨87082627418953293667256981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58055084945968862444837987 87082627418953293667256981)
                    ·
                      refine ⟨4081998160263435640652671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87082627418953293667256981 4081998160263435640652671)
                      ·
                        rfl

theorem cell23_7949663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4, 1, 1, 6].length) (baseStart_7949663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7949663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7949663 prefixEnd_7949663 := by exact prefixLift 7949663
  have htrace : WordTrace (prefixWord ++ tailWord_7949663) baseStart_7949663 baseEnd_7949663 := by
    simpa [prefixWord, tailWord_7949663, baseEnd_7949663] using wordTrace_append hprefix tailTrace_7949663
  have hstable : (prefixWord ++ tailWord_7949663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7949663).length < 2 ^ (prefixWord ++ tailWord_7949663).sum := by decide
  have hdescent : baseEnd_7949663 < baseStart_7949663 := by decide
  rcases family_descends (prefixWord ++ tailWord_7949663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7949677 : List Nat := [1, 5, 1, 1, 1, 5, 1, 1, 1, 6]
def baseStart_7949677 : Nat := 118140960795 + 7949677 * 2 ^ 59
def prefixEnd_7949677 : Nat := 4983230072969 + 3 ^ 40 * 7949677 * 2
def baseEnd_7949677 : Nat := 1360668449664199528625869

theorem tailTrace_7949677 : CollatzResearch.WordTrace tailWord_7949677 prefixEnd_7949677 1360668449664199528625869 := by
  unfold tailWord_7949677
  simp only [CollatzResearch.WordTrace]
  refine ⟨289948540420685400584951285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193299026947123600389967523 289948540420685400584951285)
  ·
    refine ⟨27182675664439256304839183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 289948540420685400584951285 27182675664439256304839183)
    ·
      refine ⟨40774013496658884457258775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27182675664439256304839183 40774013496658884457258775)
      ·
        refine ⟨61161020244988326685888163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40774013496658884457258775 61161020244988326685888163)
        ·
          refine ⟨91741530367482490028832245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61161020244988326685888163 91741530367482490028832245)
          ·
            refine ⟨8600768471951483440203023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91741530367482490028832245 8600768471951483440203023)
            ·
              refine ⟨12901152707927225160304535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8600768471951483440203023 12901152707927225160304535)
              ·
                refine ⟨19351729061890837740456803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12901152707927225160304535 19351729061890837740456803)
                ·
                  refine ⟨29027593592836256610685205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19351729061890837740456803 29027593592836256610685205)
                  ·
                    refine ⟨1360668449664199528625869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29027593592836256610685205 1360668449664199528625869)
                    ·
                      rfl

theorem cell23_7949677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 1, 1, 6].length) (baseStart_7949677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7949677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7949677 prefixEnd_7949677 := by exact prefixLift 7949677
  have htrace : WordTrace (prefixWord ++ tailWord_7949677) baseStart_7949677 baseEnd_7949677 := by
    simpa [prefixWord, tailWord_7949677, baseEnd_7949677] using wordTrace_append hprefix tailTrace_7949677
  have hstable : (prefixWord ++ tailWord_7949677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7949677).length < 2 ^ (prefixWord ++ tailWord_7949677).sum := by decide
  have hdescent : baseEnd_7949677 < baseStart_7949677 := by decide
  rcases family_descends (prefixWord ++ tailWord_7949677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7949687 : List Nat := [1, 1, 3, 1, 1, 2, 6, 2, 1, 2, 3]
def baseStart_7949687 : Nat := 118140960795 + 7949687 * 2 ^ 59
def prefixEnd_7949687 : Nat := 4983230072969 + 3 ^ 40 * 7949687 * 2
def baseEnd_7949687 : Nat := 4082010483799143546752561

theorem tailTrace_7949687 : CollatzResearch.WordTrace tailWord_7949687 prefixEnd_7949687 4082010483799143546752561 := by
  unfold tailWord_7949687
  simp only [CollatzResearch.WordTrace]
  refine ⟨289948905150649172292815315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193299270100432781528543543 289948905150649172292815315)
  ·
    refine ⟨434923357725973758439222973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289948905150649172292815315 434923357725973758439222973)
    ·
      refine ⟨163096259147240159414708615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 434923357725973758439222973 163096259147240159414708615)
      ·
        refine ⟨244644388720860239122062923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163096259147240159414708615 244644388720860239122062923)
        ·
          refine ⟨366966583081290358683094385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244644388720860239122062923 366966583081290358683094385)
          ·
            refine ⟨275224937310967769012320789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 366966583081290358683094385 275224937310967769012320789)
            ·
              refine ⟨12901168936451614172452537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 275224937310967769012320789 12901168936451614172452537)
              ·
                refine ⟨9675876702338710629339403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12901168936451614172452537 9675876702338710629339403)
                ·
                  refine ⟨14513815053508065944009105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9675876702338710629339403 14513815053508065944009105)
                  ·
                    refine ⟨10885361290131049458006829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14513815053508065944009105 10885361290131049458006829)
                    ·
                      refine ⟨4082010483799143546752561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10885361290131049458006829 4082010483799143546752561)
                      ·
                        rfl

theorem cell23_7949687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 2, 1, 2, 3].length) (baseStart_7949687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7949687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7949687 prefixEnd_7949687 := by exact prefixLift 7949687
  have htrace : WordTrace (prefixWord ++ tailWord_7949687) baseStart_7949687 baseEnd_7949687 := by
    simpa [prefixWord, tailWord_7949687, baseEnd_7949687] using wordTrace_append hprefix tailTrace_7949687
  have hstable : (prefixWord ++ tailWord_7949687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7949687).length < 2 ^ (prefixWord ++ tailWord_7949687).sum := by decide
  have hdescent : baseEnd_7949687 < baseStart_7949687 := by decide
  rcases family_descends (prefixWord ++ tailWord_7949687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7949701 : List Nat := [1, 3, 1, 1, 3, 1, 5, 3, 1, 2, 2]
def baseStart_7949701 : Nat := 118140960795 + 7949701 * 2 ^ 59
def prefixEnd_7949701 : Nat := 4983230072969 + 3 ^ 40 * 7949701 * 2
def baseEnd_7949701 : Nat := 4082017672528306491977497

theorem tailTrace_7949701 : CollatzResearch.WordTrace tailWord_7949701 prefixEnd_7949701 4082017672528306491977497 := by
  unfold tailWord_7949701
  simp only [CollatzResearch.WordTrace]
  refine ⟨289949415772598452683824957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193299610515065635122549971 289949415772598452683824957)
  ·
    refine ⟨108731030914724419756434359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289949415772598452683824957 108731030914724419756434359)
    ·
      refine ⟨163096546372086629634651539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108731030914724419756434359 163096546372086629634651539)
      ·
        refine ⟨244644819558129944451977309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163096546372086629634651539 244644819558129944451977309)
        ·
          refine ⟨91741807334298729169491491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 244644819558129944451977309 91741807334298729169491491)
          ·
            refine ⟨137612711001448093754237237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91741807334298729169491491 137612711001448093754237237)
            ·
              refine ⟨12901191656385758789459741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 137612711001448093754237237 12901191656385758789459741)
              ·
                refine ⟨4837946871144659546047403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12901191656385758789459741 4837946871144659546047403)
                ·
                  refine ⟨7256920306716989319071105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4837946871144659546047403 7256920306716989319071105)
                  ·
                    refine ⟨5442690230037741989303329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7256920306716989319071105 5442690230037741989303329)
                    ·
                      refine ⟨4082017672528306491977497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5442690230037741989303329 4082017672528306491977497)
                      ·
                        rfl

theorem cell23_7949701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 3, 1, 2, 2].length) (baseStart_7949701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7949701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7949701 prefixEnd_7949701 := by exact prefixLift 7949701
  have htrace : WordTrace (prefixWord ++ tailWord_7949701) baseStart_7949701 baseEnd_7949701 := by
    simpa [prefixWord, tailWord_7949701, baseEnd_7949701] using wordTrace_append hprefix tailTrace_7949701
  have hstable : (prefixWord ++ tailWord_7949701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7949701).length < 2 ^ (prefixWord ++ tailWord_7949701).sum := by decide
  have hdescent : baseEnd_7949701 < baseStart_7949701 := by decide
  rcases family_descends (prefixWord ++ tailWord_7949701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7949717 : List Nat := [1, 3, 2, 1, 1, 2, 4, 1, 4, 1, 3]
def baseStart_7949717 : Nat := 118140960795 + 7949717 * 2 ^ 59
def prefixEnd_7949717 : Nat := 4983230072969 + 3 ^ 40 * 7949717 * 2
def baseEnd_7949717 : Nat := 4082025888218778429377423

theorem tailTrace_7949717 : CollatzResearch.WordTrace tailWord_7949717 prefixEnd_7949717 4082025888218778429377423 := by
  unfold tailWord_7949717
  simp only [CollatzResearch.WordTrace]
  refine ⟨289949999340540487416407405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193299999560360324944271603 289949999340540487416407405)
  ·
    refine ⟨108731249752702682781152777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289949999340540487416407405 108731249752702682781152777)
    ·
      refine ⟨81548437314527012085864583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108731249752702682781152777 81548437314527012085864583)
      ·
        refine ⟨122322655971790518128796875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81548437314527012085864583 122322655971790518128796875)
        ·
          refine ⟨183483983957685777193195313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122322655971790518128796875 183483983957685777193195313)
          ·
            refine ⟨137612987968264332894896485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183483983957685777193195313 137612987968264332894896485)
            ·
              refine ⟨25802435244049562417793091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137612987968264332894896485 25802435244049562417793091)
              ·
                refine ⟨38703652866074343626689637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25802435244049562417793091 38703652866074343626689637)
                ·
                  refine ⟨7256934912388939430004307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38703652866074343626689637 7256934912388939430004307)
                  ·
                    refine ⟨10885402368583409145006461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7256934912388939430004307 10885402368583409145006461)
                    ·
                      refine ⟨4082025888218778429377423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10885402368583409145006461 4082025888218778429377423)
                      ·
                        rfl

theorem cell23_7949717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 1, 4, 1, 3].length) (baseStart_7949717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7949717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7949717 prefixEnd_7949717 := by exact prefixLift 7949717
  have htrace : WordTrace (prefixWord ++ tailWord_7949717) baseStart_7949717 baseEnd_7949717 := by
    simpa [prefixWord, tailWord_7949717, baseEnd_7949717] using wordTrace_append hprefix tailTrace_7949717
  have hstable : (prefixWord ++ tailWord_7949717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7949717).length < 2 ^ (prefixWord ++ tailWord_7949717).sum := by decide
  have hdescent : baseEnd_7949717 < baseStart_7949717 := by decide
  rcases family_descends (prefixWord ++ tailWord_7949717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7949760 : List Nat := [2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 5]
def baseStart_7949760 : Nat := 118140960795 + 7949760 * 2 ^ 59
def prefixEnd_7949760 : Nat := 4983230072969 + 3 ^ 40 * 7949760 * 2
def baseEnd_7949760 : Nat := 4082047967886921761139725

theorem tailTrace_7949760 : CollatzResearch.WordTrace tailWord_7949760 prefixEnd_7949760 4082047967886921761139725 := by
  unfold tailWord_7949760
  simp only [CollatzResearch.WordTrace]
  refine ⟨144975783839692352880111367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193301045119589803840148489 144975783839692352880111367)
  ·
    refine ⟨217463675759538529320167051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144975783839692352880111367 217463675759538529320167051)
    ·
      refine ⟨326195513639307793980250577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217463675759538529320167051 326195513639307793980250577)
      ·
        refine ⟨244646635229480845485187933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326195513639307793980250577 244646635229480845485187933)
        ·
          refine ⟨91742488211055317056945475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 244646635229480845485187933 91742488211055317056945475)
          ·
            refine ⟨137613732316582975585418213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91742488211055317056945475 137613732316582975585418213)
            ·
              refine ⟨25802574809359307922265915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137613732316582975585418213 25802574809359307922265915)
              ·
                refine ⟨38703862214038961883398873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25802574809359307922265915 38703862214038961883398873)
                ·
                  refine ⟨29027896660529221412549155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38703862214038961883398873 29027896660529221412549155)
                  ·
                    refine ⟨43541844990793832118823733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29027896660529221412549155 43541844990793832118823733)
                    ·
                      refine ⟨4082047967886921761139725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43541844990793832118823733 4082047967886921761139725)
                      ·
                        rfl

theorem cell23_7949760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 5].length) (baseStart_7949760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7949760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7949760 prefixEnd_7949760 := by exact prefixLift 7949760
  have htrace : WordTrace (prefixWord ++ tailWord_7949760) baseStart_7949760 baseEnd_7949760 := by
    simpa [prefixWord, tailWord_7949760, baseEnd_7949760] using wordTrace_append hprefix tailTrace_7949760
  have hstable : (prefixWord ++ tailWord_7949760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7949760).length < 2 ^ (prefixWord ++ tailWord_7949760).sum := by decide
  have hdescent : baseEnd_7949760 < baseStart_7949760 := by decide
  rcases family_descends (prefixWord ++ tailWord_7949760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7949774 : List Nat := [4, 1, 1, 1, 2, 1, 2, 3, 4, 2, 2]
def baseStart_7949774 : Nat := 118140960795 + 7949774 * 2 ^ 59
def prefixEnd_7949774 : Nat := 4983230072969 + 3 ^ 40 * 7949774 * 2
def baseEnd_7949774 : Nat := 4082055156616084706364661

theorem tailTrace_7949774 : CollatzResearch.WordTrace tailWord_7949774 prefixEnd_7949774 4082055156616084706364661 := by
  unfold tailWord_7949774
  simp only [CollatzResearch.WordTrace]
  refine ⟨36244009787666748268904047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193301385534222657434154917 36244009787666748268904047)
  ·
    refine ⟨54366014681500122403356071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36244009787666748268904047 54366014681500122403356071)
    ·
      refine ⟨81549022022250183605034107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54366014681500122403356071 81549022022250183605034107)
      ·
        refine ⟨122323533033375275407551161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81549022022250183605034107 122323533033375275407551161)
        ·
          refine ⟨91742649775031456555663371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122323533033375275407551161 91742649775031456555663371)
          ·
            refine ⟨137613974662547184833495057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91742649775031456555663371 137613974662547184833495057)
            ·
              refine ⟨103210480996910388625121293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137613974662547184833495057 103210480996910388625121293)
              ·
                refine ⟨38703930373841395734420485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103210480996910388625121293 38703930373841395734420485)
                ·
                  refine ⟨7256986945095261700203841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38703930373841395734420485 7256986945095261700203841)
                  ·
                    refine ⟨5442740208821446275152881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7256986945095261700203841 5442740208821446275152881)
                    ·
                      refine ⟨4082055156616084706364661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5442740208821446275152881 4082055156616084706364661)
                      ·
                        rfl

theorem cell23_7949774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 3, 4, 2, 2].length) (baseStart_7949774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7949774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7949774 prefixEnd_7949774 := by exact prefixLift 7949774
  have htrace : WordTrace (prefixWord ++ tailWord_7949774) baseStart_7949774 baseEnd_7949774 := by
    simpa [prefixWord, tailWord_7949774, baseEnd_7949774] using wordTrace_append hprefix tailTrace_7949774
  have hstable : (prefixWord ++ tailWord_7949774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7949774).length < 2 ^ (prefixWord ++ tailWord_7949774).sum := by decide
  have hdescent : baseEnd_7949774 < baseStart_7949774 := by decide
  rcases family_descends (prefixWord ++ tailWord_7949774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7949797 : List Nat := [1, 3, 1, 5, 1, 2, 1, 2, 7]
def baseStart_7949797 : Nat := 118140960795 + 7949797 * 2 ^ 59
def prefixEnd_7949797 : Nat := 4983230072969 + 3 ^ 40 * 7949797 * 2
def baseEnd_7949797 : Nat := 453562996296793124041895

theorem tailTrace_7949797 : CollatzResearch.WordTrace tailWord_7949797 prefixEnd_7949797 453562996296793124041895 := by
  unfold tailWord_7949797
  simp only [CollatzResearch.WordTrace]
  refine ⟨289952917180250661079319645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193301944786833774052879763 289952917180250661079319645)
  ·
    refine ⟨108732343942593997904744867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289952917180250661079319645 108732343942593997904744867)
    ·
      refine ⟨163098515913890996857117301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108732343942593997904744867 163098515913890996857117301)
      ·
        refine ⟨15290485866927280955354747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 163098515913890996857117301 15290485866927280955354747)
        ·
          refine ⟨22935728800390921433032121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15290485866927280955354747 22935728800390921433032121)
          ·
            refine ⟨17201796600293191074774091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22935728800390921433032121 17201796600293191074774091)
            ·
              refine ⟨25802694900439786612161137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17201796600293191074774091 25802694900439786612161137)
              ·
                refine ⟨19352021175329839959120853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25802694900439786612161137 19352021175329839959120853)
                ·
                  refine ⟨453562996296793124041895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19352021175329839959120853 453562996296793124041895)
                  ·
                    rfl

theorem cell23_7949797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 2, 7].length) (baseStart_7949797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7949797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7949797 prefixEnd_7949797 := by exact prefixLift 7949797
  have htrace : WordTrace (prefixWord ++ tailWord_7949797) baseStart_7949797 baseEnd_7949797 := by
    simpa [prefixWord, tailWord_7949797, baseEnd_7949797] using wordTrace_append hprefix tailTrace_7949797
  have hstable : (prefixWord ++ tailWord_7949797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7949797).length < 2 ^ (prefixWord ++ tailWord_7949797).sum := by decide
  have hdescent : baseEnd_7949797 < baseStart_7949797 := by decide
  rcases family_descends (prefixWord ++ tailWord_7949797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7949814 : List Nat := [5, 1, 1, 1, 2, 2, 1, 5, 5]
def baseStart_7949814 : Nat := 118140960795 + 7949814 * 2 ^ 59
def prefixEnd_7949814 : Nat := 4983230072969 + 3 ^ 40 * 7949814 * 2
def baseEnd_7949814 : Nat := 453563966204696061096053

theorem tailTrace_7949814 : CollatzResearch.WordTrace tailWord_7949814 prefixEnd_7949814 453563966204696061096053 := by
  unfold tailWord_7949814
  simp only [CollatzResearch.WordTrace]
  refine ⟨18122096076324317061418031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 193302358147459381988458997 18122096076324317061418031)
  ·
    refine ⟨27183144114486475592127047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18122096076324317061418031 27183144114486475592127047)
    ·
      refine ⟨40774716171729713388190571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27183144114486475592127047 40774716171729713388190571)
      ·
        refine ⟨61162074257594570082285857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40774716171729713388190571 61162074257594570082285857)
        ·
          refine ⟨45871555693195927561714393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61162074257594570082285857 45871555693195927561714393)
          ·
            refine ⟨34403666769896945671285795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45871555693195927561714393 34403666769896945671285795)
            ·
              refine ⟨51605500154845418506928693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34403666769896945671285795 51605500154845418506928693)
              ·
                refine ⟨4838015639516757985024565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51605500154845418506928693 4838015639516757985024565)
                ·
                  refine ⟨453563966204696061096053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4838015639516757985024565 453563966204696061096053)
                  ·
                    rfl

theorem cell23_7949814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 5, 5].length) (baseStart_7949814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7949814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7949814 prefixEnd_7949814 := by exact prefixLift 7949814
  have htrace : WordTrace (prefixWord ++ tailWord_7949814) baseStart_7949814 baseEnd_7949814 := by
    simpa [prefixWord, tailWord_7949814, baseEnd_7949814] using wordTrace_append hprefix tailTrace_7949814
  have hstable : (prefixWord ++ tailWord_7949814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7949814).length < 2 ^ (prefixWord ++ tailWord_7949814).sum := by decide
  have hdescent : baseEnd_7949814 < baseStart_7949814 := by decide
  rcases family_descends (prefixWord ++ tailWord_7949814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7949820 : List Nat := [2, 2, 2, 1, 2, 1, 2, 1, 3, 2, 5]
def baseStart_7949820 : Nat := 118140960795 + 7949820 * 2 ^ 59
def prefixEnd_7949820 : Nat := 4983230072969 + 3 ^ 40 * 7949820 * 2
def baseEnd_7949820 : Nat := 4082078776726191526389449

theorem tailTrace_7949820 : CollatzResearch.WordTrace tailWord_7949820 prefixEnd_7949820 4082078776726191526389449 := by
  unfold tailWord_7949820
  simp only [CollatzResearch.WordTrace]
  refine ⟨144976878029583668003703457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193302504039444890671604609 144976878029583668003703457)
  ·
    refine ⟨108732658522187751002777593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144976878029583668003703457 108732658522187751002777593)
    ·
      refine ⟨81549493891640813252083195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108732658522187751002777593 81549493891640813252083195)
      ·
        refine ⟨122324240837461219878124793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81549493891640813252083195 122324240837461219878124793)
        ·
          refine ⟨91743180628095914908593595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122324240837461219878124793 91743180628095914908593595)
          ·
            refine ⟨137614770942143872362890393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91743180628095914908593595 137614770942143872362890393)
            ·
              refine ⟨103211078206607904272167795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137614770942143872362890393 103211078206607904272167795)
              ·
                refine ⟨154816617309911856408251693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103211078206607904272167795 154816617309911856408251693)
                ·
                  refine ⟨58056231491216946153094385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 154816617309911856408251693 58056231491216946153094385)
                  ·
                    refine ⟨43542173618412709614820789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58056231491216946153094385 43542173618412709614820789)
                    ·
                      refine ⟨4082078776726191526389449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43542173618412709614820789 4082078776726191526389449)
                      ·
                        rfl

theorem cell23_7949820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 3, 2, 5].length) (baseStart_7949820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7949820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7949820 prefixEnd_7949820 := by exact prefixLift 7949820
  have htrace : WordTrace (prefixWord ++ tailWord_7949820) baseStart_7949820 baseEnd_7949820 := by
    simpa [prefixWord, tailWord_7949820, baseEnd_7949820] using wordTrace_append hprefix tailTrace_7949820
  have hstable : (prefixWord ++ tailWord_7949820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7949820).length < 2 ^ (prefixWord ++ tailWord_7949820).sum := by decide
  have hdescent : baseEnd_7949820 < baseStart_7949820 := by decide
  rcases family_descends (prefixWord ++ tailWord_7949820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7949825 : List Nat := [1, 2, 4, 1, 5, 1, 1, 2, 2, 2, 2]
def baseStart_7949825 : Nat := 118140960795 + 7949825 * 2 ^ 59
def prefixEnd_7949825 : Nat := 4983230072969 + 3 ^ 40 * 7949825 * 2
def baseEnd_7949825 : Nat := 4082081344129464006826927

theorem tailTrace_7949825 : CollatzResearch.WordTrace tailWord_7949825 prefixEnd_7949825 4082081344129464006826927 := by
  unfold tailWord_7949825
  simp only [CollatzResearch.WordTrace]
  refine ⟨289953938424149221861338929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193302625616099481240892619 289953938424149221861338929)
  ·
    refine ⟨217465453818111916396004197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289953938424149221861338929 217465453818111916396004197)
    ·
      refine ⟨40774772590895984324250787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 217465453818111916396004197 40774772590895984324250787)
      ·
        refine ⟨61162158886343976486376181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40774772590895984324250787 61162158886343976486376181)
        ·
          refine ⟨5733952395594747795597767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61162158886343976486376181 5733952395594747795597767)
          ·
            refine ⟨8600928593392121693396651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5733952395594747795597767 8600928593392121693396651)
            ·
              refine ⟨12901392890088182540094977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8600928593392121693396651 12901392890088182540094977)
              ·
                refine ⟨9676044667566136905071233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12901392890088182540094977 9676044667566136905071233)
                ·
                  refine ⟨7257033500674602678803425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9676044667566136905071233 7257033500674602678803425)
                  ·
                    refine ⟨5442775125505952009102569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7257033500674602678803425 5442775125505952009102569)
                    ·
                      refine ⟨4082081344129464006826927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5442775125505952009102569 4082081344129464006826927)
                      ·
                        rfl

theorem cell23_7949825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 2, 2, 2, 2].length) (baseStart_7949825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7949825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7949825 prefixEnd_7949825 := by exact prefixLift 7949825
  have htrace : WordTrace (prefixWord ++ tailWord_7949825) baseStart_7949825 baseEnd_7949825 := by
    simpa [prefixWord, tailWord_7949825, baseEnd_7949825] using wordTrace_append hprefix tailTrace_7949825
  have hstable : (prefixWord ++ tailWord_7949825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7949825).length < 2 ^ (prefixWord ++ tailWord_7949825).sum := by decide
  have hdescent : baseEnd_7949825 < baseStart_7949825 := by decide
  rcases family_descends (prefixWord ++ tailWord_7949825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7949914 : List Nat := [3, 1, 1, 2, 1, 1, 1, 6, 3, 1, 3]
def baseStart_7949914 : Nat := 118140960795 + 7949914 * 2 ^ 59
def prefixEnd_7949914 : Nat := 4983230072969 + 3 ^ 40 * 7949914 * 2
def baseEnd_7949914 : Nat := 4082127043907714158614017

theorem tailTrace_7949914 : CollatzResearch.WordTrace tailWord_7949914 prefixEnd_7949914 4082127043907714158614017 := by
  unfold tailWord_7949914
  simp only [CollatzResearch.WordTrace]
  refine ⟨72489296130206697515332199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193304789680551193374219197 72489296130206697515332199)
  ·
    refine ⟨108733944195310046272998299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72489296130206697515332199 108733944195310046272998299)
    ·
      refine ⟨163100916292965069409497449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108733944195310046272998299 163100916292965069409497449)
      ·
        refine ⟨122325687219723802057123087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163100916292965069409497449 122325687219723802057123087)
        ·
          refine ⟨183488530829585703085684631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122325687219723802057123087 183488530829585703085684631)
          ·
            refine ⟨275232796244378554628526947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183488530829585703085684631 275232796244378554628526947)
            ·
              refine ⟨412849194366567831942790421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275232796244378554628526947 412849194366567831942790421)
              ·
                refine ⟨19352305985932867122318301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 412849194366567831942790421 19352305985932867122318301)
                ·
                  refine ⟨7257114744724825170869363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19352305985932867122318301 7257114744724825170869363)
                  ·
                    refine ⟨10885672117087237756304045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7257114744724825170869363 10885672117087237756304045)
                    ·
                      refine ⟨4082127043907714158614017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10885672117087237756304045 4082127043907714158614017)
                      ·
                        rfl

theorem cell23_7949914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 6, 3, 1, 3].length) (baseStart_7949914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7949914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7949914 prefixEnd_7949914 := by exact prefixLift 7949914
  have htrace : WordTrace (prefixWord ++ tailWord_7949914) baseStart_7949914 baseEnd_7949914 := by
    simpa [prefixWord, tailWord_7949914, baseEnd_7949914] using wordTrace_append hprefix tailTrace_7949914
  have hstable : (prefixWord ++ tailWord_7949914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7949914).length < 2 ^ (prefixWord ++ tailWord_7949914).sum := by decide
  have hdescent : baseEnd_7949914 < baseStart_7949914 := by decide
  rcases family_descends (prefixWord ++ tailWord_7949914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7949957 : List Nat := [1, 3, 1, 1, 4, 1, 2, 1, 3, 1, 5]
def baseStart_7949957 : Nat := 118140960795 + 7949957 * 2 ^ 59
def prefixEnd_7949957 : Nat := 4983230072969 + 3 ^ 40 * 7949957 * 2
def baseEnd_7949957 : Nat := 4082149123575857490376319

theorem tailTrace_7949957 : CollatzResearch.WordTrace tailWord_7949957 prefixEnd_7949957 4082149123575857490376319 := by
  unfold tailWord_7949957
  simp only [CollatzResearch.WordTrace]
  refine ⟨289958752859671008405144125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193305835239780672270096083 289958752859671008405144125)
  ·
    refine ⟨108734532322376628151929047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289958752859671008405144125 108734532322376628151929047)
    ·
      refine ⟨163101798483564942227893571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108734532322376628151929047 163101798483564942227893571)
      ·
        refine ⟨244652697725347413341840357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163101798483564942227893571 244652697725347413341840357)
        ·
          refine ⟨45872380823502640001595067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 244652697725347413341840357 45872380823502640001595067)
          ·
            refine ⟨68808571235253960002392601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45872380823502640001595067 68808571235253960002392601)
            ·
              refine ⟨51606428426440470001794451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68808571235253960002392601 51606428426440470001794451)
              ·
                refine ⟨77409642639660705002691677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51606428426440470001794451 77409642639660705002691677)
                ·
                  refine ⟨29028615989872764376009379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77409642639660705002691677 29028615989872764376009379)
                  ·
                    refine ⟨43542923984809146564014069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29028615989872764376009379 43542923984809146564014069)
                    ·
                      refine ⟨4082149123575857490376319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43542923984809146564014069 4082149123575857490376319)
                      ·
                        rfl

theorem cell23_7949957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 3, 1, 5].length) (baseStart_7949957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7949957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7949957 prefixEnd_7949957 := by exact prefixLift 7949957
  have htrace : WordTrace (prefixWord ++ tailWord_7949957) baseStart_7949957 baseEnd_7949957 := by
    simpa [prefixWord, tailWord_7949957, baseEnd_7949957] using wordTrace_append hprefix tailTrace_7949957
  have hstable : (prefixWord ++ tailWord_7949957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7949957).length < 2 ^ (prefixWord ++ tailWord_7949957).sum := by decide
  have hdescent : baseEnd_7949957 < baseStart_7949957 := by decide
  rcases family_descends (prefixWord ++ tailWord_7949957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7949964 : List Nat := [2, 2, 1, 2, 1, 1, 3, 5, 2, 4]
def baseStart_7949964 : Nat := 118140960795 + 7949964 * 2 ^ 59
def prefixEnd_7949964 : Nat := 4983230072969 + 3 ^ 40 * 7949964 * 2
def baseEnd_7949964 : Nat := 1360717572646812987662929

theorem tailTrace_7949964 : CollatzResearch.WordTrace tailWord_7949964 prefixEnd_7949964 1360717572646812987662929 := by
  unfold tailWord_7949964
  simp only [CollatzResearch.WordTrace]
  refine ⟨144979504085322824300324473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193306005447097099067099297 144979504085322824300324473)
  ·
    refine ⟨108734628063992118225243355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144979504085322824300324473 108734628063992118225243355)
    ·
      refine ⟨163101942095988177337865033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108734628063992118225243355 163101942095988177337865033)
      ·
        refine ⟨122326456571991133003398775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163101942095988177337865033 122326456571991133003398775)
        ·
          refine ⟨183489684857986699505098163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122326456571991133003398775 183489684857986699505098163)
          ·
            refine ⟨275234527286980049257647245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183489684857986699505098163 275234527286980049257647245)
            ·
              refine ⟨103212947732617518471617717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 275234527286980049257647245 103212947732617518471617717)
              ·
                refine ⟨9676213849932892356714161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 103212947732617518471617717 9676213849932892356714161)
                ·
                  refine ⟨7257160387449669267535621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9676213849932892356714161 7257160387449669267535621)
                  ·
                    refine ⟨1360717572646812987662929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7257160387449669267535621 1360717572646812987662929)
                    ·
                      rfl

theorem cell23_7949964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 5, 2, 4].length) (baseStart_7949964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7949964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7949964 prefixEnd_7949964 := by exact prefixLift 7949964
  have htrace : WordTrace (prefixWord ++ tailWord_7949964) baseStart_7949964 baseEnd_7949964 := by
    simpa [prefixWord, tailWord_7949964, baseEnd_7949964] using wordTrace_append hprefix tailTrace_7949964
  have hstable : (prefixWord ++ tailWord_7949964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7949964).length < 2 ^ (prefixWord ++ tailWord_7949964).sum := by decide
  have hdescent : baseEnd_7949964 < baseStart_7949964 := by decide
  rcases family_descends (prefixWord ++ tailWord_7949964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7949984 : List Nat := [2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 4]
def baseStart_7949984 : Nat := 118140960795 + 7949984 * 2 ^ 59
def prefixEnd_7949984 : Nat := 4983230072969 + 3 ^ 40 * 7949984 * 2
def baseEnd_7949984 : Nat := 4082162987553528884738695

theorem tailTrace_7949984 : CollatzResearch.WordTrace tailWord_7949984 prefixEnd_7949984 4082162987553528884738695 := by
  unfold tailWord_7949984
  simp only [CollatzResearch.WordTrace]
  refine ⟨144979868815286596008188503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193306491753715461344251337 144979868815286596008188503)
  ·
    refine ⟨217469803222929894012282755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144979868815286596008188503 217469803222929894012282755)
    ·
      refine ⟨326204704834394841018424133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217469803222929894012282755 326204704834394841018424133)
      ·
        refine ⟨61163382156449032690954525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 326204704834394841018424133 61163382156449032690954525)
        ·
          refine ⟨22936268308668387259107947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61163382156449032690954525 22936268308668387259107947)
          ·
            refine ⟨34404402463002580888661921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22936268308668387259107947 34404402463002580888661921)
            ·
              refine ⟨25803301847251935666496441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34404402463002580888661921 25803301847251935666496441)
              ·
                refine ⟨19352476385438951749872331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25803301847251935666496441 19352476385438951749872331)
                ·
                  refine ⟨29028714578158427624808497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19352476385438951749872331 29028714578158427624808497)
                  ·
                    refine ⟨21771535933618820718606373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29028714578158427624808497 21771535933618820718606373)
                    ·
                      refine ⟨4082162987553528884738695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21771535933618820718606373 4082162987553528884738695)
                      ·
                        rfl

theorem cell23_7949984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_7949984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7949984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7949984 prefixEnd_7949984 := by exact prefixLift 7949984
  have htrace : WordTrace (prefixWord ++ tailWord_7949984) baseStart_7949984 baseEnd_7949984 := by
    simpa [prefixWord, tailWord_7949984, baseEnd_7949984] using wordTrace_append hprefix tailTrace_7949984
  have hstable : (prefixWord ++ tailWord_7949984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7949984).length < 2 ^ (prefixWord ++ tailWord_7949984).sum := by decide
  have hdescent : baseEnd_7949984 < baseStart_7949984 := by decide
  rcases family_descends (prefixWord ++ tailWord_7949984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7949988 : List Nat := [2, 3, 1, 2, 2, 4, 2, 1, 1, 1, 4]
def baseStart_7949988 : Nat := 118140960795 + 7949988 * 2 ^ 59
def prefixEnd_7949988 : Nat := 4983230072969 + 3 ^ 40 * 7949988 * 2
def baseEnd_7949988 : Nat := 4082165041476146869088677

theorem tailTrace_7949988 : CollatzResearch.WordTrace tailWord_7949988 prefixEnd_7949988 4082165041476146869088677 := by
  unfold tailWord_7949988
  simp only [CollatzResearch.WordTrace]
  refine ⟨144979941761279350349761309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193306589015039133799681745 144979941761279350349761309)
  ·
    refine ⟨54367478160479756381160491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144979941761279350349761309 54367478160479756381160491)
    ·
      refine ⟨81551217240719634571740737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54367478160479756381160491 81551217240719634571740737)
      ·
        refine ⟨61163412930539725928805553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81551217240719634571740737 61163412930539725928805553)
        ·
          refine ⟨45872559697904794446604165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61163412930539725928805553 45872559697904794446604165)
          ·
            refine ⟨8601104943357148958738281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45872559697904794446604165 8601104943357148958738281)
            ·
              refine ⟨6450828707517861719053711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8601104943357148958738281 6450828707517861719053711)
              ·
                refine ⟨9676243061276792578580567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6450828707517861719053711 9676243061276792578580567)
                ·
                  refine ⟨14514364591915188867870851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9676243061276792578580567 14514364591915188867870851)
                  ·
                    refine ⟨21771546887872783301806277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14514364591915188867870851 21771546887872783301806277)
                    ·
                      refine ⟨4082165041476146869088677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21771546887872783301806277 4082165041476146869088677)
                      ·
                        rfl

theorem cell23_7949988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 2, 1, 1, 1, 4].length) (baseStart_7949988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7949988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7949988 prefixEnd_7949988 := by exact prefixLift 7949988
  have htrace : WordTrace (prefixWord ++ tailWord_7949988) baseStart_7949988 baseEnd_7949988 := by
    simpa [prefixWord, tailWord_7949988, baseEnd_7949988] using wordTrace_append hprefix tailTrace_7949988
  have hstable : (prefixWord ++ tailWord_7949988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7949988).length < 2 ^ (prefixWord ++ tailWord_7949988).sum := by decide
  have hdescent : baseEnd_7949988 < baseStart_7949988 := by decide
  rcases family_descends (prefixWord ++ tailWord_7949988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7949998 : List Nat := [4, 1, 4, 1, 2, 1, 1, 1, 4, 4]
def baseStart_7949998 : Nat := 118140960795 + 7949998 * 2 ^ 59
def prefixEnd_7949998 : Nat := 4983230072969 + 3 ^ 40 * 7949998 * 2
def baseEnd_7949998 : Nat := 1360723392094230609987877

theorem tailTrace_7949998 : CollatzResearch.WordTrace tailWord_7949998 prefixEnd_7949998 1360723392094230609987877 := by
  unfold tailWord_7949998
  simp only [CollatzResearch.WordTrace]
  refine ⟨36245031031565309050923331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193306832168348314938257765 36245031031565309050923331)
  ·
    refine ⟨54367546547347963576384997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36245031031565309050923331 54367546547347963576384997)
    ·
      refine ⟨10193914977627743170572187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54367546547347963576384997 10193914977627743170572187)
      ·
        refine ⟨15290872466441614755858281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10193914977627743170572187 15290872466441614755858281)
        ·
          refine ⟨11468154349831211066893711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15290872466441614755858281 11468154349831211066893711)
          ·
            refine ⟨17202231524746816600340567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11468154349831211066893711 17202231524746816600340567)
            ·
              refine ⟨25803347287120224900510851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17202231524746816600340567 25803347287120224900510851)
              ·
                refine ⟨38705020930680337350766277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25803347287120224900510851 38705020930680337350766277)
                ·
                  refine ⟨7257191424502563253268677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38705020930680337350766277 7257191424502563253268677)
                  ·
                    refine ⟨1360723392094230609987877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7257191424502563253268677 1360723392094230609987877)
                    ·
                      rfl

theorem cell23_7949998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_7949998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7949998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7949998 prefixEnd_7949998 := by exact prefixLift 7949998
  have htrace : WordTrace (prefixWord ++ tailWord_7949998) baseStart_7949998 baseEnd_7949998 := by
    simpa [prefixWord, tailWord_7949998, baseEnd_7949998] using wordTrace_append hprefix tailTrace_7949998
  have hstable : (prefixWord ++ tailWord_7949998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7949998).length < 2 ^ (prefixWord ++ tailWord_7949998).sum := by decide
  have hdescent : baseEnd_7949998 < baseStart_7949998 := by decide
  rcases family_descends (prefixWord ++ tailWord_7949998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7950005 : List Nat := [1, 3, 3, 3, 2, 1, 2, 1, 3, 2, 2]
def baseStart_7950005 : Nat := 118140960795 + 7950005 * 2 ^ 59
def prefixEnd_7950005 : Nat := 4983230072969 + 3 ^ 40 * 7950005 * 2
def baseEnd_7950005 : Nat := 4082173770647273302576099

theorem tailTrace_7950005 : CollatzResearch.WordTrace tailWord_7950005 prefixEnd_7950005 4082173770647273302576099 := by
  unfold tailWord_7950005
  simp only [CollatzResearch.WordTrace]
  refine ⟨289960503563497112602891469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193307002375664741735260979 289960503563497112602891469)
  ·
    refine ⟨108735188836311417226084301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289960503563497112602891469 108735188836311417226084301)
    ·
      refine ⟨40775695813616781459781613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108735188836311417226084301 40775695813616781459781613)
      ·
        refine ⟨15290885930106293047418105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40775695813616781459781613 15290885930106293047418105)
        ·
          refine ⟨11468164447579719785563579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15290885930106293047418105 11468164447579719785563579)
          ·
            refine ⟨17202246671369579678345369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11468164447579719785563579 17202246671369579678345369)
            ·
              refine ⟨12901685003527184758759027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17202246671369579678345369 12901685003527184758759027)
              ·
                refine ⟨19352527505290777138138541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12901685003527184758759027 19352527505290777138138541)
                ·
                  refine ⟨7257197814484041426801953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19352527505290777138138541 7257197814484041426801953)
                  ·
                    refine ⟨5442898360863031070101465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7257197814484041426801953 5442898360863031070101465)
                    ·
                      refine ⟨4082173770647273302576099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5442898360863031070101465 4082173770647273302576099)
                      ·
                        rfl

theorem cell23_7950005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_7950005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7950005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7950005 prefixEnd_7950005 := by exact prefixLift 7950005
  have htrace : WordTrace (prefixWord ++ tailWord_7950005) baseStart_7950005 baseEnd_7950005 := by
    simpa [prefixWord, tailWord_7950005, baseEnd_7950005] using wordTrace_append hprefix tailTrace_7950005
  have hstable : (prefixWord ++ tailWord_7950005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7950005).length < 2 ^ (prefixWord ++ tailWord_7950005).sum := by decide
  have hdescent : baseEnd_7950005 < baseStart_7950005 := by decide
  rcases family_descends (prefixWord ++ tailWord_7950005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7950022 : List Nat := [6, 1, 2, 1, 1, 1, 2, 2, 3, 2, 2]
def baseStart_7950022 : Nat := 118140960795 + 7950022 * 2 ^ 59
def prefixEnd_7950022 : Nat := 4983230072969 + 3 ^ 40 * 7950022 * 2
def baseEnd_7950022 : Nat := 4082182499818399736063521

theorem tailTrace_7950022 : CollatzResearch.WordTrace tailWord_7950022 prefixEnd_7950022 4082182499818399736063521 := by
  unfold tailWord_7950022
  simp only [CollatzResearch.WordTrace]
  refine ⟨9061285112638610140820635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 193307415736290349670840213 9061285112638610140820635)
  ·
    refine ⟨13591927668957915211230953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9061285112638610140820635 13591927668957915211230953)
    ·
      refine ⟨10193945751718436408423215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13591927668957915211230953 10193945751718436408423215)
      ·
        refine ⟨15290918627577654612634823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10193945751718436408423215 15290918627577654612634823)
        ·
          refine ⟨22936377941366481918952235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15290918627577654612634823 22936377941366481918952235)
          ·
            refine ⟨34404566912049722878428353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22936377941366481918952235 34404566912049722878428353)
            ·
              refine ⟨25803425184037292158821265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34404566912049722878428353 25803425184037292158821265)
              ·
                refine ⟨19352568888027969119115949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25803425184037292158821265 19352568888027969119115949)
                ·
                  refine ⟨7257213333010488419668481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19352568888027969119115949 7257213333010488419668481)
                  ·
                    refine ⟨5442909999757866314751361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7257213333010488419668481 5442909999757866314751361)
                    ·
                      refine ⟨4082182499818399736063521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5442909999757866314751361 4082182499818399736063521)
                      ·
                        rfl

theorem cell23_7950022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_7950022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7950022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7950022 prefixEnd_7950022 := by exact prefixLift 7950022
  have htrace : WordTrace (prefixWord ++ tailWord_7950022) baseStart_7950022 baseEnd_7950022 := by
    simpa [prefixWord, tailWord_7950022, baseEnd_7950022] using wordTrace_append hprefix tailTrace_7950022
  have hstable : (prefixWord ++ tailWord_7950022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7950022).length < 2 ^ (prefixWord ++ tailWord_7950022).sum := by decide
  have hdescent : baseEnd_7950022 < baseStart_7950022 := by decide
  rcases family_descends (prefixWord ++ tailWord_7950022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7950027 : List Nat := [1, 1, 1, 1, 3, 2, 1, 4, 2, 3, 4]
def baseStart_7950027 : Nat := 118140960795 + 7950027 * 2 ^ 59
def prefixEnd_7950027 : Nat := 4983230072969 + 3 ^ 40 * 7950027 * 2
def baseEnd_7950027 : Nat := 4082185067221672216500997

theorem tailTrace_7950027 : CollatzResearch.WordTrace tailWord_7950027 prefixEnd_7950027 4082185067221672216500997 := by
  unfold tailWord_7950027
  simp only [CollatzResearch.WordTrace]
  refine ⟨289961305969417410360192335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193307537312944940240128223 289961305969417410360192335)
  ·
    refine ⟨434941958954126115540288503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289961305969417410360192335 434941958954126115540288503)
    ·
      refine ⟨652412938431189173310432755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434941958954126115540288503 652412938431189173310432755)
      ·
        refine ⟨978619407646783759965649133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 652412938431189173310432755 978619407646783759965649133)
        ·
          refine ⟨366982277867543909987118425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 978619407646783759965649133 366982277867543909987118425)
          ·
            refine ⟨275236708400657932490338819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 366982277867543909987118425 275236708400657932490338819)
            ·
              refine ⟨412855062600986898735508229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275236708400657932490338819 412855062600986898735508229)
              ·
                refine ⟨77410324237685043512907793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 412855062600986898735508229 77410324237685043512907793)
                ·
                  refine ⟨58057743178263782634680845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77410324237685043512907793 58057743178263782634680845)
                  ·
                    refine ⟨21771653691848918488005317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58057743178263782634680845 21771653691848918488005317)
                    ·
                      refine ⟨4082185067221672216500997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21771653691848918488005317 4082185067221672216500997)
                      ·
                        rfl

theorem cell23_7950027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2, 3, 4].length) (baseStart_7950027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7950027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7950027 prefixEnd_7950027 := by exact prefixLift 7950027
  have htrace : WordTrace (prefixWord ++ tailWord_7950027) baseStart_7950027 baseEnd_7950027 := by
    simpa [prefixWord, tailWord_7950027, baseEnd_7950027] using wordTrace_append hprefix tailTrace_7950027
  have hstable : (prefixWord ++ tailWord_7950027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7950027).length < 2 ^ (prefixWord ++ tailWord_7950027).sum := by decide
  have hdescent : baseEnd_7950027 < baseStart_7950027 := by decide
  rcases family_descends (prefixWord ++ tailWord_7950027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7950028 : List Nat := [2, 2, 1, 5, 3, 1, 2, 7]
def baseStart_7950028 : Nat := 118140960795 + 7950028 * 2 ^ 59
def prefixEnd_7950028 : Nat := 4983230072969 + 3 ^ 40 * 7950028 * 2
def baseEnd_7950028 : Nat := 151192058544530618984759

theorem tailTrace_7950028 : CollatzResearch.WordTrace tailWord_7950028 prefixEnd_7950028 151192058544530618984759 := by
  unfold tailWord_7950028
  simp only [CollatzResearch.WordTrace]
  refine ⟨144980671221206893765489369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193307561628275858353985825 144980671221206893765489369)
  ·
    refine ⟨108735503415905170324117027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144980671221206893765489369 108735503415905170324117027)
    ·
      refine ⟨163103255123857755486175541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108735503415905170324117027 163103255123857755486175541)
      ·
        refine ⟨15290930167861664576828957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 163103255123857755486175541 15290930167861664576828957)
        ·
          refine ⟨5734098812948124216310859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15290930167861664576828957 5734098812948124216310859)
          ·
            refine ⟨8601148219422186324466289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5734098812948124216310859 8601148219422186324466289)
            ·
              refine ⟨6450861164566639743349717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8601148219422186324466289 6450861164566639743349717)
              ·
                refine ⟨151192058544530618984759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6450861164566639743349717 151192058544530618984759)
                ·
                  rfl

theorem cell23_7950028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 2, 7].length) (baseStart_7950028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7950028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7950028 prefixEnd_7950028 := by exact prefixLift 7950028
  have htrace : WordTrace (prefixWord ++ tailWord_7950028) baseStart_7950028 baseEnd_7950028 := by
    simpa [prefixWord, tailWord_7950028, baseEnd_7950028] using wordTrace_append hprefix tailTrace_7950028
  have hstable : (prefixWord ++ tailWord_7950028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7950028).length < 2 ^ (prefixWord ++ tailWord_7950028).sum := by decide
  have hdescent : baseEnd_7950028 < baseStart_7950028 := by decide
  rcases family_descends (prefixWord ++ tailWord_7950028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7950034 : List Nat := [3, 2, 2, 2, 2, 1, 1, 1, 2, 2, 5]
def baseStart_7950034 : Nat := 118140960795 + 7950034 * 2 ^ 59
def prefixEnd_7950034 : Nat := 4983230072969 + 3 ^ 40 * 7950034 * 2
def baseEnd_7950034 : Nat := 4082188661586253689113465

theorem tailTrace_7950034 : CollatzResearch.WordTrace tailWord_7950034 prefixEnd_7950034 4082188661586253689113465 := by
  unfold tailWord_7950034
  simp only [CollatzResearch.WordTrace]
  refine ⟨72490390320098012638924289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193307707520261367037131437 72490390320098012638924289)
  ·
    refine ⟨54367792740073509479193217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72490390320098012638924289 54367792740073509479193217)
    ·
      refine ⟨40775844555055132109394913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54367792740073509479193217 40775844555055132109394913)
      ·
        refine ⟨30581883416291349082046185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40775844555055132109394913 30581883416291349082046185)
        ·
          refine ⟨22936412562218511811534639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30581883416291349082046185 22936412562218511811534639)
          ·
            refine ⟨34404618843327767717301959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22936412562218511811534639 34404618843327767717301959)
            ·
              refine ⟨51606928264991651575952939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34404618843327767717301959 51606928264991651575952939)
              ·
                refine ⟨77410392397487477363929409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51606928264991651575952939 77410392397487477363929409)
                ·
                  refine ⟨58057794298115608022947057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77410392397487477363929409 58057794298115608022947057)
                  ·
                    refine ⟨43543345723586706017210293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58057794298115608022947057 43543345723586706017210293)
                    ·
                      refine ⟨4082188661586253689113465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43543345723586706017210293 4082188661586253689113465)
                      ·
                        rfl

theorem cell23_7950034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_7950034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7950034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7950034 prefixEnd_7950034 := by exact prefixLift 7950034
  have htrace : WordTrace (prefixWord ++ tailWord_7950034) baseStart_7950034 baseEnd_7950034 := by
    simpa [prefixWord, tailWord_7950034, baseEnd_7950034] using wordTrace_append hprefix tailTrace_7950034
  have hstable : (prefixWord ++ tailWord_7950034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7950034).length < 2 ^ (prefixWord ++ tailWord_7950034).sum := by decide
  have hdescent : baseEnd_7950034 < baseStart_7950034 := by decide
  rcases family_descends (prefixWord ++ tailWord_7950034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7950107 : List Nat := [1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 7]
def baseStart_7950107 : Nat := 118140960795 + 7950107 * 2 ^ 59
def prefixEnd_7950107 : Nat := 4983230072969 + 3 ^ 40 * 7950107 * 2
def baseEnd_7950107 : Nat := 4082226145674031903500629

theorem tailTrace_7950107 : CollatzResearch.WordTrace tailWord_7950107 prefixEnd_7950107 4082226145674031903500629 := by
  unfold tailWord_7950107
  simp only [CollatzResearch.WordTrace]
  refine ⟨289964223809127584023104575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193309482539418389348736383 289964223809127584023104575)
  ·
    refine ⟨434946335713691376034656863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289964223809127584023104575 434946335713691376034656863)
    ·
      refine ⟨652419503570537064051985295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434946335713691376034656863 652419503570537064051985295)
      ·
        refine ⟨978629255355805596077977943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 652419503570537064051985295 978629255355805596077977943)
        ·
          refine ⟨1467943883033708394116966915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 978629255355805596077977943 1467943883033708394116966915)
          ·
            refine ⟨2201915824550562591175450373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1467943883033708394116966915 2201915824550562591175450373)
            ·
              refine ⟨412859217103230485845396945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2201915824550562591175450373 412859217103230485845396945)
              ·
                refine ⟨309644412827422864384047709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 412859217103230485845396945 309644412827422864384047709)
                ·
                  refine ⟨116116654810283574144017891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 309644412827422864384047709 116116654810283574144017891)
                  ·
                    refine ⟨174174982215425361216026837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 116116654810283574144017891 174174982215425361216026837)
                    ·
                      refine ⟨4082226145674031903500629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 174174982215425361216026837 4082226145674031903500629)
                      ·
                        rfl

theorem cell23_7950107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 7].length) (baseStart_7950107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7950107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7950107 prefixEnd_7950107 := by exact prefixLift 7950107
  have htrace : WordTrace (prefixWord ++ tailWord_7950107) baseStart_7950107 baseEnd_7950107 := by
    simpa [prefixWord, tailWord_7950107, baseEnd_7950107] using wordTrace_append hprefix tailTrace_7950107
  have hstable : (prefixWord ++ tailWord_7950107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7950107).length < 2 ^ (prefixWord ++ tailWord_7950107).sum := by decide
  have hdescent : baseEnd_7950107 < baseStart_7950107 := by decide
  rcases family_descends (prefixWord ++ tailWord_7950107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7950124 : List Nat := [2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 5]
def baseStart_7950124 : Nat := 118140960795 + 7950124 * 2 ^ 59
def prefixEnd_7950124 : Nat := 4983230072969 + 3 ^ 40 * 7950124 * 2
def baseEnd_7950124 : Nat := 4082234874845158336988051

theorem tailTrace_7950124 : CollatzResearch.WordTrace tailWord_7950124 prefixEnd_7950124 4082234874845158336988051 := by
  unfold tailWord_7950124
  simp only [CollatzResearch.WordTrace]
  refine ⟨144982421925032997963236713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193309895900043997284315617 144982421925032997963236713)
  ·
    refine ⟨108736816443774748472427535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144982421925032997963236713 108736816443774748472427535)
    ·
      refine ⟨163105224665662122708641303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108736816443774748472427535 163105224665662122708641303)
      ·
        refine ⟨244657836998493184062961955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163105224665662122708641303 244657836998493184062961955)
        ·
          refine ⟨366986755497739776094442933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244657836998493184062961955 366986755497739776094442933)
          ·
            refine ⟨34405008327913104008854025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 366986755497739776094442933 34405008327913104008854025)
            ·
              refine ⟨25803756245934828006640519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34405008327913104008854025 25803756245934828006640519)
              ·
                refine ⟨38705634368902242009960779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25803756245934828006640519 38705634368902242009960779)
                ·
                  refine ⟨58058451553353363014941169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38705634368902242009960779 58058451553353363014941169)
                  ·
                    refine ⟨43543838665015022261205877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58058451553353363014941169 43543838665015022261205877)
                    ·
                      refine ⟨4082234874845158336988051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43543838665015022261205877 4082234874845158336988051)
                      ·
                        rfl

theorem cell23_7950124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 5].length) (baseStart_7950124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7950124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7950124 prefixEnd_7950124 := by exact prefixLift 7950124
  have htrace : WordTrace (prefixWord ++ tailWord_7950124) baseStart_7950124 baseEnd_7950124 := by
    simpa [prefixWord, tailWord_7950124, baseEnd_7950124] using wordTrace_append hprefix tailTrace_7950124
  have hstable : (prefixWord ++ tailWord_7950124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7950124).length < 2 ^ (prefixWord ++ tailWord_7950124).sum := by decide
  have hdescent : baseEnd_7950124 < baseStart_7950124 := by decide
  rcases family_descends (prefixWord ++ tailWord_7950124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7950151 : List Nat := [1, 1, 4, 1, 2, 1, 5, 1, 2, 1, 4]
def baseStart_7950151 : Nat := 118140960795 + 7950151 * 2 ^ 59
def prefixEnd_7950151 : Nat := 4983230072969 + 3 ^ 40 * 7950151 * 2
def baseEnd_7950151 : Nat := 4082248738822829731350427

theorem tailTrace_7950151 : CollatzResearch.WordTrace tailWord_7950151 prefixEnd_7950151 4082248738822829731350427 := by
  unfold tailWord_7950151
  simp only [CollatzResearch.WordTrace]
  refine ⟨289965828620968179537706307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193310552413978786358470871 289965828620968179537706307)
  ·
    refine ⟨434948742931452269306559461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289965828620968179537706307 434948742931452269306559461)
    ·
      refine ⟨81552889299647300494979899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 434948742931452269306559461 81552889299647300494979899)
      ·
        refine ⟨122329333949470950742469849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81552889299647300494979899 122329333949470950742469849)
        ·
          refine ⟨91747000462103213056852387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122329333949470950742469849 91747000462103213056852387)
          ·
            refine ⟨137620500693154819585278581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91747000462103213056852387 137620500693154819585278581)
            ·
              refine ⟨12901921939983264336119867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 137620500693154819585278581 12901921939983264336119867)
              ·
                refine ⟨19352882909974896504179801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12901921939983264336119867 19352882909974896504179801)
                ·
                  refine ⟨14514662182481172378134851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19352882909974896504179801 14514662182481172378134851)
                  ·
                    refine ⟨21771993273721758567202277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14514662182481172378134851 21771993273721758567202277)
                    ·
                      refine ⟨4082248738822829731350427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21771993273721758567202277 4082248738822829731350427)
                      ·
                        rfl

theorem cell23_7950151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 1, 2, 1, 4].length) (baseStart_7950151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7950151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7950151 prefixEnd_7950151 := by exact prefixLift 7950151
  have htrace : WordTrace (prefixWord ++ tailWord_7950151) baseStart_7950151 baseEnd_7950151 := by
    simpa [prefixWord, tailWord_7950151, baseEnd_7950151] using wordTrace_append hprefix tailTrace_7950151
  have hstable : (prefixWord ++ tailWord_7950151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7950151).length < 2 ^ (prefixWord ++ tailWord_7950151).sum := by decide
  have hdescent : baseEnd_7950151 < baseStart_7950151 := by decide
  rcases family_descends (prefixWord ++ tailWord_7950151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7950178 : List Nat := [3, 3, 2, 1, 2, 1, 1, 3, 3, 4]
def baseStart_7950178 : Nat := 118140960795 + 7950178 * 2 ^ 59
def prefixEnd_7950178 : Nat := 4983230072969 + 3 ^ 40 * 7950178 * 2
def baseEnd_7950178 : Nat := 1360754200933500375237601

theorem tailTrace_7950178 : CollatzResearch.WordTrace tailWord_7950178 prefixEnd_7950178 1360754200933500375237601 := by
  unfold tailWord_7950178
  simp only [CollatzResearch.WordTrace]
  refine ⟨72491703347967590787234797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193311208927913575432626125 72491703347967590787234797)
  ·
    refine ⟨27184388755487846545213049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72491703347967590787234797 27184388755487846545213049)
    ·
      refine ⟨20388291566615884908909787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27184388755487846545213049 20388291566615884908909787)
      ·
        refine ⟨30582437349923827363364681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20388291566615884908909787 30582437349923827363364681)
        ·
          refine ⟨22936828012442870522523511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30582437349923827363364681 22936828012442870522523511)
          ·
            refine ⟨34405242018664305783785267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22936828012442870522523511 34405242018664305783785267)
            ·
              refine ⟨51607863027996458675677901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34405242018664305783785267 51607863027996458675677901)
              ·
                refine ⟨19352948635498672003379213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51607863027996458675677901 19352948635498672003379213)
                ·
                  refine ⟨7257355738312002001267205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19352948635498672003379213 7257355738312002001267205)
                  ·
                    refine ⟨1360754200933500375237601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7257355738312002001267205 1360754200933500375237601)
                    ·
                      rfl

theorem cell23_7950178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_7950178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7950178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7950178 prefixEnd_7950178 := by exact prefixLift 7950178
  have htrace : WordTrace (prefixWord ++ tailWord_7950178) baseStart_7950178 baseEnd_7950178 := by
    simpa [prefixWord, tailWord_7950178, baseEnd_7950178] using wordTrace_append hprefix tailTrace_7950178
  have hstable : (prefixWord ++ tailWord_7950178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7950178).length < 2 ^ (prefixWord ++ tailWord_7950178).sum := by decide
  have hdescent : baseEnd_7950178 < baseStart_7950178 := by decide
  rcases family_descends (prefixWord ++ tailWord_7950178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7950194 : List Nat := [3, 2, 1, 2, 1, 1, 1, 1, 3, 2, 6]
def baseStart_7950194 : Nat := 118140960795 + 7950194 * 2 ^ 59
def prefixEnd_7950194 : Nat := 4983230072969 + 3 ^ 40 * 7950194 * 2
def baseEnd_7950194 : Nat := 4082270818490973063112729

theorem tailTrace_7950194 : CollatzResearch.WordTrace tailWord_7950194 prefixEnd_7950194 4082270818490973063112729 := by
  unfold tailWord_7950194
  simp only [CollatzResearch.WordTrace]
  refine ⟨72491849239953099470380409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193311597973208265254347757 72491849239953099470380409)
  ·
    refine ⟨54368886929964824602785307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72491849239953099470380409 54368886929964824602785307)
    ·
      refine ⟨81553330394947236904177961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54368886929964824602785307 81553330394947236904177961)
      ·
        refine ⟨61164997796210427678133471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81553330394947236904177961 61164997796210427678133471)
        ·
          refine ⟨91747496694315641517200207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61164997796210427678133471 91747496694315641517200207)
          ·
            refine ⟨137621245041473462275800311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91747496694315641517200207 137621245041473462275800311)
            ·
              refine ⟨206431867562210193413700467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137621245041473462275800311 206431867562210193413700467)
              ·
                refine ⟨309647801343315290120550701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206431867562210193413700467 309647801343315290120550701)
                ·
                  refine ⟨116117925503743233795206513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 309647801343315290120550701 116117925503743233795206513)
                  ·
                    refine ⟨87088444127807425346404885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 116117925503743233795206513 87088444127807425346404885)
                    ·
                      refine ⟨4082270818490973063112729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87088444127807425346404885 4082270818490973063112729)
                      ·
                        rfl

theorem cell23_7950194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_7950194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7950194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7950194 prefixEnd_7950194 := by exact prefixLift 7950194
  have htrace : WordTrace (prefixWord ++ tailWord_7950194) baseStart_7950194 baseEnd_7950194 := by
    simpa [prefixWord, tailWord_7950194, baseEnd_7950194] using wordTrace_append hprefix tailTrace_7950194
  have hstable : (prefixWord ++ tailWord_7950194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7950194).length < 2 ^ (prefixWord ++ tailWord_7950194).sum := by decide
  have hdescent : baseEnd_7950194 < baseStart_7950194 := by decide
  rcases family_descends (prefixWord ++ tailWord_7950194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7950242 : List Nat := [3, 3, 1, 2, 4, 1, 2, 1, 6]
def baseStart_7950242 : Nat := 118140960795 + 7950242 * 2 ^ 59
def prefixEnd_7950242 : Nat := 4983230072969 + 3 ^ 40 * 7950242 * 2
def baseEnd_7950242 : Nat := 453588385062487652812501

theorem tailTrace_7950242 : CollatzResearch.WordTrace tailWord_7950242 prefixEnd_7950242 453588385062487652812501 := by
  unfold tailWord_7950242
  simp only [CollatzResearch.WordTrace]
  refine ⟨72492286915909625519817245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193312765109092334719512653 72492286915909625519817245)
  ·
    refine ⟨27184607593466109569931467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72492286915909625519817245 27184607593466109569931467)
    ·
      refine ⟨40776911390199164354897201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27184607593466109569931467 40776911390199164354897201)
      ·
        refine ⟨30582683542649373266172901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40776911390199164354897201 30582683542649373266172901)
        ·
          refine ⟨5734253164246757487407419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30582683542649373266172901 5734253164246757487407419)
          ·
            refine ⟨8601379746370136231111129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5734253164246757487407419 8601379746370136231111129)
            ·
              refine ⟨6451034809777602173333347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8601379746370136231111129 6451034809777602173333347)
              ·
                refine ⟨9676552214666403260000021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6451034809777602173333347 9676552214666403260000021)
                ·
                  refine ⟨453588385062487652812501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9676552214666403260000021 453588385062487652812501)
                  ·
                    rfl

theorem cell23_7950242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 2, 1, 6].length) (baseStart_7950242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7950242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7950242 prefixEnd_7950242 := by exact prefixLift 7950242
  have htrace : WordTrace (prefixWord ++ tailWord_7950242) baseStart_7950242 baseEnd_7950242 := by
    simpa [prefixWord, tailWord_7950242, baseEnd_7950242] using wordTrace_append hprefix tailTrace_7950242
  have hstable : (prefixWord ++ tailWord_7950242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7950242).length < 2 ^ (prefixWord ++ tailWord_7950242).sum := by decide
  have hdescent : baseEnd_7950242 < baseStart_7950242 := by decide
  rcases family_descends (prefixWord ++ tailWord_7950242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7950264 : List Nat := [2, 1, 2, 1, 2, 3, 1, 11]
def baseStart_7950264 : Nat := 118140960795 + 7950264 * 2 ^ 59
def prefixEnd_7950264 : Nat := 4983230072969 + 3 ^ 40 * 7950264 * 2
def baseEnd_7950264 : Nat := 151196546745806955156941

theorem tailTrace_7950264 : CollatzResearch.WordTrace tailWord_7950264 prefixEnd_7950264 151196546745806955156941 := by
  unfold tailWord_7950264
  simp only [CollatzResearch.WordTrace]
  refine ⟨144984975034779399918284923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193313300046372533224379897 144984975034779399918284923)
  ·
    refine ⟨217477462552169099877427385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144984975034779399918284923 217477462552169099877427385)
    ·
      refine ⟨163108096914126824908070539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217477462552169099877427385 163108096914126824908070539)
      ·
        refine ⟨244662145371190237362105809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163108096914126824908070539 244662145371190237362105809)
        ·
          refine ⟨183496609028392678021579357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244662145371190237362105809 183496609028392678021579357)
          ·
            refine ⟨68811228385647254258092259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183496609028392678021579357 68811228385647254258092259)
            ·
              refine ⟨103216842578470881387138389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68811228385647254258092259 103216842578470881387138389)
              ·
                refine ⟨151196546745806955156941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 103216842578470881387138389 151196546745806955156941)
                ·
                  rfl

theorem cell23_7950264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 11].length) (baseStart_7950264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7950264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7950264 prefixEnd_7950264 := by exact prefixLift 7950264
  have htrace : WordTrace (prefixWord ++ tailWord_7950264) baseStart_7950264 baseEnd_7950264 := by
    simpa [prefixWord, tailWord_7950264, baseEnd_7950264] using wordTrace_append hprefix tailTrace_7950264
  have hstable : (prefixWord ++ tailWord_7950264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7950264).length < 2 ^ (prefixWord ++ tailWord_7950264).sum := by decide
  have hdescent : baseEnd_7950264 < baseStart_7950264 := by decide
  rcases family_descends (prefixWord ++ tailWord_7950264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7950271 : List Nat := [1, 1, 2, 2, 2, 1, 5, 2, 1, 2, 4]
def baseStart_7950271 : Nat := 118140960795 + 7950271 * 2 ^ 59
def prefixEnd_7950271 : Nat := 4983230072969 + 3 ^ 40 * 7950271 * 2
def baseEnd_7950271 : Nat := 4082310356501369261849875

theorem tailTrace_7950271 : CollatzResearch.WordTrace tailWord_7950271 prefixEnd_7950271 4082310356501369261849875 := by
  unfold tailWord_7950271
  simp only [CollatzResearch.WordTrace]
  refine ⟨289970205380533440032074667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193313470253688960021383111 289970205380533440032074667)
  ·
    refine ⟨434955308070800160048112001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289970205380533440032074667 434955308070800160048112001)
    ·
      refine ⟨326216481053100120036084001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 434955308070800160048112001 326216481053100120036084001)
      ·
        refine ⟨244662360789825090027063001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326216481053100120036084001 244662360789825090027063001)
        ·
          refine ⟨183496770592368817520297251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244662360789825090027063001 183496770592368817520297251)
          ·
            refine ⟨275245155888553226280445877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183496770592368817520297251 275245155888553226280445877)
            ·
              refine ⟨25804233364551864963791801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 275245155888553226280445877 25804233364551864963791801)
              ·
                refine ⟨19353175023413898722843851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25804233364551864963791801 19353175023413898722843851)
                ·
                  refine ⟨29029762535120848084265777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19353175023413898722843851 29029762535120848084265777)
                  ·
                    refine ⟨21772321901340636063199333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29029762535120848084265777 21772321901340636063199333)
                    ·
                      refine ⟨4082310356501369261849875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21772321901340636063199333 4082310356501369261849875)
                      ·
                        rfl

theorem cell23_7950271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 2, 1, 2, 4].length) (baseStart_7950271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7950271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7950271 prefixEnd_7950271 := by exact prefixLift 7950271
  have htrace : WordTrace (prefixWord ++ tailWord_7950271) baseStart_7950271 baseEnd_7950271 := by
    simpa [prefixWord, tailWord_7950271, baseEnd_7950271] using wordTrace_append hprefix tailTrace_7950271
  have hstable : (prefixWord ++ tailWord_7950271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7950271).length < 2 ^ (prefixWord ++ tailWord_7950271).sum := by decide
  have hdescent : baseEnd_7950271 < baseStart_7950271 := by decide
  rcases family_descends (prefixWord ++ tailWord_7950271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7950298 : List Nat := [3, 1, 1, 2, 5, 2, 1, 8]
def baseStart_7950298 : Nat := 118140960795 + 7950298 * 2 ^ 59
def prefixEnd_7950298 : Nat := 4983230072969 + 3 ^ 40 * 7950298 * 2
def baseEnd_7950298 : Nat := 151197193351075579859713

theorem tailTrace_7950298 : CollatzResearch.WordTrace tailWord_7950298 prefixEnd_7950298 151197193351075579859713 := by
  unfold tailWord_7950298
  simp only [CollatzResearch.WordTrace]
  refine ⟨72492797537858905910826887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193314126767623749095538365 72492797537858905910826887)
  ·
    refine ⟨108739196306788358866240331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72492797537858905910826887 108739196306788358866240331)
    ·
      refine ⟨163108794460182538299360497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108739196306788358866240331 163108794460182538299360497)
      ·
        refine ⟨122331595845136903724520373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163108794460182538299360497 122331595845136903724520373)
        ·
          refine ⟨11468587110481584724173785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 122331595845136903724520373 11468587110481584724173785)
          ·
            refine ⟨8601440332861188543130339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11468587110481584724173785 8601440332861188543130339)
            ·
              refine ⟨12902160499291782814695509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8601440332861188543130339 12902160499291782814695509)
              ·
                refine ⟨151197193351075579859713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12902160499291782814695509 151197193351075579859713)
                ·
                  rfl

theorem cell23_7950298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 8].length) (baseStart_7950298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7950298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7950298 prefixEnd_7950298 := by exact prefixLift 7950298
  have htrace : WordTrace (prefixWord ++ tailWord_7950298) baseStart_7950298 baseEnd_7950298 := by
    simpa [prefixWord, tailWord_7950298, baseEnd_7950298] using wordTrace_append hprefix tailTrace_7950298
  have hstable : (prefixWord ++ tailWord_7950298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7950298).length < 2 ^ (prefixWord ++ tailWord_7950298).sum := by decide
  have hdescent : baseEnd_7950298 < baseStart_7950298 := by decide
  rcases family_descends (prefixWord ++ tailWord_7950298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7950308 : List Nat := [2, 3, 1, 1, 1, 1, 6, 1, 1, 3, 3]
def baseStart_7950308 : Nat := 118140960795 + 7950308 * 2 ^ 59
def prefixEnd_7950308 : Nat := 4983230072969 + 3 ^ 40 * 7950308 * 2
def baseEnd_7950308 : Nat := 4082329355285585617087205

theorem tailTrace_7950308 : CollatzResearch.WordTrace tailWord_7950308 prefixEnd_7950308 4082329355285585617087205 := by
  unfold tailWord_7950308
  simp only [CollatzResearch.WordTrace]
  refine ⟨144985777440699697675585789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193314369920932930234114385 144985777440699697675585789)
  ·
    refine ⟨54369666540262386628344671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144985777440699697675585789 54369666540262386628344671)
    ·
      refine ⟨81554499810393579942517007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54369666540262386628344671 81554499810393579942517007)
      ·
        refine ⟨122331749715590369913775511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81554499810393579942517007 122331749715590369913775511)
        ·
          refine ⟨183497624573385554870663267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122331749715590369913775511 183497624573385554870663267)
          ·
            refine ⟨275246436860078332305994901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183497624573385554870663267 275246436860078332305994901)
            ·
              refine ⟨12902176727816171826843511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 275246436860078332305994901 12902176727816171826843511)
              ·
                refine ⟨19353265091724257740265267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12902176727816171826843511 19353265091724257740265267)
                ·
                  refine ⟨29029897637586386610397901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19353265091724257740265267 29029897637586386610397901)
                  ·
                    refine ⟨10886211614094894978899213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29029897637586386610397901 10886211614094894978899213)
                    ·
                      refine ⟨4082329355285585617087205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10886211614094894978899213 4082329355285585617087205)
                      ·
                        rfl

theorem cell23_7950308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 1, 1, 3, 3].length) (baseStart_7950308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7950308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7950308 prefixEnd_7950308 := by exact prefixLift 7950308
  have htrace : WordTrace (prefixWord ++ tailWord_7950308) baseStart_7950308 baseEnd_7950308 := by
    simpa [prefixWord, tailWord_7950308, baseEnd_7950308] using wordTrace_append hprefix tailTrace_7950308
  have hstable : (prefixWord ++ tailWord_7950308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7950308).length < 2 ^ (prefixWord ++ tailWord_7950308).sum := by decide
  have hdescent : baseEnd_7950308 < baseStart_7950308 := by decide
  rcases family_descends (prefixWord ++ tailWord_7950308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7950326 : List Nat := [5, 1, 1, 1, 4, 1, 2, 3, 1, 2, 2]
def baseStart_7950326 : Nat := 118140960795 + 7950326 * 2 ^ 59
def prefixEnd_7950326 : Nat := 4983230072969 + 3 ^ 40 * 7950326 * 2
def baseEnd_7950326 : Nat := 4082338597937366546662123

theorem tailTrace_7950326 : CollatzResearch.WordTrace tailWord_7950326 prefixEnd_7950326 4082338597937366546662123 := by
  unfold tailWord_7950326
  simp only [CollatzResearch.WordTrace]
  refine ⟨18123263212208386526582927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 193314807596889456283551221 18123263212208386526582927)
  ·
    refine ⟨27184894818312579789874391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18123263212208386526582927 27184894818312579789874391)
    ·
      refine ⟨40777342227468869684811587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27184894818312579789874391 40777342227468869684811587)
      ·
        refine ⟨61166013341203304527217381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40777342227468869684811587 61166013341203304527217381)
        ·
          refine ⟨11468627501475619598853259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61166013341203304527217381 11468627501475619598853259)
          ·
            refine ⟨17202941252213429398279889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11468627501475619598853259 17202941252213429398279889)
            ·
              refine ⟨12902205939160072048709917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17202941252213429398279889 12902205939160072048709917)
              ·
                refine ⟨4838327227185027018266219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12902205939160072048709917 4838327227185027018266219)
                ·
                  refine ⟨7257490840777540527399329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4838327227185027018266219 7257490840777540527399329)
                  ·
                    refine ⟨5443118130583155395549497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7257490840777540527399329 5443118130583155395549497)
                    ·
                      refine ⟨4082338597937366546662123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5443118130583155395549497 4082338597937366546662123)
                      ·
                        rfl

theorem cell23_7950326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 3, 1, 2, 2].length) (baseStart_7950326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7950326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7950326 prefixEnd_7950326 := by exact prefixLift 7950326
  have htrace : WordTrace (prefixWord ++ tailWord_7950326) baseStart_7950326 baseEnd_7950326 := by
    simpa [prefixWord, tailWord_7950326, baseEnd_7950326] using wordTrace_append hprefix tailTrace_7950326
  have hstable : (prefixWord ++ tailWord_7950326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7950326).length < 2 ^ (prefixWord ++ tailWord_7950326).sum := by decide
  have hdescent : baseEnd_7950326 < baseStart_7950326 := by decide
  rcases family_descends (prefixWord ++ tailWord_7950326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7950341 : List Nat := [1, 3, 1, 1, 2, 4, 1, 2, 2, 6]
def baseStart_7950341 : Nat := 118140960795 + 7950341 * 2 ^ 59
def prefixEnd_7950341 : Nat := 4983230072969 + 3 ^ 40 * 7950341 * 2
def baseEnd_7950341 : Nat := 1360782100049061329324851

theorem tailTrace_7950341 : CollatzResearch.WordTrace tailWord_7950341 prefixEnd_7950341 1360782100049061329324851 := by
  unfold tailWord_7950341
  simp only [CollatzResearch.WordTrace]
  refine ⟨289972758490279841987122877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193315172326853227991415251 289972758490279841987122877)
  ·
    refine ⟨108739784433854940745171079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289972758490279841987122877 108739784433854940745171079)
    ·
      refine ⟨163109676650782411117756619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108739784433854940745171079 163109676650782411117756619)
      ·
        refine ⟨244664514976173616676634929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163109676650782411117756619 244664514976173616676634929)
        ·
          refine ⟨183498386232130212507476197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244664514976173616676634929 183498386232130212507476197)
          ·
            refine ⟨34405947418524414845151787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 183498386232130212507476197 34405947418524414845151787)
            ·
              refine ⟨51608921127786622267727681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34405947418524414845151787 51608921127786622267727681)
              ·
                refine ⟨38706690845839966700795761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51608921127786622267727681 38706690845839966700795761)
                ·
                  refine ⟨29030018134379975025596821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38706690845839966700795761 29030018134379975025596821)
                  ·
                    refine ⟨1360782100049061329324851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29030018134379975025596821 1360782100049061329324851)
                    ·
                      rfl

theorem cell23_7950341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 2, 2, 6].length) (baseStart_7950341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7950341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7950341 prefixEnd_7950341 := by exact prefixLift 7950341
  have htrace : WordTrace (prefixWord ++ tailWord_7950341) baseStart_7950341 baseEnd_7950341 := by
    simpa [prefixWord, tailWord_7950341, baseEnd_7950341] using wordTrace_append hprefix tailTrace_7950341
  have hstable : (prefixWord ++ tailWord_7950341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7950341).length < 2 ^ (prefixWord ++ tailWord_7950341).sum := by decide
  have hdescent : baseEnd_7950341 < baseStart_7950341 := by decide
  rcases family_descends (prefixWord ++ tailWord_7950341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7950359 : List Nat := [1, 1, 3, 5, 2, 1, 3, 1, 2, 1, 3]
def baseStart_7950359 : Nat := 118140960795 + 7950359 * 2 ^ 59
def prefixEnd_7950359 : Nat := 4983230072969 + 3 ^ 40 * 7950359 * 2
def baseEnd_7950359 : Nat := 4082355542798964917549471

theorem tailTrace_7950359 : CollatzResearch.WordTrace tailWord_7950359 prefixEnd_7950359 4082355542798964917549471 := by
  unfold tailWord_7950359
  simp only [CollatzResearch.WordTrace]
  refine ⟨289973415004214631061278131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193315610002809754040852087 289973415004214631061278131)
  ·
    refine ⟨434960122506321946591917197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289973415004214631061278131 434960122506321946591917197)
    ·
      refine ⟨163110045939870729971968949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 434960122506321946591917197 163110045939870729971968949)
      ·
        refine ⟨15291566806862880934872089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 163110045939870729971968949 15291566806862880934872089)
        ·
          refine ⟨11468675105147160701154067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15291566806862880934872089 11468675105147160701154067)
          ·
            refine ⟨17203012657720741051731101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11468675105147160701154067 17203012657720741051731101)
            ·
              refine ⟨6451129746645277894399163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17203012657720741051731101 6451129746645277894399163)
              ·
                refine ⟨9676694619967916841598745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6451129746645277894399163 9676694619967916841598745)
                ·
                  refine ⟨7257520964975937631199059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9676694619967916841598745 7257520964975937631199059)
                  ·
                    refine ⟨10886281447463906446798589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7257520964975937631199059 10886281447463906446798589)
                    ·
                      refine ⟨4082355542798964917549471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10886281447463906446798589 4082355542798964917549471)
                      ·
                        rfl

theorem cell23_7950359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_7950359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7950359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7950359 prefixEnd_7950359 := by exact prefixLift 7950359
  have htrace : WordTrace (prefixWord ++ tailWord_7950359) baseStart_7950359 baseEnd_7950359 := by
    simpa [prefixWord, tailWord_7950359, baseEnd_7950359] using wordTrace_append hprefix tailTrace_7950359
  have hstable : (prefixWord ++ tailWord_7950359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7950359).length < 2 ^ (prefixWord ++ tailWord_7950359).sum := by decide
  have hdescent : baseEnd_7950359 < baseStart_7950359 := by decide
  rcases family_descends (prefixWord ++ tailWord_7950359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7950371 : List Nat := [1, 1, 1, 4, 3, 1, 1, 4, 7]
def baseStart_7950371 : Nat := 118140960795 + 7950371 * 2 ^ 59
def prefixEnd_7950371 : Nat := 4983230072969 + 3 ^ 40 * 7950371 * 2
def baseEnd_7950371 : Nat := 453595744951868763399935

theorem tailTrace_7950371 : CollatzResearch.WordTrace tailWord_7950371 prefixEnd_7950371 453595744951868763399935 := by
  unfold tailWord_7950371
  simp only [CollatzResearch.WordTrace]
  refine ⟨289973852680171157110714967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193315901786780771407143311 289973852680171157110714967)
  ·
    refine ⟨434960779020256735666072451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289973852680171157110714967 434960779020256735666072451)
    ·
      refine ⟨652441168530385103499108677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434960779020256735666072451 652441168530385103499108677)
      ·
        refine ⟨122332719099447206906082877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 652441168530385103499108677 122332719099447206906082877)
        ·
          refine ⟨45874769662292702589781079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122332719099447206906082877 45874769662292702589781079)
          ·
            refine ⟨68812154493439053884671619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45874769662292702589781079 68812154493439053884671619)
            ·
              refine ⟨103218231740158580827007429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68812154493439053884671619 103218231740158580827007429)
              ·
                refine ⟨19353418451279733905063893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103218231740158580827007429 19353418451279733905063893)
                ·
                  refine ⟨453595744951868763399935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19353418451279733905063893 453595744951868763399935)
                  ·
                    rfl

theorem cell23_7950371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 4, 7].length) (baseStart_7950371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7950371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7950371 prefixEnd_7950371 := by exact prefixLift 7950371
  have htrace : WordTrace (prefixWord ++ tailWord_7950371) baseStart_7950371 baseEnd_7950371 := by
    simpa [prefixWord, tailWord_7950371, baseEnd_7950371] using wordTrace_append hprefix tailTrace_7950371
  have hstable : (prefixWord ++ tailWord_7950371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7950371).length < 2 ^ (prefixWord ++ tailWord_7950371).sum := by decide
  have hdescent : baseEnd_7950371 < baseStart_7950371 := by decide
  rcases family_descends (prefixWord ++ tailWord_7950371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7950382 : List Nat := [4, 1, 3, 1, 1, 2, 1, 2, 4, 2, 2]
def baseStart_7950382 : Nat := 118140960795 + 7950382 * 2 ^ 59
def prefixEnd_7950382 : Nat := 4983230072969 + 3 ^ 40 * 7950382 * 2
def baseEnd_7950382 : Nat := 4082367352854018327561865

theorem tailTrace_7950382 : CollatzResearch.WordTrace tailWord_7950382 prefixEnd_7950382 4082367352854018327561865 := by
  unfold tailWord_7950382
  simp only [CollatzResearch.WordTrace]
  refine ⟨36246781735391413248670675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193316169255420870659576933 36246781735391413248670675)
  ·
    refine ⟨54370172603087119873006013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36246781735391413248670675 54370172603087119873006013)
    ·
      refine ⟨20388814726157669952377255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54370172603087119873006013 20388814726157669952377255)
      ·
        refine ⟨30583222089236504928565883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20388814726157669952377255 30583222089236504928565883)
        ·
          refine ⟨45874833133854757392848825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30583222089236504928565883 45874833133854757392848825)
          ·
            refine ⟨34406124850391068044636619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45874833133854757392848825 34406124850391068044636619)
            ·
              refine ⟨51609187275586602066954929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34406124850391068044636619 51609187275586602066954929)
              ·
                refine ⟨38706890456689951550216197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51609187275586602066954929 38706890456689951550216197)
                ·
                  refine ⟨7257541960629365915665537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38706890456689951550216197 7257541960629365915665537)
                  ·
                    refine ⟨5443156470472024436749153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7257541960629365915665537 5443156470472024436749153)
                    ·
                      refine ⟨4082367352854018327561865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5443156470472024436749153 4082367352854018327561865)
                      ·
                        rfl

theorem cell23_7950382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 2, 4, 2, 2].length) (baseStart_7950382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7950382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7950382 prefixEnd_7950382 := by exact prefixLift 7950382
  have htrace : WordTrace (prefixWord ++ tailWord_7950382) baseStart_7950382 baseEnd_7950382 := by
    simpa [prefixWord, tailWord_7950382, baseEnd_7950382] using wordTrace_append hprefix tailTrace_7950382
  have hstable : (prefixWord ++ tailWord_7950382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7950382).length < 2 ^ (prefixWord ++ tailWord_7950382).sum := by decide
  have hdescent : baseEnd_7950382 < baseStart_7950382 := by decide
  rcases family_descends (prefixWord ++ tailWord_7950382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7950411 : List Nat := [1, 1, 1, 1, 3, 1, 2, 5, 1, 2, 5]
def baseStart_7950411 : Nat := 118140960795 + 7950411 * 2 ^ 59
def prefixEnd_7950411 : Nat := 4983230072969 + 3 ^ 40 * 7950411 * 2
def baseEnd_7950411 : Nat := 4082382243792998714099231

theorem tailTrace_7950411 : CollatzResearch.WordTrace tailWord_7950411 prefixEnd_7950411 4082382243792998714099231 := by
  unfold tailWord_7950411
  simp only [CollatzResearch.WordTrace]
  refine ⟨289975311600026243942171087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193316874400017495961447391 289975311600026243942171087)
  ·
    refine ⟨434962967400039365913256631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289975311600026243942171087 434962967400039365913256631)
    ·
      refine ⟨652444451100059048869884947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434962967400039365913256631 652444451100059048869884947)
      ·
        refine ⟨978666676650088573304827421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 652444451100059048869884947 978666676650088573304827421)
        ·
          refine ⟨367000003743783214989310283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 978666676650088573304827421 367000003743783214989310283)
          ·
            refine ⟨550500005615674822483965425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 367000003743783214989310283 550500005615674822483965425)
            ·
              refine ⟨412875004211756116862974069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 550500005615674822483965425 412875004211756116862974069)
              ·
                refine ⟨38707031644852135955903819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 412875004211756116862974069 38707031644852135955903819)
                ·
                  refine ⟨58060547467278203933855729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38707031644852135955903819 58060547467278203933855729)
                  ·
                    refine ⟨43545410600458652950391797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58060547467278203933855729 43545410600458652950391797)
                    ·
                      refine ⟨4082382243792998714099231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43545410600458652950391797 4082382243792998714099231)
                      ·
                        rfl

theorem cell23_7950411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5, 1, 2, 5].length) (baseStart_7950411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7950411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7950411 prefixEnd_7950411 := by exact prefixLift 7950411
  have htrace : WordTrace (prefixWord ++ tailWord_7950411) baseStart_7950411 baseEnd_7950411 := by
    simpa [prefixWord, tailWord_7950411, baseEnd_7950411] using wordTrace_append hprefix tailTrace_7950411
  have hstable : (prefixWord ++ tailWord_7950411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7950411).length < 2 ^ (prefixWord ++ tailWord_7950411).sum := by decide
  have hdescent : baseEnd_7950411 < baseStart_7950411 := by decide
  rcases family_descends (prefixWord ++ tailWord_7950411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7950472 : List Nat := [2, 1, 3, 4, 1, 2, 1, 1, 2, 4, 2]
def baseStart_7950472 : Nat := 118140960795 + 7950472 * 2 ^ 59
def prefixEnd_7950472 : Nat := 4983230072969 + 3 ^ 40 * 7950472 * 2
def baseEnd_7950472 : Nat := 4082413566112922975436451

theorem tailTrace_7950472 : CollatzResearch.WordTrace tailWord_7950472 prefixEnd_7950472 4082413566112922975436451 := by
  unfold tailWord_7950472
  simp only [CollatzResearch.WordTrace]
  refine ⟨144988768226402625680070835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193318357635203500906761113 144988768226402625680070835)
  ·
    refine ⟨217483152339603938520106253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144988768226402625680070835 217483152339603938520106253)
    ·
      refine ⟨81556182127351476945039845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217483152339603938520106253 81556182127351476945039845)
      ·
        refine ⟨15291784148878401927194971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81556182127351476945039845 15291784148878401927194971)
        ·
          refine ⟨22937676223317602890792457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15291784148878401927194971 22937676223317602890792457)
          ·
            refine ⟨17203257167488202168094343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22937676223317602890792457 17203257167488202168094343)
            ·
              refine ⟨25804885751232303252141515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17203257167488202168094343 25804885751232303252141515)
              ·
                refine ⟨38707328626848454878212273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25804885751232303252141515 38707328626848454878212273)
                ·
                  refine ⟨29030496470136341158659205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38707328626848454878212273 29030496470136341158659205)
                  ·
                    refine ⟨5443218088150563967248601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29030496470136341158659205 5443218088150563967248601)
                    ·
                      refine ⟨4082413566112922975436451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5443218088150563967248601 4082413566112922975436451)
                      ·
                        rfl

theorem cell23_7950472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_7950472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7950472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7950472 prefixEnd_7950472 := by exact prefixLift 7950472
  have htrace : WordTrace (prefixWord ++ tailWord_7950472) baseStart_7950472 baseEnd_7950472 := by
    simpa [prefixWord, tailWord_7950472, baseEnd_7950472] using wordTrace_append hprefix tailTrace_7950472
  have hstable : (prefixWord ++ tailWord_7950472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7950472).length < 2 ^ (prefixWord ++ tailWord_7950472).sum := by decide
  have hdescent : baseEnd_7950472 < baseStart_7950472 := by decide
  rcases family_descends (prefixWord ++ tailWord_7950472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7950486 : List Nat := [5, 3, 2, 1, 1, 1, 1, 1, 1, 7]
def baseStart_7950486 : Nat := 118140960795 + 7950486 * 2 ^ 59
def prefixEnd_7950486 : Nat := 4983230072969 + 3 ^ 40 * 7950486 * 2
def baseEnd_7950486 : Nat := 1360806918280695306887129

theorem tailTrace_7950486 : CollatzResearch.WordTrace tailWord_7950486 prefixEnd_7950486 1360806918280695306887129 := by
  unfold tailWord_7950486
  simp only [CollatzResearch.WordTrace]
  refine ⟨18123627942172158234446957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 193318698049836354500767541 18123627942172158234446957)
  ·
    refine ⟨6796360478314559337917609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18123627942172158234446957 6796360478314559337917609)
    ·
      refine ⟨5097270358735919503438207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6796360478314559337917609 5097270358735919503438207)
      ·
        refine ⟨7645905538103879255157311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5097270358735919503438207 7645905538103879255157311)
        ·
          refine ⟨11468858307155818882735967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7645905538103879255157311 11468858307155818882735967)
          ·
            refine ⟨17203287460733728324103951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11468858307155818882735967 17203287460733728324103951)
            ·
              refine ⟨25804931191100592486155927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17203287460733728324103951 25804931191100592486155927)
              ·
                refine ⟨38707396786650888729233891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25804931191100592486155927 38707396786650888729233891)
                ·
                  refine ⟨58061095179976333093850837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38707396786650888729233891 58061095179976333093850837)
                  ·
                    refine ⟨1360806918280695306887129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58061095179976333093850837 1360806918280695306887129)
                    ·
                      rfl

theorem cell23_7950486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_7950486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7950486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7950486 prefixEnd_7950486 := by exact prefixLift 7950486
  have htrace : WordTrace (prefixWord ++ tailWord_7950486) baseStart_7950486 baseEnd_7950486 := by
    simpa [prefixWord, tailWord_7950486, baseEnd_7950486] using wordTrace_append hprefix tailTrace_7950486
  have hstable : (prefixWord ++ tailWord_7950486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7950486).length < 2 ^ (prefixWord ++ tailWord_7950486).sum := by decide
  have hdescent : baseEnd_7950486 < baseStart_7950486 := by decide
  rcases family_descends (prefixWord ++ tailWord_7950486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7950491 : List Nat := [1, 1, 1, 1, 1, 1, 2, 4, 2, 9]
def baseStart_7950491 : Nat := 118140960795 + 7950491 * 2 ^ 59
def prefixEnd_7950491 : Nat := 4983230072969 + 3 ^ 40 * 7950491 * 2
def baseEnd_7950491 : Nat := 1360807774081786133699621

theorem tailTrace_7950491 : CollatzResearch.WordTrace tailWord_7950491 prefixEnd_7950491 1360807774081786133699621 := by
  unfold tailWord_7950491
  simp only [CollatzResearch.WordTrace]
  refine ⟨289978229439736417605083327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193318819626490945070055551 289978229439736417605083327)
  ·
    refine ⟨434967344159604626407624991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289978229439736417605083327 434967344159604626407624991)
    ·
      refine ⟨652451016239406939611437487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434967344159604626407624991 652451016239406939611437487)
      ·
        refine ⟨978676524359110409417156231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 652451016239406939611437487 978676524359110409417156231)
        ·
          refine ⟨1468014786538665614125734347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 978676524359110409417156231 1468014786538665614125734347)
          ·
            refine ⟨2202022179807998421188601521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1468014786538665614125734347 2202022179807998421188601521)
            ·
              refine ⟨1651516634855998815891451141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2202022179807998421188601521 1651516634855998815891451141)
              ·
                refine ⟨309659369035499777979647089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1651516634855998815891451141 309659369035499777979647089)
                ·
                  refine ⟨232244526776624833484735317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 309659369035499777979647089 232244526776624833484735317)
                  ·
                    refine ⟨1360807774081786133699621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 232244526776624833484735317 1360807774081786133699621)
                    ·
                      rfl

theorem cell23_7950491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 9].length) (baseStart_7950491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7950491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7950491 prefixEnd_7950491 := by exact prefixLift 7950491
  have htrace : WordTrace (prefixWord ++ tailWord_7950491) baseStart_7950491 baseEnd_7950491 := by
    simpa [prefixWord, tailWord_7950491, baseEnd_7950491] using wordTrace_append hprefix tailTrace_7950491
  have hstable : (prefixWord ++ tailWord_7950491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7950491).length < 2 ^ (prefixWord ++ tailWord_7950491).sum := by decide
  have hdescent : baseEnd_7950491 < baseStart_7950491 := by decide
  rcases family_descends (prefixWord ++ tailWord_7950491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7950515 : List Nat := [1, 1, 1, 2, 3, 2, 1, 3, 4, 3, 2]
def baseStart_7950515 : Nat := 118140960795 + 7950515 * 2 ^ 59
def prefixEnd_7950515 : Nat := 4983230072969 + 3 ^ 40 * 7950515 * 2
def baseEnd_7950515 : Nat := 4082435645781066307198753

theorem tailTrace_7950515 : CollatzResearch.WordTrace tailWord_7950515 prefixEnd_7950515 4082435645781066307198753 := by
  unfold tailWord_7950515
  simp only [CollatzResearch.WordTrace]
  refine ⟨289979104791649469703956999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193319403194432979802637999 289979104791649469703956999)
  ·
    refine ⟨434968657187474204555935499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289979104791649469703956999 434968657187474204555935499)
    ·
      refine ⟨652452985781211306833903249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434968657187474204555935499 652452985781211306833903249)
      ·
        refine ⟨489339739335908480125427437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 652452985781211306833903249 489339739335908480125427437)
        ·
          refine ⟨183502402250965680047035289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 489339739335908480125427437 183502402250965680047035289)
          ·
            refine ⟨137626801688224260035276467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183502402250965680047035289 137626801688224260035276467)
            ·
              refine ⟨206440202532336390052914701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137626801688224260035276467 206440202532336390052914701)
              ·
                refine ⟨77415075949626146269843013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 206440202532336390052914701 77415075949626146269843013)
                ·
                  refine ⟨14515326740554902425595565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77415075949626146269843013 14515326740554902425595565)
                  ·
                    refine ⟨5443247527708088409598337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14515326740554902425595565 5443247527708088409598337)
                    ·
                      refine ⟨4082435645781066307198753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5443247527708088409598337 4082435645781066307198753)
                      ·
                        rfl

theorem cell23_7950515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 4, 3, 2].length) (baseStart_7950515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7950515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7950515 prefixEnd_7950515 := by exact prefixLift 7950515
  have htrace : WordTrace (prefixWord ++ tailWord_7950515) baseStart_7950515 baseEnd_7950515 := by
    simpa [prefixWord, tailWord_7950515, baseEnd_7950515] using wordTrace_append hprefix tailTrace_7950515
  have hstable : (prefixWord ++ tailWord_7950515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7950515).length < 2 ^ (prefixWord ++ tailWord_7950515).sum := by decide
  have hdescent : baseEnd_7950515 < baseStart_7950515 := by decide
  rcases family_descends (prefixWord ++ tailWord_7950515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7950529 : List Nat := [1, 2, 6, 1, 2, 1, 3, 1, 6]
def baseStart_7950529 : Nat := 118140960795 + 7950529 * 2 ^ 59
def prefixEnd_7950529 : Nat := 4983230072969 + 3 ^ 40 * 7950529 * 2
def baseEnd_7950529 : Nat := 453604759390025472491521

theorem tailTrace_7950529 : CollatzResearch.WordTrace tailWord_7950529 prefixEnd_7950529 453604759390025472491521 := by
  unfold tailWord_7950529
  simp only [CollatzResearch.WordTrace]
  refine ⟨289979615413598750094966641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193319743609065833396644427 289979615413598750094966641)
  ·
    refine ⟨217484711560199062571224981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289979615413598750094966641 217484711560199062571224981)
    ·
      refine ⟨10194595854384331058026171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 217484711560199062571224981 10194595854384331058026171)
      ·
        refine ⟨15291893781576496587039257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10194595854384331058026171 15291893781576496587039257)
        ·
          refine ⟨11468920336182372440279443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15291893781576496587039257 11468920336182372440279443)
          ·
            refine ⟨17203380504273558660419165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11468920336182372440279443 17203380504273558660419165)
            ·
              refine ⟨6451267689102584497657187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17203380504273558660419165 6451267689102584497657187)
              ·
                refine ⟨9676901533653876746485781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6451267689102584497657187 9676901533653876746485781)
                ·
                  refine ⟨453604759390025472491521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9676901533653876746485781 453604759390025472491521)
                  ·
                    rfl

theorem cell23_7950529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 3, 1, 6].length) (baseStart_7950529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7950529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7950529 prefixEnd_7950529 := by exact prefixLift 7950529
  have htrace : WordTrace (prefixWord ++ tailWord_7950529) baseStart_7950529 baseEnd_7950529 := by
    simpa [prefixWord, tailWord_7950529, baseEnd_7950529] using wordTrace_append hprefix tailTrace_7950529
  have hstable : (prefixWord ++ tailWord_7950529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7950529).length < 2 ^ (prefixWord ++ tailWord_7950529).sum := by decide
  have hdescent : baseEnd_7950529 < baseStart_7950529 := by decide
  rcases family_descends (prefixWord ++ tailWord_7950529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7950532 : List Nat := [2, 3, 3, 1, 2, 1, 1, 2, 1, 5, 2]
def baseStart_7950532 : Nat := 118140960795 + 7950532 * 2 ^ 59
def prefixEnd_7950532 : Nat := 4983230072969 + 3 ^ 40 * 7950532 * 2
def baseEnd_7950532 : Nat := 4082444374952192740686175

theorem tailTrace_7950532 : CollatzResearch.WordTrace tailWord_7950532 prefixEnd_7950532 4082444374952192740686175 := by
  unfold tailWord_7950532
  simp only [CollatzResearch.WordTrace]
  refine ⟨144989862416293940803662925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193319816555058587738217233 144989862416293940803662925)
  ·
    refine ⟨54371198406110227801373597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144989862416293940803662925 54371198406110227801373597)
    ·
      refine ⟨20389199402291335425515099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54371198406110227801373597 20389199402291335425515099)
      ·
        refine ⟨30583799103437003138272649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20389199402291335425515099 30583799103437003138272649)
        ·
          refine ⟨22937849327577752353704487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30583799103437003138272649 22937849327577752353704487)
          ·
            refine ⟨34406773991366628530556731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22937849327577752353704487 34406773991366628530556731)
            ·
              refine ⟨51610160987049942795835097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34406773991366628530556731 51610160987049942795835097)
              ·
                refine ⟨38707620740287457096876323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51610160987049942795835097 38707620740287457096876323)
                ·
                  refine ⟨58061431110431185645314485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38707620740287457096876323 58061431110431185645314485)
                  ·
                    refine ⟨5443259166602923654248233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58061431110431185645314485 5443259166602923654248233)
                    ·
                      refine ⟨4082444374952192740686175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5443259166602923654248233 4082444374952192740686175)
                      ·
                        rfl

theorem cell23_7950532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 2, 1, 5, 2].length) (baseStart_7950532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7950532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7950532 prefixEnd_7950532 := by exact prefixLift 7950532
  have htrace : WordTrace (prefixWord ++ tailWord_7950532) baseStart_7950532 baseEnd_7950532 := by
    simpa [prefixWord, tailWord_7950532, baseEnd_7950532] using wordTrace_append hprefix tailTrace_7950532
  have hstable : (prefixWord ++ tailWord_7950532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7950532).length < 2 ^ (prefixWord ++ tailWord_7950532).sum := by decide
  have hdescent : baseEnd_7950532 < baseStart_7950532 := by decide
  rcases family_descends (prefixWord ++ tailWord_7950532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7950542 : List Nat := [4, 1, 1, 1, 4, 2, 2, 2, 1, 5]
def baseStart_7950542 : Nat := 118140960795 + 7950542 * 2 ^ 59
def prefixEnd_7950542 : Nat := 4983230072969 + 3 ^ 40 * 7950542 * 2
def baseEnd_7950542 : Nat := 1360816503252912567187043

theorem tailTrace_7950542 : CollatzResearch.WordTrace tailWord_7950542 prefixEnd_7950542 1360816503252912567187043 := by
  unfold tailWord_7950542
  simp only [CollatzResearch.WordTrace]
  refine ⟨36247511195318956664398735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193320059708367768876793253 36247511195318956664398735)
  ·
    refine ⟨54371266792978434996598103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36247511195318956664398735 54371266792978434996598103)
    ·
      refine ⟨81556900189467652494897155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54371266792978434996598103 81556900189467652494897155)
      ·
        refine ⟨122335350284201478742345733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81556900189467652494897155 122335350284201478742345733)
        ·
          refine ⟨22937878178287777264189825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122335350284201478742345733 22937878178287777264189825)
          ·
            refine ⟨17203408633715832948142369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22937878178287777264189825 17203408633715832948142369)
            ·
              refine ⟨12902556475286874711106777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17203408633715832948142369 12902556475286874711106777)
              ·
                refine ⟨9676917356465156033330083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12902556475286874711106777 9676917356465156033330083)
                ·
                  refine ⟨14515376034697734049995125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9676917356465156033330083 14515376034697734049995125)
                  ·
                    refine ⟨1360816503252912567187043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14515376034697734049995125 1360816503252912567187043)
                    ·
                      rfl

theorem cell23_7950542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 2, 1, 5].length) (baseStart_7950542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7950542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7950542 prefixEnd_7950542 := by exact prefixLift 7950542
  have htrace : WordTrace (prefixWord ++ tailWord_7950542) baseStart_7950542 baseEnd_7950542 := by
    simpa [prefixWord, tailWord_7950542, baseEnd_7950542] using wordTrace_append hprefix tailTrace_7950542
  have hstable : (prefixWord ++ tailWord_7950542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7950542).length < 2 ^ (prefixWord ++ tailWord_7950542).sum := by decide
  have hdescent : baseEnd_7950542 < baseStart_7950542 := by decide
  rcases family_descends (prefixWord ++ tailWord_7950542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7950545 : List Nat := [1, 2, 2, 1, 2, 2, 3, 4, 1, 1, 4]
def baseStart_7950545 : Nat := 118140960795 + 7950545 * 2 ^ 59
def prefixEnd_7950545 : Nat := 4983230072969 + 3 ^ 40 * 7950545 * 2
def baseEnd_7950545 : Nat := 4082451050200701189823615

theorem tailTrace_7950545 : CollatzResearch.WordTrace tailWord_7950545 prefixEnd_7950545 4082451050200701189823615 := by
  unfold tailWord_7950545
  simp only [CollatzResearch.WordTrace]
  refine ⟨289980198981540784827549089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193320132654360523218366059 289980198981540784827549089)
  ·
    refine ⟨217485149236155588620661817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289980198981540784827549089 217485149236155588620661817)
    ·
      refine ⟨163113861927116691465496363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217485149236155588620661817 163113861927116691465496363)
      ·
        refine ⟨244670792890675037198244545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163113861927116691465496363 244670792890675037198244545)
        ·
          refine ⟨183503094668006277898683409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244670792890675037198244545 183503094668006277898683409)
          ·
            refine ⟨137627321001004708424012557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183503094668006277898683409 137627321001004708424012557)
            ·
              refine ⟨51610245375376765659004709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137627321001004708424012557 51610245375376765659004709)
              ·
                refine ⟨9676921007883143561063383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51610245375376765659004709 9676921007883143561063383)
                ·
                  refine ⟨14515381511824715341595075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9676921007883143561063383 14515381511824715341595075)
                  ·
                    refine ⟨21773072267737073012392613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14515381511824715341595075 21773072267737073012392613)
                    ·
                      refine ⟨4082451050200701189823615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21773072267737073012392613 4082451050200701189823615)
                      ·
                        rfl

theorem cell23_7950545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 4, 1, 1, 4].length) (baseStart_7950545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7950545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7950545 prefixEnd_7950545 := by exact prefixLift 7950545
  have htrace : WordTrace (prefixWord ++ tailWord_7950545) baseStart_7950545 baseEnd_7950545 := by
    simpa [prefixWord, tailWord_7950545, baseEnd_7950545] using wordTrace_append hprefix tailTrace_7950545
  have hstable : (prefixWord ++ tailWord_7950545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7950545).length < 2 ^ (prefixWord ++ tailWord_7950545).sum := by decide
  have hdescent : baseEnd_7950545 < baseStart_7950545 := by decide
  rcases family_descends (prefixWord ++ tailWord_7950545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7950565 : List Nat := [1, 3, 1, 4, 2, 1, 1, 3, 1, 1, 5]
def baseStart_7950565 : Nat := 118140960795 + 7950565 * 2 ^ 59
def prefixEnd_7950565 : Nat := 4983230072969 + 3 ^ 40 * 7950565 * 2
def baseEnd_7950565 : Nat := 4082461319813791111573523

theorem tailTrace_7950565 : CollatzResearch.WordTrace tailWord_7950565 prefixEnd_7950565 4082461319813791111573523 := by
  unfold tailWord_7950565
  simp only [CollatzResearch.WordTrace]
  refine ⟨289980928441468328243277149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193320618960978885495518099 289980928441468328243277149)
  ·
    refine ⟨108742848165550623091228931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289980928441468328243277149 108742848165550623091228931)
    ·
      refine ⟨163114272248325934636843397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108742848165550623091228931 163114272248325934636843397)
      ·
        refine ⟨30583926046561112744408137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163114272248325934636843397 30583926046561112744408137)
        ·
          refine ⟨22937944534920834558306103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30583926046561112744408137 22937944534920834558306103)
          ·
            refine ⟨34406916802381251837459155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22937944534920834558306103 34406916802381251837459155)
            ·
              refine ⟨51610375203571877756188733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34406916802381251837459155 51610375203571877756188733)
              ·
                refine ⟨19353890701339454158570775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51610375203571877756188733 19353890701339454158570775)
                ·
                  refine ⟨29030836052009181237856163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19353890701339454158570775 29030836052009181237856163)
                  ·
                    refine ⟨43546254078013771856784245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29030836052009181237856163 43546254078013771856784245)
                    ·
                      refine ⟨4082461319813791111573523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43546254078013771856784245 4082461319813791111573523)
                      ·
                        rfl

theorem cell23_7950565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_7950565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7950565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7950565 prefixEnd_7950565 := by exact prefixLift 7950565
  have htrace : WordTrace (prefixWord ++ tailWord_7950565) baseStart_7950565 baseEnd_7950565 := by
    simpa [prefixWord, tailWord_7950565, baseEnd_7950565] using wordTrace_append hprefix tailTrace_7950565
  have hstable : (prefixWord ++ tailWord_7950565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7950565).length < 2 ^ (prefixWord ++ tailWord_7950565).sum := by decide
  have hdescent : baseEnd_7950565 < baseStart_7950565 := by decide
  rcases family_descends (prefixWord ++ tailWord_7950565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7950568 : List Nat := [2, 1, 4, 1, 2, 2, 11]
def baseStart_7950568 : Nat := 118140960795 + 7950568 * 2 ^ 59
def prefixEnd_7950568 : Nat := 4983230072969 + 3 ^ 40 * 7950568 * 2
def baseEnd_7950568 : Nat := 50400776052540180244889

theorem tailTrace_7950568 : CollatzResearch.WordTrace tailWord_7950568 prefixEnd_7950568 50400776052540180244889 := by
  unfold tailWord_7950568
  simp only [CollatzResearch.WordTrace]
  refine ⟨144990518930228729877818179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193320691906971639837090905 144990518930228729877818179)
  ·
    refine ⟨217485778395343094816727269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144990518930228729877818179 217485778395343094816727269)
    ·
      refine ⟨40778583449126830278136363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 217485778395343094816727269 40778583449126830278136363)
      ·
        refine ⟨61167875173690245417204545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40778583449126830278136363 61167875173690245417204545)
        ·
          refine ⟨45875906380267684062903409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61167875173690245417204545 45875906380267684062903409)
          ·
            refine ⟨34406929785200763047177557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45875906380267684062903409 34406929785200763047177557)
            ·
              refine ⟨50400776052540180244889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 34406929785200763047177557 50400776052540180244889)
              ·
                rfl

theorem cell23_7950568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 11].length) (baseStart_7950568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7950568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7950568 prefixEnd_7950568 := by exact prefixLift 7950568
  have htrace : WordTrace (prefixWord ++ tailWord_7950568) baseStart_7950568 baseEnd_7950568 := by
    simpa [prefixWord, tailWord_7950568, baseEnd_7950568] using wordTrace_append hprefix tailTrace_7950568
  have hstable : (prefixWord ++ tailWord_7950568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7950568).length < 2 ^ (prefixWord ++ tailWord_7950568).sum := by decide
  have hdescent : baseEnd_7950568 < baseStart_7950568 := by decide
  rcases family_descends (prefixWord ++ tailWord_7950568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7950573 : List Nat := [1, 5, 1, 2, 3, 1, 3, 2, 1, 1, 3]
def baseStart_7950573 : Nat := 118140960795 + 7950573 * 2 ^ 59
def prefixEnd_7950573 : Nat := 4983230072969 + 3 ^ 40 * 7950573 * 2
def baseEnd_7950573 : Nat := 4082465427659027080273487

theorem tailTrace_7950573 : CollatzResearch.WordTrace tailWord_7950573 prefixEnd_7950573 4082465427659027080273487 := by
  unfold tailWord_7950573
  simp only [CollatzResearch.WordTrace]
  refine ⟨289981220225439345609568373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193320813483626230406378915 289981220225439345609568373)
  ·
    refine ⟨27185739396134938650897035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 289981220225439345609568373 27185739396134938650897035)
    ·
      refine ⟨40778609094202407976345553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27185739396134938650897035 40778609094202407976345553)
      ·
        refine ⟨30583956820651805982259165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40778609094202407976345553 30583956820651805982259165)
        ·
          refine ⟨11468983807744427243347187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30583956820651805982259165 11468983807744427243347187)
          ·
            refine ⟨17203475711616640865020781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11468983807744427243347187 17203475711616640865020781)
            ·
              refine ⟨6451303391856240324382793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17203475711616640865020781 6451303391856240324382793)
              ·
                refine ⟨4838477543892180243287095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6451303391856240324382793 4838477543892180243287095)
                ·
                  refine ⟨7257716315838270364930643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4838477543892180243287095 7257716315838270364930643)
                  ·
                    refine ⟨10886574473757405547395965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7257716315838270364930643 10886574473757405547395965)
                    ·
                      refine ⟨4082465427659027080273487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10886574473757405547395965 4082465427659027080273487)
                      ·
                        rfl

theorem cell23_7950573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 3, 2, 1, 1, 3].length) (baseStart_7950573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7950573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7950573 prefixEnd_7950573 := by exact prefixLift 7950573
  have htrace : WordTrace (prefixWord ++ tailWord_7950573) baseStart_7950573 baseEnd_7950573 := by
    simpa [prefixWord, tailWord_7950573, baseEnd_7950573] using wordTrace_append hprefix tailTrace_7950573
  have hstable : (prefixWord ++ tailWord_7950573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7950573).length < 2 ^ (prefixWord ++ tailWord_7950573).sum := by decide
  have hdescent : baseEnd_7950573 < baseStart_7950573 := by decide
  rcases family_descends (prefixWord ++ tailWord_7950573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7950595 : List Nat := [1, 1, 1, 3, 2, 3, 2, 3, 1, 3, 3]
def baseStart_7950595 : Nat := 118140960795 + 7950595 * 2 ^ 59
def prefixEnd_7950595 : Nat := 4983230072969 + 3 ^ 40 * 7950595 * 2
def baseEnd_7950595 : Nat := 4082476724233425994198385

theorem tailTrace_7950595 : CollatzResearch.WordTrace tailWord_7950595 prefixEnd_7950595 4082476724233425994198385 := by
  unfold tailWord_7950595
  simp only [CollatzResearch.WordTrace]
  refine ⟨289982022631359643366869239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193321348420906428911246159 289982022631359643366869239)
  ·
    refine ⟨434973033947039465050303859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289982022631359643366869239 434973033947039465050303859)
    ·
      refine ⟨652459550920559197575455789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434973033947039465050303859 652459550920559197575455789)
      ·
        refine ⟨244672331595209699090795921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 652459550920559197575455789 244672331595209699090795921)
        ·
          refine ⟨183504248696407274318096941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244672331595209699090795921 183504248696407274318096941)
          ·
            refine ⟨68814093261152727869286353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183504248696407274318096941 68814093261152727869286353)
            ·
              refine ⟨51610569945864545901964765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68814093261152727869286353 51610569945864545901964765)
              ·
                refine ⟨19353963729699204713236787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51610569945864545901964765 19353963729699204713236787)
                ·
                  refine ⟨29030945594548807069855181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19353963729699204713236787 29030945594548807069855181)
                  ·
                    refine ⟨10886604597955802651195693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29030945594548807069855181 10886604597955802651195693)
                    ·
                      refine ⟨4082476724233425994198385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10886604597955802651195693 4082476724233425994198385)
                      ·
                        rfl

theorem cell23_7950595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 3, 1, 3, 3].length) (baseStart_7950595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7950595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7950595 prefixEnd_7950595 := by exact prefixLift 7950595
  have htrace : WordTrace (prefixWord ++ tailWord_7950595) baseStart_7950595 baseEnd_7950595 := by
    simpa [prefixWord, tailWord_7950595, baseEnd_7950595] using wordTrace_append hprefix tailTrace_7950595
  have hstable : (prefixWord ++ tailWord_7950595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7950595).length < 2 ^ (prefixWord ++ tailWord_7950595).sum := by decide
  have hdescent : baseEnd_7950595 < baseStart_7950595 := by decide
  rcases family_descends (prefixWord ++ tailWord_7950595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7950596 : List Nat := [2, 3, 2, 2, 4, 1, 1, 2, 1, 1, 4]
def baseStart_7950596 : Nat := 118140960795 + 7950596 * 2 ^ 59
def prefixEnd_7950596 : Nat := 4983230072969 + 3 ^ 40 * 7950596 * 2
def baseEnd_7950596 : Nat := 4082477237714080490285881

theorem tailTrace_7950596 : CollatzResearch.WordTrace tailWord_7950596 prefixEnd_7950596 4082477237714080490285881 := by
  unfold tailWord_7950596
  simp only [CollatzResearch.WordTrace]
  refine ⟨144991029552178010268827821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193321372736237347025103761 144991029552178010268827821)
  ·
    refine ⟨54371636082066753850810433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144991029552178010268827821 54371636082066753850810433)
    ·
      refine ⟨40778727061550065388107825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54371636082066753850810433 40778727061550065388107825)
      ·
        refine ⟨30584045296162549041080869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40778727061550065388107825 30584045296162549041080869)
        ·
          refine ⟨5734508493030477945202663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30584045296162549041080869 5734508493030477945202663)
          ·
            refine ⟨8601762739545716917803995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5734508493030477945202663 8601762739545716917803995)
            ·
              refine ⟨12902644109318575376705993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8601762739545716917803995 12902644109318575376705993)
              ·
                refine ⟨9676983081988931532529495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12902644109318575376705993 9676983081988931532529495)
                ·
                  refine ⟨14515474622983397298794243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9676983081988931532529495 14515474622983397298794243)
                  ·
                    refine ⟨21773211934475095948191365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14515474622983397298794243 21773211934475095948191365)
                    ·
                      refine ⟨4082477237714080490285881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21773211934475095948191365 4082477237714080490285881)
                      ·
                        rfl

theorem cell23_7950596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 2, 1, 1, 4].length) (baseStart_7950596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7950596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7950596 prefixEnd_7950596 := by exact prefixLift 7950596
  have htrace : WordTrace (prefixWord ++ tailWord_7950596) baseStart_7950596 baseEnd_7950596 := by
    simpa [prefixWord, tailWord_7950596, baseEnd_7950596] using wordTrace_append hprefix tailTrace_7950596
  have hstable : (prefixWord ++ tailWord_7950596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7950596).length < 2 ^ (prefixWord ++ tailWord_7950596).sum := by decide
  have hdescent : baseEnd_7950596 < baseStart_7950596 := by decide
  rcases family_descends (prefixWord ++ tailWord_7950596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7950599 : List Nat := [1, 1, 4, 5, 1, 1, 1, 1, 3, 2, 3]
def baseStart_7950599 : Nat := 118140960795 + 7950599 * 2 ^ 59
def prefixEnd_7950599 : Nat := 4983230072969 + 3 ^ 40 * 7950599 * 2
def baseEnd_7950599 : Nat := 4082478778156043978548367

theorem tailTrace_7950599 : CollatzResearch.WordTrace tailWord_7950599 prefixEnd_7950599 4082478778156043978548367 := by
  unfold tailWord_7950599
  simp only [CollatzResearch.WordTrace]
  refine ⟨289982168523345152050014851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193321445682230101366676567 289982168523345152050014851)
  ·
    refine ⟨434973252785017728075022277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289982168523345152050014851 434973252785017728075022277)
    ·
      refine ⟨81557484897190824014066677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 434973252785017728075022277 81557484897190824014066677)
      ·
        refine ⟨7646014209111639751318751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81557484897190824014066677 7646014209111639751318751)
        ·
          refine ⟨11469021313667459626978127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7646014209111639751318751 11469021313667459626978127)
          ·
            refine ⟨17203531970501189440467191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11469021313667459626978127 17203531970501189440467191)
            ·
              refine ⟨25805297955751784160700787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17203531970501189440467191 25805297955751784160700787)
              ·
                refine ⟨38707946933627676241051181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25805297955751784160700787 38707946933627676241051181)
                ·
                  refine ⟨14515480100110378590394193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38707946933627676241051181 14515480100110378590394193)
                  ·
                    refine ⟨10886610075082783942795645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14515480100110378590394193 10886610075082783942795645)
                    ·
                      refine ⟨4082478778156043978548367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10886610075082783942795645 4082478778156043978548367)
                      ·
                        rfl

theorem cell23_7950599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_7950599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7950599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7950599 prefixEnd_7950599 := by exact prefixLift 7950599
  have htrace : WordTrace (prefixWord ++ tailWord_7950599) baseStart_7950599 baseEnd_7950599 := by
    simpa [prefixWord, tailWord_7950599, baseEnd_7950599] using wordTrace_append hprefix tailTrace_7950599
  have hstable : (prefixWord ++ tailWord_7950599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7950599).length < 2 ^ (prefixWord ++ tailWord_7950599).sum := by decide
  have hdescent : baseEnd_7950599 < baseStart_7950599 := by decide
  rcases family_descends (prefixWord ++ tailWord_7950599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7950635 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 1, 10, 2]
def baseStart_7950635 : Nat := 118140960795 + 7950635 * 2 ^ 59
def prefixEnd_7950635 : Nat := 4983230072969 + 3 ^ 40 * 7950635 * 2
def baseEnd_7950635 : Nat := 4082497263459605837698201

theorem tailTrace_7950635 : CollatzResearch.WordTrace tailWord_7950635 prefixEnd_7950635 4082497263459605837698201 := by
  unfold tailWord_7950635
  simp only [CollatzResearch.WordTrace]
  refine ⟨289983481551214730198325359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193322321034143153465550239 289983481551214730198325359)
  ·
    refine ⟨434975222326822095297488039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289983481551214730198325359 434975222326822095297488039)
    ·
      refine ⟨652462833490233142946232059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434975222326822095297488039 652462833490233142946232059)
      ·
        refine ⟨978694250235349714419348089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 652462833490233142946232059 978694250235349714419348089)
        ·
          refine ⟨734020687676512285814511067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 978694250235349714419348089 734020687676512285814511067)
          ·
            refine ⟨1101031031514768428721766601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 734020687676512285814511067 1101031031514768428721766601)
            ·
              refine ⟨825773273636076321541324951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1101031031514768428721766601 825773273636076321541324951)
              ·
                refine ⟨1238659910454114482311987427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 825773273636076321541324951 1238659910454114482311987427)
                ·
                  refine ⟨1857989865681171723467981141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1238659910454114482311987427 1857989865681171723467981141)
                  ·
                    refine ⟨5443329684612807783597601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 1857989865681171723467981141 5443329684612807783597601)
                    ·
                      refine ⟨4082497263459605837698201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5443329684612807783597601 4082497263459605837698201)
                      ·
                        rfl

theorem cell23_7950635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 10, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 10, 2].length) (baseStart_7950635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7950635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7950635 prefixEnd_7950635 := by exact prefixLift 7950635
  have htrace : WordTrace (prefixWord ++ tailWord_7950635) baseStart_7950635 baseEnd_7950635 := by
    simpa [prefixWord, tailWord_7950635, baseEnd_7950635] using wordTrace_append hprefix tailTrace_7950635
  have hstable : (prefixWord ++ tailWord_7950635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7950635).length < 2 ^ (prefixWord ++ tailWord_7950635).sum := by decide
  have hdescent : baseEnd_7950635 < baseStart_7950635 := by decide
  rcases family_descends (prefixWord ++ tailWord_7950635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7950645 : List Nat := [1, 3, 3, 1, 2, 1, 3, 1, 2, 6]
def baseStart_7950645 : Nat := 118140960795 + 7950645 * 2 ^ 59
def prefixEnd_7950645 : Nat := 4983230072969 + 3 ^ 40 * 7950645 * 2
def baseEnd_7950645 : Nat := 1360834132755383599524385

theorem tailTrace_7950645 : CollatzResearch.WordTrace tailWord_7950645 prefixEnd_7950645 1360834132755383599524385 := by
  unfold tailWord_7950645
  simp only [CollatzResearch.WordTrace]
  refine ⟨289983846281178501906189389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193322564187452334604126259 289983846281178501906189389)
  ·
    refine ⟨108743942355441938214821021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289983846281178501906189389 108743942355441938214821021)
    ·
      refine ⟨40778978383290726830557883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108743942355441938214821021 40778978383290726830557883)
      ·
        refine ⟨61168467574936090245836825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40778978383290726830557883 61168467574936090245836825)
        ·
          refine ⟨45876350681202067684377619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61168467574936090245836825 45876350681202067684377619)
          ·
            refine ⟨68814526021803101526566429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45876350681202067684377619 68814526021803101526566429)
            ·
              refine ⟨25805447258176163072462411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68814526021803101526566429 25805447258176163072462411)
              ·
                refine ⟨38708170887264244608693617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25805447258176163072462411 38708170887264244608693617)
                ·
                  refine ⟨29031128165448183456520213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38708170887264244608693617 29031128165448183456520213)
                  ·
                    refine ⟨1360834132755383599524385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29031128165448183456520213 1360834132755383599524385)
                    ·
                      rfl

theorem cell23_7950645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 1, 2, 6].length) (baseStart_7950645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7950645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7950645 prefixEnd_7950645 := by exact prefixLift 7950645
  have htrace : WordTrace (prefixWord ++ tailWord_7950645) baseStart_7950645 baseEnd_7950645 := by
    simpa [prefixWord, tailWord_7950645, baseEnd_7950645] using wordTrace_append hprefix tailTrace_7950645
  have hstable : (prefixWord ++ tailWord_7950645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7950645).length < 2 ^ (prefixWord ++ tailWord_7950645).sum := by decide
  have hdescent : baseEnd_7950645 < baseStart_7950645 := by decide
  rcases family_descends (prefixWord ++ tailWord_7950645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7950655 : List Nat := [1, 1, 2, 2, 4, 1, 1, 2, 2, 4, 3]
def baseStart_7950655 : Nat := 118140960795 + 7950655 * 2 ^ 59
def prefixEnd_7950655 : Nat := 4983230072969 + 3 ^ 40 * 7950655 * 2
def baseEnd_7950655 : Nat := 4082507533072695759448109

theorem tailTrace_7950655 : CollatzResearch.WordTrace tailWord_7950655 prefixEnd_7950655 4082507533072695759448109 := by
  unfold tailWord_7950655
  simp only [CollatzResearch.WordTrace]
  refine ⟨289984211011142273614053419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193322807340761515742702279 289984211011142273614053419)
  ·
    refine ⟨434976316516713410421080129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289984211011142273614053419 434976316516713410421080129)
    ·
      refine ⟨326232237387535057815810097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 434976316516713410421080129 326232237387535057815810097)
      ·
        refine ⟨244674178040651293361857573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326232237387535057815810097 244674178040651293361857573)
        ·
          refine ⟨45876408382622117505348295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 244674178040651293361857573 45876408382622117505348295)
          ·
            refine ⟨68814612573933176258022443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45876408382622117505348295 68814612573933176258022443)
            ·
              refine ⟨103221918860899764387033665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68814612573933176258022443 103221918860899764387033665)
              ·
                refine ⟨77416439145674823290275249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103221918860899764387033665 77416439145674823290275249)
                ·
                  refine ⟨58062329359256117467706437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77416439145674823290275249 58062329359256117467706437)
                  ·
                    refine ⟨10886686754860522025194957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58062329359256117467706437 10886686754860522025194957)
                    ·
                      refine ⟨4082507533072695759448109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10886686754860522025194957 4082507533072695759448109)
                      ·
                        rfl

theorem cell23_7950655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 2, 4, 3].length) (baseStart_7950655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7950655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7950655 prefixEnd_7950655 := by exact prefixLift 7950655
  have htrace : WordTrace (prefixWord ++ tailWord_7950655) baseStart_7950655 baseEnd_7950655 := by
    simpa [prefixWord, tailWord_7950655, baseEnd_7950655] using wordTrace_append hprefix tailTrace_7950655
  have hstable : (prefixWord ++ tailWord_7950655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7950655).length < 2 ^ (prefixWord ++ tailWord_7950655).sum := by decide
  have hdescent : baseEnd_7950655 < baseStart_7950655 := by decide
  rcases family_descends (prefixWord ++ tailWord_7950655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7950692 : List Nat := [2, 3, 1, 1, 3, 1, 1, 6, 5]
def baseStart_7950692 : Nat := 118140960795 + 7950692 * 2 ^ 59
def prefixEnd_7950692 : Nat := 4983230072969 + 3 ^ 40 * 7950692 * 2
def baseEnd_7950692 : Nat := 453614059095212457187271

theorem tailTrace_7950692 : CollatzResearch.WordTrace tailWord_7950692 prefixEnd_7950692 453614059095212457187271 := by
  unfold tailWord_7950692
  simp only [CollatzResearch.WordTrace]
  refine ⟨144992780256004114466575165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193323707008005485955433553 144992780256004114466575165)
  ·
    refine ⟨54372292596001542924965687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 144992780256004114466575165 54372292596001542924965687)
    ·
      refine ⟨81558438894002314387448531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54372292596001542924965687 81558438894002314387448531)
      ·
        refine ⟨122337658341003471581172797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81558438894002314387448531 122337658341003471581172797)
        ·
          refine ⟨45876621877876301842939799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122337658341003471581172797 45876621877876301842939799)
          ·
            refine ⟨68814932816814452764409699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45876621877876301842939799 68814932816814452764409699)
            ·
              refine ⟨103222399225221679146614549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68814932816814452764409699 103222399225221679146614549)
              ·
                refine ⟨4838549963682266209997557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 103222399225221679146614549 4838549963682266209997557)
                ·
                  refine ⟨453614059095212457187271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4838549963682266209997557 453614059095212457187271)
                  ·
                    rfl

theorem cell23_7950692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 6, 5].length) (baseStart_7950692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7950692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7950692 prefixEnd_7950692 := by exact prefixLift 7950692
  have htrace : WordTrace (prefixWord ++ tailWord_7950692) baseStart_7950692 baseEnd_7950692 := by
    simpa [prefixWord, tailWord_7950692, baseEnd_7950692] using wordTrace_append hprefix tailTrace_7950692
  have hstable : (prefixWord ++ tailWord_7950692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7950692).length < 2 ^ (prefixWord ++ tailWord_7950692).sum := by decide
  have hdescent : baseEnd_7950692 < baseStart_7950692 := by decide
  rcases family_descends (prefixWord ++ tailWord_7950692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7950809 : List Nat := [1, 2, 1, 2, 4, 1, 2, 3, 3, 1, 3]
def baseStart_7950809 : Nat := 118140960795 + 7950809 * 2 ^ 59
def prefixEnd_7950809 : Nat := 4983230072969 + 3 ^ 40 * 7950809 * 2
def baseEnd_7950809 : Nat := 4082586609093488156922401

theorem tailTrace_7950809 : CollatzResearch.WordTrace tailWord_7950809 prefixEnd_7950809 4082586609093488156922401 := by
  unfold tailWord_7950809
  simp only [CollatzResearch.WordTrace]
  refine ⟨289989827852584357915159481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193326551901722905276772987 289989827852584357915159481)
  ·
    refine ⟨217492370889438268436369611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 289989827852584357915159481 217492370889438268436369611)
    ·
      refine ⟨326238556334157402654554417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217492370889438268436369611 326238556334157402654554417)
      ·
        refine ⟨244678917250618051990915813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326238556334157402654554417 244678917250618051990915813)
        ·
          refine ⟨45877296984490884748296715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 244678917250618051990915813 45877296984490884748296715)
          ·
            refine ⟨68815945476736327122445073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45877296984490884748296715 68815945476736327122445073)
            ·
              refine ⟨51611959107552245341833805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68815945476736327122445073 51611959107552245341833805)
              ·
                refine ⟨19354484665332092003187677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51611959107552245341833805 19354484665332092003187677)
                ·
                  refine ⟨7257931749499534501195379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19354484665332092003187677 7257931749499534501195379)
                  ·
                    refine ⟨10886897624249301751793069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7257931749499534501195379 10886897624249301751793069)
                    ·
                      refine ⟨4082586609093488156922401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10886897624249301751793069 4082586609093488156922401)
                      ·
                        rfl

theorem cell23_7950809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 3, 3, 1, 3].length) (baseStart_7950809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7950809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7950809 prefixEnd_7950809 := by exact prefixLift 7950809
  have htrace : WordTrace (prefixWord ++ tailWord_7950809) baseStart_7950809 baseEnd_7950809 := by
    simpa [prefixWord, tailWord_7950809, baseEnd_7950809] using wordTrace_append hprefix tailTrace_7950809
  have hstable : (prefixWord ++ tailWord_7950809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7950809).length < 2 ^ (prefixWord ++ tailWord_7950809).sum := by decide
  have hdescent : baseEnd_7950809 < baseStart_7950809 := by decide
  rcases family_descends (prefixWord ++ tailWord_7950809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7950826 : List Nat := [3, 1, 3, 1, 3, 2, 1, 2, 3, 1, 3]
def baseStart_7950826 : Nat := 118140960795 + 7950826 * 2 ^ 59
def prefixEnd_7950826 : Nat := 4983230072969 + 3 ^ 40 * 7950826 * 2
def baseEnd_7950826 : Nat := 4082595338264614590409823

theorem tailTrace_7950826 : CollatzResearch.WordTrace tailWord_7950826 prefixEnd_7950826 4082595338264614590409823 := by
  unfold tailWord_7950826
  simp only [CollatzResearch.WordTrace]
  refine ⟨72497611973380692454632083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193326965262348513212352221 72497611973380692454632083)
  ·
    refine ⟨108746417960071038681948125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72497611973380692454632083 108746417960071038681948125)
    ·
      refine ⟨40779906735026639505730547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108746417960071038681948125 40779906735026639505730547)
      ·
        refine ⟨61169860102539959258595821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40779906735026639505730547 61169860102539959258595821)
        ·
          refine ⟨22938697538452484721973433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61169860102539959258595821 22938697538452484721973433)
          ·
            refine ⟨17204023153839363541480075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22938697538452484721973433 17204023153839363541480075)
            ·
              refine ⟨25806034730759045312220113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17204023153839363541480075 25806034730759045312220113)
              ·
                refine ⟨19354526048069283984165085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25806034730759045312220113 19354526048069283984165085)
                ·
                  refine ⟨7257947268025981494061907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19354526048069283984165085 7257947268025981494061907)
                  ·
                    refine ⟨10886920902038972241092861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7257947268025981494061907 10886920902038972241092861)
                    ·
                      refine ⟨4082595338264614590409823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10886920902038972241092861 4082595338264614590409823)
                      ·
                        rfl

theorem cell23_7950826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 2, 3, 1, 3].length) (baseStart_7950826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7950826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7950826 prefixEnd_7950826 := by exact prefixLift 7950826
  have htrace : WordTrace (prefixWord ++ tailWord_7950826) baseStart_7950826 baseEnd_7950826 := by
    simpa [prefixWord, tailWord_7950826, baseEnd_7950826] using wordTrace_append hprefix tailTrace_7950826
  have hstable : (prefixWord ++ tailWord_7950826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7950826).length < 2 ^ (prefixWord ++ tailWord_7950826).sum := by decide
  have hdescent : baseEnd_7950826 < baseStart_7950826 := by decide
  rcases family_descends (prefixWord ++ tailWord_7950826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7950829 : List Nat := [1, 5, 1, 3, 1, 1, 2, 1, 3, 5]
def baseStart_7950829 : Nat := 118140960795 + 7950829 * 2 ^ 59
def prefixEnd_7950829 : Nat := 4983230072969 + 3 ^ 40 * 7950829 * 2
def baseEnd_7950829 : Nat := 1360865626235526026224103

theorem tailTrace_7950829 : CollatzResearch.WordTrace tailWord_7950829 prefixEnd_7950829 1360865626235526026224103 := by
  unfold tailWord_7950829
  simp only [CollatzResearch.WordTrace]
  refine ⟨289990557312511901330887541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193327038208341267553925027 289990557312511901330887541)
  ·
    refine ⟨27186614748047990749770707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 289990557312511901330887541 27186614748047990749770707)
    ·
      refine ⟨40779922122071986124656061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27186614748047990749770707 40779922122071986124656061)
      ·
        refine ⟨15292470795776994796746023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40779922122071986124656061 15292470795776994796746023)
        ·
          refine ⟨22938706193665492195119035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15292470795776994796746023 22938706193665492195119035)
          ·
            refine ⟨34408059290498238292678553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22938706193665492195119035 34408059290498238292678553)
            ·
              refine ⟨25806044467873678719508915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34408059290498238292678553 25806044467873678719508915)
              ·
                refine ⟨38709066701810518079263373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25806044467873678719508915 38709066701810518079263373)
                ·
                  refine ⟨14515900013178944279723765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38709066701810518079263373 14515900013178944279723765)
                  ·
                    refine ⟨1360865626235526026224103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14515900013178944279723765 1360865626235526026224103)
                    ·
                      rfl

theorem cell23_7950829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 1, 3, 5].length) (baseStart_7950829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7950829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7950829 prefixEnd_7950829 := by exact prefixLift 7950829
  have htrace : WordTrace (prefixWord ++ tailWord_7950829) baseStart_7950829 baseEnd_7950829 := by
    simpa [prefixWord, tailWord_7950829, baseEnd_7950829] using wordTrace_append hprefix tailTrace_7950829
  have hstable : (prefixWord ++ tailWord_7950829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7950829).length < 2 ^ (prefixWord ++ tailWord_7950829).sum := by decide
  have hdescent : baseEnd_7950829 < baseStart_7950829 := by decide
  rcases family_descends (prefixWord ++ tailWord_7950829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7950832 : List Nat := [2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 4]
def baseStart_7950832 : Nat := 118140960795 + 7950832 * 2 ^ 59
def prefixEnd_7950832 : Nat := 4983230072969 + 3 ^ 40 * 7950832 * 2
def baseEnd_7950832 : Nat := 4082598419148541566934795

theorem tailTrace_7950832 : CollatzResearch.WordTrace tailWord_7950832 prefixEnd_7950832 4082598419148541566934795 := by
  unfold tailWord_7950832
  simp only [CollatzResearch.WordTrace]
  refine ⟨144995333365750516421623375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193327111154334021895497833 144995333365750516421623375)
  ·
    refine ⟨217493000048625774632435063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144995333365750516421623375 217493000048625774632435063)
    ·
      refine ⟨326239500072938661948652595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217493000048625774632435063 326239500072938661948652595)
      ·
        refine ⟨489359250109407992922978893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326239500072938661948652595 489359250109407992922978893)
        ·
          refine ⟨183509718791027997346117085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 489359250109407992922978893 183509718791027997346117085)
          ·
            refine ⟨68816144546635499004793907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183509718791027997346117085 68816144546635499004793907)
            ·
              refine ⟨103224216819953248507190861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68816144546635499004793907 103224216819953248507190861)
              ·
                refine ⟨38709081307482468190196573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103224216819953248507190861 38709081307482468190196573)
                ·
                  refine ⟨14515905490305925571323715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38709081307482468190196573 14515905490305925571323715)
                  ·
                    refine ⟨21773858235458888356985573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14515905490305925571323715 21773858235458888356985573)
                    ·
                      refine ⟨4082598419148541566934795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21773858235458888356985573 4082598419148541566934795)
                      ·
                        rfl

theorem cell23_7950832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 4].length) (baseStart_7950832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7950832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7950832 prefixEnd_7950832 := by exact prefixLift 7950832
  have htrace : WordTrace (prefixWord ++ tailWord_7950832) baseStart_7950832 baseEnd_7950832 := by
    simpa [prefixWord, tailWord_7950832, baseEnd_7950832] using wordTrace_append hprefix tailTrace_7950832
  have hstable : (prefixWord ++ tailWord_7950832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7950832).length < 2 ^ (prefixWord ++ tailWord_7950832).sum := by decide
  have hdescent : baseEnd_7950832 < baseStart_7950832 := by decide
  rcases family_descends (prefixWord ++ tailWord_7950832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7950859 : List Nat := [1, 1, 1, 1, 7, 2, 1, 1, 4, 4]
def baseStart_7950859 : Nat := 118140960795 + 7950859 * 2 ^ 59
def prefixEnd_7950859 : Nat := 4983230072969 + 3 ^ 40 * 7950859 * 2
def baseEnd_7950859 : Nat := 1360870761042070987099057

theorem tailTrace_7950859 : CollatzResearch.WordTrace tailWord_7950859 prefixEnd_7950859 1360870761042070987099057 := by
  unfold tailWord_7950859
  simp only [CollatzResearch.WordTrace]
  refine ⟨289991651502403216454479631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193327767668268810969653087 289991651502403216454479631)
  ·
    refine ⟨434987477253604824681719447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289991651502403216454479631 434987477253604824681719447)
    ·
      refine ⟨652481215880407237022579171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434987477253604824681719447 652481215880407237022579171)
      ·
        refine ⟨978721823820610855533868757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 652481215880407237022579171 978721823820610855533868757)
        ·
          refine ⟨22938792745795566926575049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 978721823820610855533868757 22938792745795566926575049)
          ·
            refine ⟨17204094559346675194931287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22938792745795566926575049 17204094559346675194931287)
            ·
              refine ⟨25806141839020012792396931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17204094559346675194931287 25806141839020012792396931)
              ·
                refine ⟨38709212758530019188595397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25806141839020012792396931 38709212758530019188595397)
                ·
                  refine ⟨7257977392224378597861637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38709212758530019188595397 7257977392224378597861637)
                  ·
                    refine ⟨1360870761042070987099057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7257977392224378597861637 1360870761042070987099057)
                    ·
                      rfl

theorem cell23_7950859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 1, 4, 4].length) (baseStart_7950859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7950859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7950859 prefixEnd_7950859 := by exact prefixLift 7950859
  have htrace : WordTrace (prefixWord ++ tailWord_7950859) baseStart_7950859 baseEnd_7950859 := by
    simpa [prefixWord, tailWord_7950859, baseEnd_7950859] using wordTrace_append hprefix tailTrace_7950859
  have hstable : (prefixWord ++ tailWord_7950859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7950859).length < 2 ^ (prefixWord ++ tailWord_7950859).sum := by decide
  have hdescent : baseEnd_7950859 < baseStart_7950859 := by decide
  rcases family_descends (prefixWord ++ tailWord_7950859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7950899 : List Nat := [1, 1, 1, 2, 4, 2, 1, 1, 6, 1, 3]
def baseStart_7950899 : Nat := 118140960795 + 7950899 * 2 ^ 59
def prefixEnd_7950899 : Nat := 4983230072969 + 3 ^ 40 * 7950899 * 2
def baseEnd_7950899 : Nat := 4082632822352392804796987

theorem tailTrace_7950899 : CollatzResearch.WordTrace tailWord_7950899 prefixEnd_7950899 4082632822352392804796987 := by
  unfold tailWord_7950899
  simp only [CollatzResearch.WordTrace]
  refine ⟨289993110422258303285935751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193328740281505535523957167 289993110422258303285935751)
  ·
    refine ⟨434989665633387454928903627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289993110422258303285935751 434989665633387454928903627)
    ·
      refine ⟨652484498450081182393355441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434989665633387454928903627 652484498450081182393355441)
      ·
        refine ⟨489363373837560886795016581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 652484498450081182393355441 489363373837560886795016581)
        ·
          refine ⟨91755632594542666274065609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 489363373837560886795016581 91755632594542666274065609)
          ·
            refine ⟨68816724445906999705549207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91755632594542666274065609 68816724445906999705549207)
            ·
              refine ⟨103225086668860499558323811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68816724445906999705549207 103225086668860499558323811)
              ·
                refine ⟨154837630003290749337485717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103225086668860499558323811 154837630003290749337485717)
                ·
                  refine ⟨7258013906404253875194643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 154837630003290749337485717 7258013906404253875194643)
                  ·
                    refine ⟨10887020859606380812791965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7258013906404253875194643 10887020859606380812791965)
                    ·
                      refine ⟨4082632822352392804796987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10887020859606380812791965 4082632822352392804796987)
                      ·
                        rfl

theorem cell23_7950899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 6, 1, 3].length) (baseStart_7950899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7950899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7950899 prefixEnd_7950899 := by exact prefixLift 7950899
  have htrace : WordTrace (prefixWord ++ tailWord_7950899) baseStart_7950899 baseEnd_7950899 := by
    simpa [prefixWord, tailWord_7950899, baseEnd_7950899] using wordTrace_append hprefix tailTrace_7950899
  have hstable : (prefixWord ++ tailWord_7950899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7950899).length < 2 ^ (prefixWord ++ tailWord_7950899).sum := by decide
  have hdescent : baseEnd_7950899 < baseStart_7950899 := by decide
  rcases family_descends (prefixWord ++ tailWord_7950899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7950933 : List Nat := [1, 3, 2, 2, 1, 1, 6, 1, 2, 1, 3]
def baseStart_7950933 : Nat := 118140960795 + 7950933 * 2 ^ 59
def prefixEnd_7950933 : Nat := 4983230072969 + 3 ^ 40 * 7950933 * 2
def baseEnd_7950933 : Nat := 4082650280694645671771831

theorem tailTrace_7950933 : CollatzResearch.WordTrace tailWord_7950933 prefixEnd_7950933 4082650280694645671771831 := by
  unfold tailWord_7950933
  simp only [CollatzResearch.WordTrace]
  refine ⟨289994350504135127092673453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193329567002756751395115635 289994350504135127092673453)
  ·
    refine ⟨108747881439050672659752545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 289994350504135127092673453 108747881439050672659752545)
    ·
      refine ⟨81560911079288004494814409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108747881439050672659752545 81560911079288004494814409)
      ·
        refine ⟨61170683309466003371110807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81560911079288004494814409 61170683309466003371110807)
        ·
          refine ⟨91756024964199005056666211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61170683309466003371110807 91756024964199005056666211)
          ·
            refine ⟨137634037446298507584999317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91756024964199005056666211 137634037446298507584999317)
            ·
              refine ⟨6451595505295242543046843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 137634037446298507584999317 6451595505295242543046843)
              ·
                refine ⟨9677393257942863814570265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6451595505295242543046843 9677393257942863814570265)
                ·
                  refine ⟨7258044943457147860927699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9677393257942863814570265 7258044943457147860927699)
                  ·
                    refine ⟨10887067415185721791391549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7258044943457147860927699 10887067415185721791391549)
                    ·
                      refine ⟨4082650280694645671771831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10887067415185721791391549 4082650280694645671771831)
                      ·
                        rfl

theorem cell23_7950933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 6, 1, 2, 1, 3].length) (baseStart_7950933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7950933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7950933 prefixEnd_7950933 := by exact prefixLift 7950933
  have htrace : WordTrace (prefixWord ++ tailWord_7950933) baseStart_7950933 baseEnd_7950933 := by
    simpa [prefixWord, tailWord_7950933, baseEnd_7950933] using wordTrace_append hprefix tailTrace_7950933
  have hstable : (prefixWord ++ tailWord_7950933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7950933).length < 2 ^ (prefixWord ++ tailWord_7950933).sum := by decide
  have hdescent : baseEnd_7950933 < baseStart_7950933 := by decide
  rcases family_descends (prefixWord ++ tailWord_7950933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7950956 : List Nat := [2, 2, 1, 1, 3, 1, 2, 1, 6, 2, 2]
def baseStart_7950956 : Nat := 118140960795 + 7950956 * 2 ^ 59
def prefixEnd_7950956 : Nat := 4983230072969 + 3 ^ 40 * 7950956 * 2
def baseEnd_7950956 : Nat := 4082662090749699081784225

theorem tailTrace_7950956 : CollatzResearch.WordTrace tailWord_7950956 prefixEnd_7950956 4082662090749699081784225 := by
  unfold tailWord_7950956
  simp only [CollatzResearch.WordTrace]
  refine ⟨144997594691525901010380361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193330126255367868013840481 144997594691525901010380361)
  ·
    refine ⟨108748196018644425757785271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144997594691525901010380361 108748196018644425757785271)
    ·
      refine ⟨163122294027966638636677907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108748196018644425757785271 163122294027966638636677907)
      ·
        refine ⟨244683441041949957955016861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163122294027966638636677907 244683441041949957955016861)
        ·
          refine ⟨91756290390731234233131323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 244683441041949957955016861 91756290390731234233131323)
          ·
            refine ⟨137634435586096851349696985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91756290390731234233131323 137634435586096851349696985)
            ·
              refine ⟨103225826689572638512272739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137634435586096851349696985 103225826689572638512272739)
              ·
                refine ⟨154838740034358957768409109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103225826689572638512272739 154838740034358957768409109)
                ·
                  refine ⟨7258065939110576145394177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 154838740034358957768409109 7258065939110576145394177)
                  ·
                    refine ⟨5443549454332932109045633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7258065939110576145394177 5443549454332932109045633)
                    ·
                      refine ⟨4082662090749699081784225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5443549454332932109045633 4082662090749699081784225)
                      ·
                        rfl

theorem cell23_7950956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 2, 2].length) (baseStart_7950956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7950956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7950956 prefixEnd_7950956 := by exact prefixLift 7950956
  have htrace : WordTrace (prefixWord ++ tailWord_7950956) baseStart_7950956 baseEnd_7950956 := by
    simpa [prefixWord, tailWord_7950956, baseEnd_7950956] using wordTrace_append hprefix tailTrace_7950956
  have hstable : (prefixWord ++ tailWord_7950956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7950956).length < 2 ^ (prefixWord ++ tailWord_7950956).sum := by decide
  have hdescent : baseEnd_7950956 < baseStart_7950956 := by decide
  rcases family_descends (prefixWord ++ tailWord_7950956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7950960 : List Nat := [2, 1, 1, 1, 7, 1, 3, 1, 1, 3, 2]
def baseStart_7950960 : Nat := 118140960795 + 7950960 * 2 ^ 59
def prefixEnd_7950960 : Nat := 4983230072969 + 3 ^ 40 * 7950960 * 2
def baseEnd_7950960 : Nat := 4082664144672317066134207

theorem tailTrace_7950960 : CollatzResearch.WordTrace tailWord_7950960 prefixEnd_7950960 4082664144672317066134207 := by
  unfold tailWord_7950960
  simp only [CollatzResearch.WordTrace]
  refine ⟨144997667637518655351953167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193330223516691540469270889 144997667637518655351953167)
  ·
    refine ⟨217496501456277983027929751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 144997667637518655351953167 217496501456277983027929751)
    ·
      refine ⟨326244752184416974541894627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217496501456277983027929751 326244752184416974541894627)
      ·
        refine ⟨489367128276625461812841941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326244752184416974541894627 489367128276625461812841941)
        ·
          refine ⟨11469542068983409261238483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 489367128276625461812841941 11469542068983409261238483)
          ·
            refine ⟨17204313103475113891857725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11469542068983409261238483 17204313103475113891857725)
            ·
              refine ⟨6451617413803167709446647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17204313103475113891857725 6451617413803167709446647)
              ·
                refine ⟨9677426120704751564169971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6451617413803167709446647 9677426120704751564169971)
                ·
                  refine ⟨14516139181057127346254957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9677426120704751564169971 14516139181057127346254957)
                  ·
                    refine ⟨5443552192896422754845609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14516139181057127346254957 5443552192896422754845609)
                    ·
                      refine ⟨4082664144672317066134207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5443552192896422754845609 4082664144672317066134207)
                      ·
                        rfl

theorem cell23_7950960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 3, 1, 1, 3, 2].length) (baseStart_7950960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7950960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7950960 prefixEnd_7950960 := by exact prefixLift 7950960
  have htrace : WordTrace (prefixWord ++ tailWord_7950960) baseStart_7950960 baseEnd_7950960 := by
    simpa [prefixWord, tailWord_7950960, baseEnd_7950960] using wordTrace_append hprefix tailTrace_7950960
  have hstable : (prefixWord ++ tailWord_7950960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7950960).length < 2 ^ (prefixWord ++ tailWord_7950960).sum := by decide
  have hdescent : baseEnd_7950960 < baseStart_7950960 := by decide
  rcases family_descends (prefixWord ++ tailWord_7950960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7950972 : List Nat := [2, 2, 2, 1, 1, 2, 2, 1, 1, 2, 7]
def baseStart_7950972 : Nat := 118140960795 + 7950972 * 2 ^ 59
def prefixEnd_7950972 : Nat := 4983230072969 + 3 ^ 40 * 7950972 * 2
def baseEnd_7950972 : Nat := 4082670306440171019184151

theorem tailTrace_7950972 : CollatzResearch.WordTrace tailWord_7950972 prefixEnd_7950972 4082670306440171019184151 := by
  unfold tailWord_7950972
  simp only [CollatzResearch.WordTrace]
  refine ⟨144997886475496918376671585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193330515300662557835562113 144997886475496918376671585)
  ·
    refine ⟨108748414856622688782503689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144997886475496918376671585 108748414856622688782503689)
    ·
      refine ⟨81561311142467016586877767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108748414856622688782503689 81561311142467016586877767)
      ·
        refine ⟨122341966713700524880316651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81561311142467016586877767 122341966713700524880316651)
        ·
          refine ⟨183512950070550787320474977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122341966713700524880316651 183512950070550787320474977)
          ·
            refine ⟨137634712552913090490356233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183512950070550787320474977 137634712552913090490356233)
            ·
              refine ⟨103226034414684817867767175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137634712552913090490356233 103226034414684817867767175)
              ·
                refine ⟨154839051622027226801650763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103226034414684817867767175 154839051622027226801650763)
                ·
                  refine ⟨232258577433040840202476145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 154839051622027226801650763 232258577433040840202476145)
                  ·
                    refine ⟨174193933074780630151857109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 232258577433040840202476145 174193933074780630151857109)
                    ·
                      refine ⟨4082670306440171019184151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 174193933074780630151857109 4082670306440171019184151)
                      ·
                        rfl

theorem cell23_7950972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_7950972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7950972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7950972 prefixEnd_7950972 := by exact prefixLift 7950972
  have htrace : WordTrace (prefixWord ++ tailWord_7950972) baseStart_7950972 baseEnd_7950972 := by
    simpa [prefixWord, tailWord_7950972, baseEnd_7950972] using wordTrace_append hprefix tailTrace_7950972
  have hstable : (prefixWord ++ tailWord_7950972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7950972).length < 2 ^ (prefixWord ++ tailWord_7950972).sum := by decide
  have hdescent : baseEnd_7950972 < baseStart_7950972 := by decide
  rcases family_descends (prefixWord ++ tailWord_7950972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7950986 : List Nat := [3, 1, 2, 3, 3, 1, 1, 1, 2, 2, 4]
def baseStart_7950986 : Nat := 118140960795 + 7950986 * 2 ^ 59
def prefixEnd_7950986 : Nat := 4983230072969 + 3 ^ 40 * 7950986 * 2
def baseEnd_7950986 : Nat := 4082677495169333964409087

theorem tailTrace_7950986 : CollatzResearch.WordTrace tailWord_7950986 prefixEnd_7950986 4082677495169333964409087 := by
  unfold tailWord_7950986
  simp only [CollatzResearch.WordTrace]
  refine ⟨72499070893235779286088203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193330855715295411429568541 72499070893235779286088203)
  ·
    refine ⟨108748606339853668929132305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72499070893235779286088203 108748606339853668929132305)
    ·
      refine ⟨81561454754890251696849229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108748606339853668929132305 81561454754890251696849229)
      ·
        refine ⟨30585545533083844386318461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81561454754890251696849229 30585545533083844386318461)
        ·
          refine ⟨11469579574906441644869423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30585545533083844386318461 11469579574906441644869423)
          ·
            refine ⟨17204369362359662467304135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11469579574906441644869423 17204369362359662467304135)
            ·
              refine ⟨25806554043539493700956203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17204369362359662467304135 25806554043539493700956203)
              ·
                refine ⟨38709831065309240551434305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25806554043539493700956203 38709831065309240551434305)
                ·
                  refine ⟨29032373298981930413575729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38709831065309240551434305 29032373298981930413575729)
                  ·
                    refine ⟨21774279974236447810181797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29032373298981930413575729 21774279974236447810181797)
                    ·
                      refine ⟨4082677495169333964409087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21774279974236447810181797 4082677495169333964409087)
                      ·
                        rfl

theorem cell23_7950986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_7950986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7950986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7950986 prefixEnd_7950986 := by exact prefixLift 7950986
  have htrace : WordTrace (prefixWord ++ tailWord_7950986) baseStart_7950986 baseEnd_7950986 := by
    simpa [prefixWord, tailWord_7950986, baseEnd_7950986] using wordTrace_append hprefix tailTrace_7950986
  have hstable : (prefixWord ++ tailWord_7950986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7950986).length < 2 ^ (prefixWord ++ tailWord_7950986).sum := by decide
  have hdescent : baseEnd_7950986 < baseStart_7950986 := by decide
  rcases family_descends (prefixWord ++ tailWord_7950986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7950996 : List Nat := [2, 4, 2, 2, 1, 2, 1, 2, 7]
def baseStart_7950996 : Nat := 118140960795 + 7950996 * 2 ^ 59
def prefixEnd_7950996 : Nat := 4983230072969 + 3 ^ 40 * 7950996 * 2
def baseEnd_7950996 : Nat := 453631403330653213920449

theorem tailTrace_7950996 : CollatzResearch.WordTrace tailWord_7950996 prefixEnd_7950996 453631403330653213920449 := by
  unfold tailWord_7950996
  simp only [CollatzResearch.WordTrace]
  refine ⟨144998324151453444426108421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193331098868604592568144561 144998324151453444426108421)
  ·
    refine ⟨27187185778397520829895329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 144998324151453444426108421 27187185778397520829895329)
    ·
      refine ⟨20390389333798140622421497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27187185778397520829895329 20390389333798140622421497)
      ·
        refine ⟨15292792000348605466816123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20390389333798140622421497 15292792000348605466816123)
        ·
          refine ⟨22939188000522908200224185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15292792000348605466816123 22939188000522908200224185)
          ·
            refine ⟨17204391000392181150168139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22939188000522908200224185 17204391000392181150168139)
            ·
              refine ⟨25806586500588271725252209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17204391000392181150168139 25806586500588271725252209)
              ·
                refine ⟨19354939875441203793939157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25806586500588271725252209 19354939875441203793939157)
                ·
                  refine ⟨453631403330653213920449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19354939875441203793939157 453631403330653213920449)
                  ·
                    rfl

theorem cell23_7950996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 2, 7].length) (baseStart_7950996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7950996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7950996 prefixEnd_7950996 := by exact prefixLift 7950996
  have htrace : WordTrace (prefixWord ++ tailWord_7950996) baseStart_7950996 baseEnd_7950996 := by
    simpa [prefixWord, tailWord_7950996, baseEnd_7950996] using wordTrace_append hprefix tailTrace_7950996
  have hstable : (prefixWord ++ tailWord_7950996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7950996).length < 2 ^ (prefixWord ++ tailWord_7950996).sum := by decide
  have hdescent : baseEnd_7950996 < baseStart_7950996 := by decide
  rcases family_descends (prefixWord ++ tailWord_7950996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7951006 : List Nat := [4, 3, 1, 1, 1, 1, 1, 2, 1, 5, 3]
def baseStart_7951006 : Nat := 118140960795 + 7951006 * 2 ^ 59
def prefixEnd_7951006 : Nat := 4983230072969 + 3 ^ 40 * 7951006 * 2
def baseEnd_7951006 : Nat := 4082687764782423886158995

theorem tailTrace_7951006 : CollatzResearch.WordTrace tailWord_7951006 prefixEnd_7951006 4082687764782423886158995 := by
  unfold tailWord_7951006
  simp only [CollatzResearch.WordTrace]
  refine ⟨36249626629108832570010109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193331342021913773706720581 36249626629108832570010109)
  ·
    refine ⟨13593609985915812213753791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36249626629108832570010109 13593609985915812213753791)
    ·
      refine ⟨20390414978873718320630687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13593609985915812213753791 20390414978873718320630687)
      ·
        refine ⟨30585622468310577480946031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20390414978873718320630687 30585622468310577480946031)
        ·
          refine ⟨45878433702465866221419047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30585622468310577480946031 45878433702465866221419047)
          ·
            refine ⟨68817650553698799332128571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45878433702465866221419047 68817650553698799332128571)
            ·
              refine ⟨103226475830548198998192857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68817650553698799332128571 103226475830548198998192857)
              ·
                refine ⟨77419856872911149248644643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103226475830548198998192857 77419856872911149248644643)
                ·
                  refine ⟨116129785309366723872966965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77419856872911149248644643 116129785309366723872966965)
                  ·
                    refine ⟨10887167372753130363090653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 116129785309366723872966965 10887167372753130363090653)
                    ·
                      refine ⟨4082687764782423886158995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10887167372753130363090653 4082687764782423886158995)
                      ·
                        rfl

theorem cell23_7951006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_7951006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7951006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7951006 prefixEnd_7951006 := by exact prefixLift 7951006
  have htrace : WordTrace (prefixWord ++ tailWord_7951006) baseStart_7951006 baseEnd_7951006 := by
    simpa [prefixWord, tailWord_7951006, baseEnd_7951006] using wordTrace_append hprefix tailTrace_7951006
  have hstable : (prefixWord ++ tailWord_7951006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7951006).length < 2 ^ (prefixWord ++ tailWord_7951006).sum := by decide
  have hdescent : baseEnd_7951006 < baseStart_7951006 := by decide
  rcases family_descends (prefixWord ++ tailWord_7951006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7951066 : List Nat := [3, 1, 1, 2, 2, 2, 2, 3, 2, 2, 3]
def baseStart_7951066 : Nat := 118140960795 + 7951066 * 2 ^ 59
def prefixEnd_7951066 : Nat := 4983230072969 + 3 ^ 40 * 7951066 * 2
def baseEnd_7951066 : Nat := 4082718573621693651408719

theorem tailTrace_7951066 : CollatzResearch.WordTrace tailWord_7951066 prefixEnd_7951066 4082718573621693651408719 := by
  unfold tailWord_7951066
  simp only [CollatzResearch.WordTrace]
  refine ⟨72499800353163322701816263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193332800941768860538176701 72499800353163322701816263)
  ·
    refine ⟨108749700529744984052724395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72499800353163322701816263 108749700529744984052724395)
    ·
      refine ⟨163124550794617476079086593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108749700529744984052724395 163124550794617476079086593)
      ·
        refine ⟨122343413095963107059314945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163124550794617476079086593 122343413095963107059314945)
        ·
          refine ⟨91757559821972330294486209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122343413095963107059314945 91757559821972330294486209)
          ·
            refine ⟨68818169866479247720864657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91757559821972330294486209 68818169866479247720864657)
            ·
              refine ⟨51613627399859435790648493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68818169866479247720864657 51613627399859435790648493)
              ·
                refine ⟨19355110274947288421493185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51613627399859435790648493 19355110274947288421493185)
                ·
                  refine ⟨14516332706210466316119889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19355110274947288421493185 14516332706210466316119889)
                  ·
                    refine ⟨10887249529657849737089917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14516332706210466316119889 10887249529657849737089917)
                    ·
                      refine ⟨4082718573621693651408719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10887249529657849737089917 4082718573621693651408719)
                      ·
                        rfl

theorem cell23_7951066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 3, 2, 2, 3].length) (baseStart_7951066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7951066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7951066 prefixEnd_7951066 := by exact prefixLift 7951066
  have htrace : WordTrace (prefixWord ++ tailWord_7951066) baseStart_7951066 baseEnd_7951066 := by
    simpa [prefixWord, tailWord_7951066, baseEnd_7951066] using wordTrace_append hprefix tailTrace_7951066
  have hstable : (prefixWord ++ tailWord_7951066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7951066).length < 2 ^ (prefixWord ++ tailWord_7951066).sum := by decide
  have hdescent : baseEnd_7951066 < baseStart_7951066 := by decide
  rcases family_descends (prefixWord ++ tailWord_7951066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7951123 : List Nat := [1, 1, 1, 2, 1, 3, 6, 1, 2, 3, 2]
def baseStart_7951123 : Nat := 118140960795 + 7951123 * 2 ^ 59
def prefixEnd_7951123 : Nat := 4983230072969 + 3 ^ 40 * 7951123 * 2
def baseEnd_7951123 : Nat := 4082747842018999928395957

theorem tailTrace_7951123 : CollatzResearch.WordTrace tailWord_7951123 prefixEnd_7951123 4082747842018999928395957 := by
  unfold tailWord_7951123
  simp only [CollatzResearch.WordTrace]
  refine ⟨290001280373446789542090023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193334186915631193028060015 290001280373446789542090023)
  ·
    refine ⟨435001920560170184313135035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290001280373446789542090023 435001920560170184313135035)
    ·
      refine ⟨652502880840255276469702553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435001920560170184313135035 652502880840255276469702553)
      ·
        refine ⟨489377160630191457352276915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 652502880840255276469702553 489377160630191457352276915)
        ·
          refine ⟨734065740945287186028415373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 489377160630191457352276915 734065740945287186028415373)
          ·
            refine ⟨275274652854482694760655765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 734065740945287186028415373 275274652854482694760655765)
            ·
              refine ⟨12903499352553876316905739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 275274652854482694760655765 12903499352553876316905739)
              ·
                refine ⟨19355249028830814475358609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12903499352553876316905739 19355249028830814475358609)
                ·
                  refine ⟨14516436771623110856518957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19355249028830814475358609 14516436771623110856518957)
                  ·
                    refine ⟨5443663789358666571194609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14516436771623110856518957 5443663789358666571194609)
                    ·
                      refine ⟨4082747842018999928395957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5443663789358666571194609 4082747842018999928395957)
                      ·
                        rfl

theorem cell23_7951123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 1, 2, 3, 2].length) (baseStart_7951123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7951123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7951123 prefixEnd_7951123 := by exact prefixLift 7951123
  have htrace : WordTrace (prefixWord ++ tailWord_7951123) baseStart_7951123 baseEnd_7951123 := by
    simpa [prefixWord, tailWord_7951123, baseEnd_7951123] using wordTrace_append hprefix tailTrace_7951123
  have hstable : (prefixWord ++ tailWord_7951123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7951123).length < 2 ^ (prefixWord ++ tailWord_7951123).sum := by decide
  have hdescent : baseEnd_7951123 < baseStart_7951123 := by decide
  rcases family_descends (prefixWord ++ tailWord_7951123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7951130 : List Nat := [3, 1, 1, 3, 2, 1, 2, 5, 1, 1, 3]
def baseStart_7951130 : Nat := 118140960795 + 7951130 * 2 ^ 59
def prefixEnd_7951130 : Nat := 4983230072969 + 3 ^ 40 * 7951130 * 2
def baseEnd_7951130 : Nat := 4082751436383581401008425

theorem tailTrace_7951130 : CollatzResearch.WordTrace tailWord_7951130 prefixEnd_7951130 4082751436383581401008425 := by
  unfold tailWord_7951130
  simp only [CollatzResearch.WordTrace]
  refine ⟨72500383921105357434398711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193334357122947619825063229 72500383921105357434398711)
  ·
    refine ⟨108750575881658036151598067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72500383921105357434398711 108750575881658036151598067)
    ·
      refine ⟨163125863822487054227397101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108750575881658036151598067 163125863822487054227397101)
      ·
        refine ⟨61172198933432645335273913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163125863822487054227397101 61172198933432645335273913)
        ·
          refine ⟨45879149200074484001455435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61172198933432645335273913 45879149200074484001455435)
          ·
            refine ⟨68818723800111726002183153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45879149200074484001455435 68818723800111726002183153)
            ·
              refine ⟨51614042850083794501637365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68818723800111726002183153 51614042850083794501637365)
              ·
                refine ⟨4838816517195355734528503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51614042850083794501637365 4838816517195355734528503)
                ·
                  refine ⟨7258224775793033601792755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4838816517195355734528503 7258224775793033601792755)
                  ·
                    refine ⟨10887337163689550402689133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7258224775793033601792755 10887337163689550402689133)
                    ·
                      refine ⟨4082751436383581401008425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10887337163689550402689133 4082751436383581401008425)
                      ·
                        rfl

theorem cell23_7951130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 5, 1, 1, 3].length) (baseStart_7951130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7951130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7951130 prefixEnd_7951130 := by exact prefixLift 7951130
  have htrace : WordTrace (prefixWord ++ tailWord_7951130) baseStart_7951130 baseEnd_7951130 := by
    simpa [prefixWord, tailWord_7951130, baseEnd_7951130] using wordTrace_append hprefix tailTrace_7951130
  have hstable : (prefixWord ++ tailWord_7951130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7951130).length < 2 ^ (prefixWord ++ tailWord_7951130).sum := by decide
  have hdescent : baseEnd_7951130 < baseStart_7951130 := by decide
  rcases family_descends (prefixWord ++ tailWord_7951130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7951176 : List Nat := [2, 1, 3, 1, 1, 3, 5, 7]
def baseStart_7951176 : Nat := 118140960795 + 7951176 * 2 ^ 59
def prefixEnd_7951176 : Nat := 4983230072969 + 3 ^ 40 * 7951176 * 2
def baseEnd_7951176 : Nat := 151213890981247711890119

theorem tailTrace_7951176 : CollatzResearch.WordTrace tailWord_7951176 prefixEnd_7951176 151213890981247711890119 := by
  unfold tailWord_7951176
  simp only [CollatzResearch.WordTrace]
  refine ⟨145001606721127389796884691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193335475628169853062512921 145001606721127389796884691)
  ·
    refine ⟨217502410081691084695327037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145001606721127389796884691 217502410081691084695327037)
    ·
      refine ⟨81563403780634156760747639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217502410081691084695327037 81563403780634156760747639)
      ·
        refine ⟨122345105670951235141121459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81563403780634156760747639 122345105670951235141121459)
        ·
          refine ⟨183517658506426852711682189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122345105670951235141121459 183517658506426852711682189)
          ·
            refine ⟨68819121939910069766880821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183517658506426852711682189 68819121939910069766880821)
            ·
              refine ⟨6451792681866569040645077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68819121939910069766880821 6451792681866569040645077)
              ·
                refine ⟨151213890981247711890119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6451792681866569040645077 151213890981247711890119)
                ·
                  rfl

theorem cell23_7951176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 5, 7].length) (baseStart_7951176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7951176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7951176 prefixEnd_7951176 := by exact prefixLift 7951176
  have htrace : WordTrace (prefixWord ++ tailWord_7951176) baseStart_7951176 baseEnd_7951176 := by
    simpa [prefixWord, tailWord_7951176, baseEnd_7951176] using wordTrace_append hprefix tailTrace_7951176
  have hstable : (prefixWord ++ tailWord_7951176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7951176).length < 2 ^ (prefixWord ++ tailWord_7951176).sum := by decide
  have hdescent : baseEnd_7951176 < baseStart_7951176 := by decide
  rcases family_descends (prefixWord ++ tailWord_7951176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7951243 : List Nat := [1, 1, 1, 1, 4, 2, 2, 4, 1, 4, 2]
def baseStart_7951243 : Nat := 118140960795 + 7951243 * 2 ^ 59
def prefixEnd_7951243 : Nat := 4983230072969 + 3 ^ 40 * 7951243 * 2
def baseEnd_7951243 : Nat := 4082809459697539458895405

theorem tailTrace_7951243 : CollatzResearch.WordTrace tailWord_7951243 prefixEnd_7951243 4082809459697539458895405 := by
  unfold tailWord_7951243
  simp only [CollatzResearch.WordTrace]
  refine ⟨290005657133012050036458383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193337104755341366690972255 290005657133012050036458383)
  ·
    refine ⟨435008485699518075054687575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290005657133012050036458383 435008485699518075054687575)
    ·
      refine ⟨652512728549277112582031363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435008485699518075054687575 652512728549277112582031363)
      ·
        refine ⟨978769092823915668873047045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 652512728549277112582031363 978769092823915668873047045)
        ·
          refine ⟨183519204904484187913696321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 978769092823915668873047045 183519204904484187913696321)
          ·
            refine ⟨137639403678363140935272241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183519204904484187913696321 137639403678363140935272241)
            ·
              refine ⟨103229552758772355701454181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137639403678363140935272241 103229552758772355701454181)
              ·
                refine ⟨19355541142269816694022659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103229552758772355701454181 19355541142269816694022659)
                ·
                  refine ⟨29033311713404725041033989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19355541142269816694022659 29033311713404725041033989)
                  ·
                    refine ⟨5443745946263385945193873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29033311713404725041033989 5443745946263385945193873)
                    ·
                      refine ⟨4082809459697539458895405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5443745946263385945193873 4082809459697539458895405)
                      ·
                        rfl

theorem cell23_7951243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 4, 1, 4, 2].length) (baseStart_7951243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7951243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7951243 prefixEnd_7951243 := by exact prefixLift 7951243
  have htrace : WordTrace (prefixWord ++ tailWord_7951243) baseStart_7951243 baseEnd_7951243 := by
    simpa [prefixWord, tailWord_7951243, baseEnd_7951243] using wordTrace_append hprefix tailTrace_7951243
  have hstable : (prefixWord ++ tailWord_7951243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7951243).length < 2 ^ (prefixWord ++ tailWord_7951243).sum := by decide
  have hdescent : baseEnd_7951243 < baseStart_7951243 := by decide
  rcases family_descends (prefixWord ++ tailWord_7951243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7951254 : List Nat := [5, 3, 1, 1, 1, 1, 2, 1, 4, 1, 3]
def baseStart_7951254 : Nat := 118140960795 + 7951254 * 2 ^ 59
def prefixEnd_7951254 : Nat := 4983230072969 + 3 ^ 40 * 7951254 * 2
def baseEnd_7951254 : Nat := 4082815107984738915857855

theorem tailTrace_7951254 : CollatzResearch.WordTrace tailWord_7951254 prefixEnd_7951254 4082815107984738915857855 := by
  unfold tailWord_7951254
  simp only [CollatzResearch.WordTrace]
  refine ⟨18125378645998262432194301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 193337372223981465943405877 18125378645998262432194301)
  ·
    refine ⟨6797016992249348412072863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18125378645998262432194301 6797016992249348412072863)
    ·
      refine ⟨10195525488374022618109295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6797016992249348412072863 10195525488374022618109295)
      ·
        refine ⟨15293288232561033927163943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10195525488374022618109295 15293288232561033927163943)
        ·
          refine ⟨22939932348841550890745915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15293288232561033927163943 22939932348841550890745915)
          ·
            refine ⟨34409898523262326336118873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22939932348841550890745915 34409898523262326336118873)
            ·
              refine ⟨25807423892446744752089155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34409898523262326336118873 25807423892446744752089155)
              ·
                refine ⟨38711135838670117128133733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25807423892446744752089155 38711135838670117128133733)
                ·
                  refine ⟨7258337969750646961525075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38711135838670117128133733 7258337969750646961525075)
                  ·
                    refine ⟨10887506954625970442287613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7258337969750646961525075 10887506954625970442287613)
                    ·
                      refine ⟨4082815107984738915857855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10887506954625970442287613 4082815107984738915857855)
                      ·
                        rfl

theorem cell23_7951254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_7951254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7951254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7951254 prefixEnd_7951254 := by exact prefixLift 7951254
  have htrace : WordTrace (prefixWord ++ tailWord_7951254) baseStart_7951254 baseEnd_7951254 := by
    simpa [prefixWord, tailWord_7951254, baseEnd_7951254] using wordTrace_append hprefix tailTrace_7951254
  have hstable : (prefixWord ++ tailWord_7951254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7951254).length < 2 ^ (prefixWord ++ tailWord_7951254).sum := by decide
  have hdescent : baseEnd_7951254 < baseStart_7951254 := by decide
  rcases family_descends (prefixWord ++ tailWord_7951254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7951271 : List Nat := [1, 1, 6, 1, 4, 1, 2, 1, 2, 1, 3]
def baseStart_7951271 : Nat := 118140960795 + 7951271 * 2 ^ 59
def prefixEnd_7951271 : Nat := 4983230072969 + 3 ^ 40 * 7951271 * 2
def baseEnd_7951271 : Nat := 4082823837155865349345277

theorem tailTrace_7951271 : CollatzResearch.WordTrace tailWord_7951271 prefixEnd_7951271 4082823837155865349345277 := by
  unfold tailWord_7951271
  simp only [CollatzResearch.WordTrace]
  refine ⟨290006678376910610818477667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193337785584607073878985111 290006678376910610818477667)
  ·
    refine ⟨435010017565365916227716501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290006678376910610818477667 435010017565365916227716501)
    ·
      refine ⟨20391094573376527323174211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 435010017565365916227716501 20391094573376527323174211)
      ·
        refine ⟨30586641860064790984761317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20391094573376527323174211 30586641860064790984761317)
        ·
          refine ⟨5734995348762148309642747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30586641860064790984761317 5734995348762148309642747)
          ·
            refine ⟨8602493023143222464464121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5734995348762148309642747 8602493023143222464464121)
            ·
              refine ⟨6451869767357416848348091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8602493023143222464464121 6451869767357416848348091)
              ·
                refine ⟨9677804651036125272522137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6451869767357416848348091 9677804651036125272522137)
                ·
                  refine ⟨7258353488277093954391603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9677804651036125272522137 7258353488277093954391603)
                  ·
                    refine ⟨10887530232415640931587405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7258353488277093954391603 10887530232415640931587405)
                    ·
                      refine ⟨4082823837155865349345277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10887530232415640931587405 4082823837155865349345277)
                      ·
                        rfl

theorem cell23_7951271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 2, 1, 2, 1, 3].length) (baseStart_7951271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7951271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7951271 prefixEnd_7951271 := by exact prefixLift 7951271
  have htrace : WordTrace (prefixWord ++ tailWord_7951271) baseStart_7951271 baseEnd_7951271 := by
    simpa [prefixWord, tailWord_7951271, baseEnd_7951271] using wordTrace_append hprefix tailTrace_7951271
  have hstable : (prefixWord ++ tailWord_7951271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7951271).length < 2 ^ (prefixWord ++ tailWord_7951271).sum := by decide
  have hdescent : baseEnd_7951271 < baseStart_7951271 := by decide
  rcases family_descends (prefixWord ++ tailWord_7951271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7951343 : List Nat := [1, 1, 2, 1, 4, 3, 1, 1, 5, 4]
def baseStart_7951343 : Nat := 118140960795 + 7951343 * 2 ^ 59
def prefixEnd_7951343 : Nat := 4983230072969 + 3 ^ 40 * 7951343 * 2
def baseEnd_7951343 : Nat := 1360953602587663022548315

theorem tailTrace_7951343 : CollatzResearch.WordTrace tailWord_7951343 prefixEnd_7951343 1360953602587663022548315 := by
  unfold tailWord_7951343
  simp only [CollatzResearch.WordTrace]
  refine ⟨290009304432649767115098683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193339536288433178076732455 290009304432649767115098683)
  ·
    refine ⟨435013956648974650672648025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290009304432649767115098683 435013956648974650672648025)
    ·
      refine ⟨326260467486730988004486019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 435013956648974650672648025 326260467486730988004486019)
      ·
        refine ⟨489390701230096482006729029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326260467486730988004486019 489390701230096482006729029)
        ·
          refine ⟨91760756480643090376261693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 489390701230096482006729029 91760756480643090376261693)
          ·
            refine ⟨34410283680241158891098135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91760756480643090376261693 34410283680241158891098135)
            ·
              refine ⟨51615425520361738336647203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34410283680241158891098135 51615425520361738336647203)
              ·
                refine ⟨77423138280542607504970805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51615425520361738336647203 77423138280542607504970805)
                ·
                  refine ⟨7258419213800869453591013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77423138280542607504970805 7258419213800869453591013)
                  ·
                    refine ⟨1360953602587663022548315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7258419213800869453591013 1360953602587663022548315)
                    ·
                      rfl

theorem cell23_7951343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 5, 4].length) (baseStart_7951343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7951343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7951343 prefixEnd_7951343 := by exact prefixLift 7951343
  have htrace : WordTrace (prefixWord ++ tailWord_7951343) baseStart_7951343 baseEnd_7951343 := by
    simpa [prefixWord, tailWord_7951343, baseEnd_7951343] using wordTrace_append hprefix tailTrace_7951343
  have hstable : (prefixWord ++ tailWord_7951343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7951343).length < 2 ^ (prefixWord ++ tailWord_7951343).sum := by decide
  have hdescent : baseEnd_7951343 < baseStart_7951343 := by decide
  rcases family_descends (prefixWord ++ tailWord_7951343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7951350 : List Nat := [5, 1, 1, 1, 3, 2, 1, 1, 1, 3, 4]
def baseStart_7951350 : Nat := 118140960795 + 7951350 * 2 ^ 59
def prefixEnd_7951350 : Nat := 4983230072969 + 3 ^ 40 * 7951350 * 2
def baseEnd_7951350 : Nat := 4082864402127570540257413

theorem tailTrace_7951350 : CollatzResearch.WordTrace tailWord_7951350 prefixEnd_7951350 4082864402127570540257413 := by
  unfold tailWord_7951350
  simp only [CollatzResearch.WordTrace]
  refine ⟨18125597483976525456912719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 193339706495749604873735669 18125597483976525456912719)
  ·
    refine ⟨27188396225964788185369079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18125597483976525456912719 27188396225964788185369079)
    ·
      refine ⟨40782594338947182278053619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27188396225964788185369079 40782594338947182278053619)
      ·
        refine ⟨61173891508420773417080429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40782594338947182278053619 61173891508420773417080429)
        ·
          refine ⟨22940209315657790031405161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61173891508420773417080429 22940209315657790031405161)
          ·
            refine ⟨17205156986743342523553871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22940209315657790031405161 17205156986743342523553871)
            ·
              refine ⟨25807735480115013785330807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17205156986743342523553871 25807735480115013785330807)
              ·
                refine ⟨38711603220172520677996211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25807735480115013785330807 38711603220172520677996211)
                ·
                  refine ⟨58067404830258781016994317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38711603220172520677996211 58067404830258781016994317)
                  ·
                    refine ⟨21775276811347042881372869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58067404830258781016994317 21775276811347042881372869)
                    ·
                      refine ⟨4082864402127570540257413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21775276811347042881372869 4082864402127570540257413)
                      ·
                        rfl

theorem cell23_7951350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_7951350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7951350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7951350 prefixEnd_7951350 := by exact prefixLift 7951350
  have htrace : WordTrace (prefixWord ++ tailWord_7951350) baseStart_7951350 baseEnd_7951350 := by
    simpa [prefixWord, tailWord_7951350, baseEnd_7951350] using wordTrace_append hprefix tailTrace_7951350
  have hstable : (prefixWord ++ tailWord_7951350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7951350).length < 2 ^ (prefixWord ++ tailWord_7951350).sum := by decide
  have hdescent : baseEnd_7951350 < baseStart_7951350 := by decide
  rcases family_descends (prefixWord ++ tailWord_7951350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7951353 : List Nat := [1, 2, 1, 3, 1, 3, 3, 1, 1, 4, 3]
def baseStart_7951353 : Nat := 118140960795 + 7951353 * 2 ^ 59
def prefixEnd_7951353 : Nat := 4983230072969 + 3 ^ 40 * 7951353 * 2
def baseEnd_7951353 : Nat := 4082865942569534028519899

theorem tailTrace_7951353 : CollatzResearch.WordTrace tailWord_7951353 prefixEnd_7951353 4082865942569534028519899 := by
  unfold tailWord_7951353
  simp only [CollatzResearch.WordTrace]
  refine ⟨290009669162613538822962713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193339779441742359215308475 290009669162613538822962713)
  ·
    refine ⟨217507251871960154117222035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290009669162613538822962713 217507251871960154117222035)
    ·
      refine ⟨326260877807940231175833053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217507251871960154117222035 326260877807940231175833053)
      ·
        refine ⟨122347829177977586690937395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 326260877807940231175833053 122347829177977586690937395)
        ·
          refine ⟨183521743766966380036406093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122347829177977586690937395 183521743766966380036406093)
          ·
            refine ⟨68820653912612392513652285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183521743766966380036406093 68820653912612392513652285)
            ·
              refine ⟨25807745217229647192619607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68820653912612392513652285 25807745217229647192619607)
              ·
                refine ⟨38711617825844470788929411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25807745217229647192619607 38711617825844470788929411)
                ·
                  refine ⟨58067426738766706183394117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38711617825844470788929411 58067426738766706183394117)
                  ·
                    refine ⟨10887642513518757409386397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58067426738766706183394117 10887642513518757409386397)
                    ·
                      refine ⟨4082865942569534028519899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10887642513518757409386397 4082865942569534028519899)
                      ·
                        rfl

theorem cell23_7951353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 1, 1, 4, 3].length) (baseStart_7951353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7951353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7951353 prefixEnd_7951353 := by exact prefixLift 7951353
  have htrace : WordTrace (prefixWord ++ tailWord_7951353) baseStart_7951353 baseEnd_7951353 := by
    simpa [prefixWord, tailWord_7951353, baseEnd_7951353] using wordTrace_append hprefix tailTrace_7951353
  have hstable : (prefixWord ++ tailWord_7951353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7951353).length < 2 ^ (prefixWord ++ tailWord_7951353).sum := by decide
  have hdescent : baseEnd_7951353 < baseStart_7951353 := by decide
  rcases family_descends (prefixWord ++ tailWord_7951353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7951410 : List Nat := [3, 2, 1, 1, 2, 2, 1, 3, 1, 5, 2]
def baseStart_7951410 : Nat := 118140960795 + 7951410 * 2 ^ 59
def prefixEnd_7951410 : Nat := 4983230072969 + 3 ^ 40 * 7951410 * 2
def baseEnd_7951410 : Nat := 4082895210966840305507137

theorem tailTrace_7951410 : CollatzResearch.WordTrace tailWord_7951410 prefixEnd_7951410 4082895210966840305507137 := by
  unfold tailWord_7951410
  simp only [CollatzResearch.WordTrace]
  refine ⟨72502937030851759389446921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193341165415604691705191789 72502937030851759389446921)
  ·
    refine ⟨54377202773138819542085191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72502937030851759389446921 54377202773138819542085191)
    ·
      refine ⟨81565804159708229313127787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54377202773138819542085191 81565804159708229313127787)
      ·
        refine ⟨122348706239562343969691681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81565804159708229313127787 122348706239562343969691681)
        ·
          refine ⟨91761529679671757977268761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122348706239562343969691681 91761529679671757977268761)
          ·
            refine ⟨68821147259753818482951571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91761529679671757977268761 68821147259753818482951571)
            ·
              refine ⟨103231720889630727724427357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68821147259753818482951571 103231720889630727724427357)
              ·
                refine ⟨38711895333611522896660259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103231720889630727724427357 38711895333611522896660259)
                ·
                  refine ⟨58067843000417284344990389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38711895333611522896660259 58067843000417284344990389)
                  ·
                    refine ⟨5443860281289120407342849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58067843000417284344990389 5443860281289120407342849)
                    ·
                      refine ⟨4082895210966840305507137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5443860281289120407342849 4082895210966840305507137)
                      ·
                        rfl

theorem cell23_7951410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3, 1, 5, 2].length) (baseStart_7951410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7951410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7951410 prefixEnd_7951410 := by exact prefixLift 7951410
  have htrace : WordTrace (prefixWord ++ tailWord_7951410) baseStart_7951410 baseEnd_7951410 := by
    simpa [prefixWord, tailWord_7951410, baseEnd_7951410] using wordTrace_append hprefix tailTrace_7951410
  have hstable : (prefixWord ++ tailWord_7951410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7951410).length < 2 ^ (prefixWord ++ tailWord_7951410).sum := by decide
  have hdescent : baseEnd_7951410 < baseStart_7951410 := by decide
  rcases family_descends (prefixWord ++ tailWord_7951410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7951420 : List Nat := [2, 2, 2, 2, 2, 2, 2, 3, 1, 5]
def baseStart_7951420 : Nat := 118140960795 + 7951420 * 2 ^ 59
def prefixEnd_7951420 : Nat := 4983230072969 + 3 ^ 40 * 7951420 * 2
def baseEnd_7951420 : Nat := 1360966781924461755460697

theorem tailTrace_7951420 : CollatzResearch.WordTrace tailWord_7951420 prefixEnd_7951420 1360966781924461755460697 := by
  unfold tailWord_7951420
  simp only [CollatzResearch.WordTrace]
  refine ⟨145006056426685404632825857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193341408568913872843767809 145006056426685404632825857)
  ·
    refine ⟨108754542320014053474619393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145006056426685404632825857 108754542320014053474619393)
    ·
      refine ⟨81565906740010540105964545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108754542320014053474619393 81565906740010540105964545)
      ·
        refine ⟨61174430055007905079473409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81565906740010540105964545 61174430055007905079473409)
        ·
          refine ⟨45880822541255928809605057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61174430055007905079473409 45880822541255928809605057)
          ·
            refine ⟨34410616905941946607203793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45880822541255928809605057 34410616905941946607203793)
            ·
              refine ⟨25807962679456459955402845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34410616905941946607203793 25807962679456459955402845)
              ·
                refine ⟨9677986004796172483276067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25807962679456459955402845 9677986004796172483276067)
                ·
                  refine ⟨14516979007194258724914101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9677986004796172483276067 14516979007194258724914101)
                  ·
                    refine ⟨1360966781924461755460697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14516979007194258724914101 1360966781924461755460697)
                    ·
                      rfl

theorem cell23_7951420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 3, 1, 5].length) (baseStart_7951420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7951420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7951420 prefixEnd_7951420 := by exact prefixLift 7951420
  have htrace : WordTrace (prefixWord ++ tailWord_7951420) baseStart_7951420 baseEnd_7951420 := by
    simpa [prefixWord, tailWord_7951420, baseEnd_7951420] using wordTrace_append hprefix tailTrace_7951420
  have hstable : (prefixWord ++ tailWord_7951420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7951420).length < 2 ^ (prefixWord ++ tailWord_7951420).sum := by decide
  have hdescent : baseEnd_7951420 < baseStart_7951420 := by decide
  rcases family_descends (prefixWord ++ tailWord_7951420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7951423 : List Nat := [1, 1, 2, 2, 3, 1, 1, 2, 5, 1, 4]
def baseStart_7951423 : Nat := 118140960795 + 7951423 * 2 ^ 59
def prefixEnd_7951423 : Nat := 4983230072969 + 3 ^ 40 * 7951423 * 2
def baseEnd_7951423 : Nat := 4082901886215348754644577

theorem tailTrace_7951423 : CollatzResearch.WordTrace tailWord_7951423 prefixEnd_7951423 4082901886215348754644577 := by
  unfold tailWord_7951423
  simp only [CollatzResearch.WordTrace]
  refine ⟨290012222272359940778010923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193341481514906627185340615 290012222272359940778010923)
  ·
    refine ⟨435018333408539911167016385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290012222272359940778010923 435018333408539911167016385)
    ·
      refine ⟨326263750056404933375262289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 435018333408539911167016385 326263750056404933375262289)
      ·
        refine ⟨244697812542303700031446717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326263750056404933375262289 244697812542303700031446717)
        ·
          refine ⟨91761679703363887511792519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 244697812542303700031446717 91761679703363887511792519)
          ·
            refine ⟨137642519555045831267688779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91761679703363887511792519 137642519555045831267688779)
            ·
              refine ⟨206463779332568746901533169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137642519555045831267688779 206463779332568746901533169)
              ·
                refine ⟨154847834499426560176149877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 206463779332568746901533169 154847834499426560176149877)
                ·
                  refine ⟨14516984484321240016514051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 154847834499426560176149877 14516984484321240016514051)
                  ·
                    refine ⟨21775476726481860024771077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14516984484321240016514051 21775476726481860024771077)
                    ·
                      refine ⟨4082901886215348754644577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21775476726481860024771077 4082901886215348754644577)
                      ·
                        rfl

theorem cell23_7951423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 5, 1, 4].length) (baseStart_7951423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7951423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7951423 prefixEnd_7951423 := by exact prefixLift 7951423
  have htrace : WordTrace (prefixWord ++ tailWord_7951423) baseStart_7951423 baseEnd_7951423 := by
    simpa [prefixWord, tailWord_7951423, baseEnd_7951423] using wordTrace_append hprefix tailTrace_7951423
  have hstable : (prefixWord ++ tailWord_7951423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7951423).length < 2 ^ (prefixWord ++ tailWord_7951423).sum := by decide
  have hdescent : baseEnd_7951423 < baseStart_7951423 := by decide
  rcases family_descends (prefixWord ++ tailWord_7951423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7951454 : List Nat := [4, 4, 1, 1, 1, 2, 1, 1, 3, 5]
def baseStart_7951454 : Nat := 118140960795 + 7951454 * 2 ^ 59
def prefixEnd_7951454 : Nat := 4983230072969 + 3 ^ 40 * 7951454 * 2
def baseEnd_7951454 : Nat := 1360972601371879377785645

theorem tailTrace_7951454 : CollatzResearch.WordTrace tailWord_7951454 prefixEnd_7951454 1360972601371879377785645 := by
  unfold tailWord_7951454
  simp only [CollatzResearch.WordTrace]
  refine ⟨36251669116905954134048677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193342235290165088714926277 36251669116905954134048677)
  ·
    refine ⟨6797187959419866400134127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36251669116905954134048677 6797187959419866400134127)
    ·
      refine ⟨10195781939129799600201191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6797187959419866400134127 10195781939129799600201191)
      ·
        refine ⟨15293672908694699400301787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10195781939129799600201191 15293672908694699400301787)
        ·
          refine ⟨22940509363042049100452681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15293672908694699400301787 22940509363042049100452681)
          ·
            refine ⟨17205382022281536825339511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22940509363042049100452681 17205382022281536825339511)
            ·
              refine ⟨25808073033422305238009267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17205382022281536825339511 25808073033422305238009267)
              ·
                refine ⟨38712109550133457857013901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25808073033422305238009267 38712109550133457857013901)
                ·
                  refine ⟨14517041081300046696380213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38712109550133457857013901 14517041081300046696380213)
                  ·
                    refine ⟨1360972601371879377785645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14517041081300046696380213 1360972601371879377785645)
                    ·
                      rfl

theorem cell23_7951454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_7951454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7951454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7951454 prefixEnd_7951454 := by exact prefixLift 7951454
  have htrace : WordTrace (prefixWord ++ tailWord_7951454) baseStart_7951454 baseEnd_7951454 := by
    simpa [prefixWord, tailWord_7951454, baseEnd_7951454] using wordTrace_append hprefix tailTrace_7951454
  have hstable : (prefixWord ++ tailWord_7951454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7951454).length < 2 ^ (prefixWord ++ tailWord_7951454).sum := by decide
  have hdescent : baseEnd_7951454 < baseStart_7951454 := by decide
  rcases family_descends (prefixWord ++ tailWord_7951454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7951457 : List Nat := [1, 2, 3, 1, 1, 2, 2, 4, 3, 2, 2]
def baseStart_7951457 : Nat := 118140960795 + 7951457 * 2 ^ 59
def prefixEnd_7951457 : Nat := 4983230072969 + 3 ^ 40 * 7951457 * 2
def baseEnd_7951457 : Nat := 4082919344557601621619421

theorem tailTrace_7951457 : CollatzResearch.WordTrace tailWord_7951457 prefixEnd_7951457 4082919344557601621619421 := by
  unfold tailWord_7951457
  simp only [CollatzResearch.WordTrace]
  refine ⟨290013462354236764584748625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193342308236157843056499083 290013462354236764584748625)
  ·
    refine ⟨217510096765677573438561469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290013462354236764584748625 217510096765677573438561469)
    ·
      refine ⟨81566286287129090039460551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217510096765677573438561469 81566286287129090039460551)
      ·
        refine ⟨122349429430693635059190827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81566286287129090039460551 122349429430693635059190827)
        ·
          refine ⟨183524144146040452588786241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122349429430693635059190827 183524144146040452588786241)
          ·
            refine ⟨137643108109530339441589681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183524144146040452588786241 137643108109530339441589681)
            ·
              refine ⟨103232331082147754581192261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137643108109530339441589681 103232331082147754581192261)
              ·
                refine ⟨19356062077902703983973549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103232331082147754581192261 19356062077902703983973549)
                ·
                  refine ⟨7258523279213513993990081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19356062077902703983973549 7258523279213513993990081)
                  ·
                    refine ⟨5443892459410135495492561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7258523279213513993990081 5443892459410135495492561)
                    ·
                      refine ⟨4082919344557601621619421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5443892459410135495492561 4082919344557601621619421)
                      ·
                        rfl

theorem cell23_7951457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 4, 3, 2, 2].length) (baseStart_7951457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7951457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7951457 prefixEnd_7951457 := by exact prefixLift 7951457
  have htrace : WordTrace (prefixWord ++ tailWord_7951457) baseStart_7951457 baseEnd_7951457 := by
    simpa [prefixWord, tailWord_7951457, baseEnd_7951457] using wordTrace_append hprefix tailTrace_7951457
  have hstable : (prefixWord ++ tailWord_7951457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7951457).length < 2 ^ (prefixWord ++ tailWord_7951457).sum := by decide
  have hdescent : baseEnd_7951457 < baseStart_7951457 := by decide
  rcases family_descends (prefixWord ++ tailWord_7951457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7951463 : List Nat := [1, 1, 5, 1, 1, 3, 2, 9]
def baseStart_7951463 : Nat := 118140960795 + 7951463 * 2 ^ 59
def prefixEnd_7951463 : Nat := 4983230072969 + 3 ^ 40 * 7951463 * 2
def baseEnd_7951463 : Nat := 151219349090426985116459

theorem tailTrace_7951463 : CollatzResearch.WordTrace tailWord_7951463 prefixEnd_7951463 151219349090426985116459 := by
  unfold tailWord_7951463
  simp only [CollatzResearch.WordTrace]
  refine ⟨290013681192215027609467043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193342454128143351739644695 290013681192215027609467043)
  ·
    refine ⟨435020521788322541414200565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290013681192215027609467043 435020521788322541414200565)
    ·
      refine ⟨40783173917655238257581303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 435020521788322541414200565 40783173917655238257581303)
      ·
        refine ⟨61174760876482857386371955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40783173917655238257581303 61174760876482857386371955)
        ·
          refine ⟨91762141314724286079557933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61174760876482857386371955 91762141314724286079557933)
          ·
            refine ⟨34410802993021607279834225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91762141314724286079557933 34410802993021607279834225)
            ·
              refine ⟨25808102244766205459875669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34410802993021607279834225 25808102244766205459875669)
              ·
                refine ⟨151219349090426985116459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25808102244766205459875669 151219349090426985116459)
                ·
                  rfl

theorem cell23_7951463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 9].length) (baseStart_7951463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7951463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7951463 prefixEnd_7951463 := by exact prefixLift 7951463
  have htrace : WordTrace (prefixWord ++ tailWord_7951463) baseStart_7951463 baseEnd_7951463 := by
    simpa [prefixWord, tailWord_7951463, baseEnd_7951463] using wordTrace_append hprefix tailTrace_7951463
  have hstable : (prefixWord ++ tailWord_7951463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7951463).length < 2 ^ (prefixWord ++ tailWord_7951463).sum := by decide
  have hdescent : baseEnd_7951463 < baseStart_7951463 := by decide
  rcases family_descends (prefixWord ++ tailWord_7951463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7951470 : List Nat := [4, 1, 2, 2, 1, 2, 1, 1, 3, 2, 4]
def baseStart_7951470 : Nat := 118140960795 + 7951470 * 2 ^ 59
def prefixEnd_7951470 : Nat := 4983230072969 + 3 ^ 40 * 7951470 * 2
def baseEnd_7951470 : Nat := 4082926019806110070756861

theorem tailTrace_7951470 : CollatzResearch.WordTrace tailWord_7951470 prefixEnd_7951470 4082926019806110070756861 := by
  unfold tailWord_7951470
  simp only [CollatzResearch.WordTrace]
  refine ⟨36251742062898708475621483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193342624335459778536647909 36251742062898708475621483)
  ·
    refine ⟨54377613094348062713432225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36251742062898708475621483 54377613094348062713432225)
    ·
      refine ⟨40783209820761047035074169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54377613094348062713432225 40783209820761047035074169)
      ·
        refine ⟨30587407365570785276305627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40783209820761047035074169 30587407365570785276305627)
        ·
          refine ⟨45881111048356177914458441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30587407365570785276305627 45881111048356177914458441)
          ·
            refine ⟨34410833286267133435843831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45881111048356177914458441 34410833286267133435843831)
            ·
              refine ⟨51616249929400700153765747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34410833286267133435843831 51616249929400700153765747)
              ·
                refine ⟨77424374894101050230648621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51616249929400700153765747 77424374894101050230648621)
                ·
                  refine ⟨29034140585287893836493233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77424374894101050230648621 29034140585287893836493233)
                  ·
                    refine ⟨21775605438965920377369925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29034140585287893836493233 21775605438965920377369925)
                    ·
                      refine ⟨4082926019806110070756861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21775605438965920377369925 4082926019806110070756861)
                      ·
                        rfl

theorem cell23_7951470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_7951470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7951470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7951470 prefixEnd_7951470 := by exact prefixLift 7951470
  have htrace : WordTrace (prefixWord ++ tailWord_7951470) baseStart_7951470 baseEnd_7951470 := by
    simpa [prefixWord, tailWord_7951470, baseEnd_7951470] using wordTrace_append hprefix tailTrace_7951470
  have hstable : (prefixWord ++ tailWord_7951470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7951470).length < 2 ^ (prefixWord ++ tailWord_7951470).sum := by decide
  have hdescent : baseEnd_7951470 < baseStart_7951470 := by decide
  rcases family_descends (prefixWord ++ tailWord_7951470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7951507 : List Nat := [1, 1, 1, 2, 1, 2, 6, 3, 2, 1, 3]
def baseStart_7951507 : Nat := 118140960795 + 7951507 * 2 ^ 59
def prefixEnd_7951507 : Nat := 4983230072969 + 3 ^ 40 * 7951507 * 2
def baseEnd_7951507 : Nat := 4082945018590326425994191

theorem tailTrace_7951507 : CollatzResearch.WordTrace tailWord_7951507 prefixEnd_7951507 4082945018590326425994191 := by
  unfold tailWord_7951507
  simp only [CollatzResearch.WordTrace]
  refine ⟨290015286004055623124068775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193343524002703748749379183 290015286004055623124068775)
  ·
    refine ⟨435022929006083434686103163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290015286004055623124068775 435022929006083434686103163)
    ·
      refine ⟨652534393509125152029154745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435022929006083434686103163 652534393509125152029154745)
      ·
        refine ⟨489400795131843864021866059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 652534393509125152029154745 489400795131843864021866059)
        ·
          refine ⟨734101192697765796032799089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 489400795131843864021866059 734101192697765796032799089)
          ·
            refine ⟨550575894523324347024599317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 734101192697765796032799089 550575894523324347024599317)
            ·
              refine ⟨25808245055780828766778093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 550575894523324347024599317 25808245055780828766778093)
              ·
                refine ⟨9678091895917810787541785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25808245055780828766778093 9678091895917810787541785)
                ·
                  refine ⟨7258568921938358090656339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9678091895917810787541785 7258568921938358090656339)
                  ·
                    refine ⟨10887853382907537135984509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7258568921938358090656339 10887853382907537135984509)
                    ·
                      refine ⟨4082945018590326425994191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10887853382907537135984509 4082945018590326425994191)
                      ·
                        rfl

theorem cell23_7951507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 3, 2, 1, 3].length) (baseStart_7951507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7951507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7951507 prefixEnd_7951507 := by exact prefixLift 7951507
  have htrace : WordTrace (prefixWord ++ tailWord_7951507) baseStart_7951507 baseEnd_7951507 := by
    simpa [prefixWord, tailWord_7951507, baseEnd_7951507] using wordTrace_append hprefix tailTrace_7951507
  have hstable : (prefixWord ++ tailWord_7951507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7951507).length < 2 ^ (prefixWord ++ tailWord_7951507).sum := by decide
  have hdescent : baseEnd_7951507 < baseStart_7951507 := by decide
  rcases family_descends (prefixWord ++ tailWord_7951507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7951517 : List Nat := [1, 4, 2, 1, 1, 2, 1, 3, 3, 3, 2]
def baseStart_7951517 : Nat := 118140960795 + 7951517 * 2 ^ 59
def prefixEnd_7951517 : Nat := 4983230072969 + 3 ^ 40 * 7951517 * 2
def baseEnd_7951517 : Nat := 4082950153396871386869145

theorem tailTrace_7951517 : CollatzResearch.WordTrace tailWord_7951517 prefixEnd_7951517 4082950153396871386869145 := by
  unfold tailWord_7951517
  simp only [CollatzResearch.WordTrace]
  refine ⟨290015650734019394831932805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193343767156012929887955203 290015650734019394831932805)
  ·
    refine ⟨54377934512628636530987401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 290015650734019394831932805 54377934512628636530987401)
    ·
      refine ⟨40783450884471477398240551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54377934512628636530987401 40783450884471477398240551)
      ·
        refine ⟨61175176326707216097360827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40783450884471477398240551 61175176326707216097360827)
        ·
          refine ⟨91762764490060824146041241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61175176326707216097360827 91762764490060824146041241)
          ·
            refine ⟨68822073367545618109530931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91762764490060824146041241 68822073367545618109530931)
            ·
              refine ⟨103233110051318427164296397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68822073367545618109530931 103233110051318427164296397)
              ·
                refine ⟨38712416269244410186611149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103233110051318427164296397 38712416269244410186611149)
                ·
                  refine ⟨14517156100966653819979181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38712416269244410186611149 14517156100966653819979181)
                  ·
                    refine ⟨5443933537862495182492193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14517156100966653819979181 5443933537862495182492193)
                    ·
                      refine ⟨4082950153396871386869145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5443933537862495182492193 4082950153396871386869145)
                      ·
                        rfl

theorem cell23_7951517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 3, 3, 3, 2].length) (baseStart_7951517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7951517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7951517 prefixEnd_7951517 := by exact prefixLift 7951517
  have htrace : WordTrace (prefixWord ++ tailWord_7951517) baseStart_7951517 baseEnd_7951517 := by
    simpa [prefixWord, tailWord_7951517, baseEnd_7951517] using wordTrace_append hprefix tailTrace_7951517
  have hstable : (prefixWord ++ tailWord_7951517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7951517).length < 2 ^ (prefixWord ++ tailWord_7951517).sum := by decide
  have hdescent : baseEnd_7951517 < baseStart_7951517 := by decide
  rcases family_descends (prefixWord ++ tailWord_7951517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7951560 : List Nat := [2, 1, 3, 1, 2, 1, 4, 1, 2, 2, 4]
def baseStart_7951560 : Nat := 118140960795 + 7951560 * 2 ^ 59
def prefixEnd_7951560 : Nat := 4983230072969 + 3 ^ 40 * 7951560 * 2
def baseEnd_7951560 : Nat := 4082972233065014718631447

theorem tailTrace_7951560 : CollatzResearch.WordTrace tailWord_7951560 prefixEnd_7951560 4082972233065014718631447 := by
  unfold tailWord_7951560
  simp only [CollatzResearch.WordTrace]
  refine ⟨145008609536431806587874067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193344812715242408783832089 145008609536431806587874067)
  ·
    refine ⟨217512914304647709881811101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145008609536431806587874067 217512914304647709881811101)
    ·
      refine ⟨81567342864242891205679163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217512914304647709881811101 81567342864242891205679163)
      ·
        refine ⟨122351014296364336808518745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81567342864242891205679163 122351014296364336808518745)
        ·
          refine ⟨91763260722273252606389059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122351014296364336808518745 91763260722273252606389059)
          ·
            refine ⟨137644891083409878909583589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91763260722273252606389059 137644891083409878909583589)
            ·
              refine ⟨25808417078139352295546923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137644891083409878909583589 25808417078139352295546923)
              ·
                refine ⟨38712625617209028443320385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25808417078139352295546923 38712625617209028443320385)
                ·
                  refine ⟨29034469212906771332490289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38712625617209028443320385 29034469212906771332490289)
                  ·
                    refine ⟨21775851909680078499367717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29034469212906771332490289 21775851909680078499367717)
                    ·
                      refine ⟨4082972233065014718631447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21775851909680078499367717 4082972233065014718631447)
                      ·
                        rfl

theorem cell23_7951560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 1, 2, 2, 4].length) (baseStart_7951560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7951560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7951560 prefixEnd_7951560 := by exact prefixLift 7951560
  have htrace : WordTrace (prefixWord ++ tailWord_7951560) baseStart_7951560 baseEnd_7951560 := by
    simpa [prefixWord, tailWord_7951560, baseEnd_7951560] using wordTrace_append hprefix tailTrace_7951560
  have hstable : (prefixWord ++ tailWord_7951560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7951560).length < 2 ^ (prefixWord ++ tailWord_7951560).sum := by decide
  have hdescent : baseEnd_7951560 < baseStart_7951560 := by decide
  rcases family_descends (prefixWord ++ tailWord_7951560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7951570 : List Nat := [3, 2, 2, 2, 1, 1, 1, 4, 7]
def baseStart_7951570 : Nat := 118140960795 + 7951570 * 2 ^ 59
def prefixEnd_7951570 : Nat := 4983230072969 + 3 ^ 40 * 7951570 * 2
def baseEnd_7951570 : Nat := 453664151985728853278489

theorem tailTrace_7951570 : CollatzResearch.WordTrace tailWord_7951570 prefixEnd_7951570 453664151985728853278489 := by
  unfold tailWord_7951570
  simp only [CollatzResearch.WordTrace]
  refine ⟨72504395950706846220903041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193345055868551589922408109 72504395950706846220903041)
  ·
    refine ⟨54378296963030134665677281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72504395950706846220903041 54378296963030134665677281)
    ·
      refine ⟨40783722722272600999257961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54378296963030134665677281 40783722722272600999257961)
      ·
        refine ⟨30587792041704450749443471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40783722722272600999257961 30587792041704450749443471)
        ·
          refine ⟨45881688062556676124165207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30587792041704450749443471 45881688062556676124165207)
          ·
            refine ⟨68822532093835014186247811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45881688062556676124165207 68822532093835014186247811)
            ·
              refine ⟨103233798140752521279371717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68822532093835014186247811 103233798140752521279371717)
              ·
                refine ⟨19356337151391097739882197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103233798140752521279371717 19356337151391097739882197)
                ·
                  refine ⟨453664151985728853278489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19356337151391097739882197 453664151985728853278489)
                  ·
                    rfl

theorem cell23_7951570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 4, 7].length) (baseStart_7951570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7951570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7951570 prefixEnd_7951570 := by exact prefixLift 7951570
  have htrace : WordTrace (prefixWord ++ tailWord_7951570) baseStart_7951570 baseEnd_7951570 := by
    simpa [prefixWord, tailWord_7951570, baseEnd_7951570] using wordTrace_append hprefix tailTrace_7951570
  have hstable : (prefixWord ++ tailWord_7951570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7951570).length < 2 ^ (prefixWord ++ tailWord_7951570).sum := by decide
  have hdescent : baseEnd_7951570 < baseStart_7951570 := by decide
  rcases family_descends (prefixWord ++ tailWord_7951570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7951610 : List Nat := [3, 1, 1, 1, 1, 4, 3, 1, 1, 2, 5]
def baseStart_7951610 : Nat := 118140960795 + 7951610 * 2 ^ 59
def prefixEnd_7951610 : Nat := 4983230072969 + 3 ^ 40 * 7951610 * 2
def baseEnd_7951610 : Nat := 4082997907097739523006217

theorem tailTrace_7951610 : CollatzResearch.WordTrace tailWord_7951610 prefixEnd_7951610 4082997907097739523006217 := by
  unfold tailWord_7951610
  simp only [CollatzResearch.WordTrace]
  refine ⟨72504760680670617928767071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193346028481788314476712189 72504760680670617928767071)
  ·
    refine ⟨108757141021005926893150607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72504760680670617928767071 108757141021005926893150607)
    ·
      refine ⟨163135711531508890339725911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108757141021005926893150607 163135711531508890339725911)
      ·
        refine ⟨244703567297263335509588867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163135711531508890339725911 244703567297263335509588867)
        ·
          refine ⟨367055350945895003264383301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244703567297263335509588867 367055350945895003264383301)
          ·
            refine ⟨68822878302355313112071869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 367055350945895003264383301 68822878302355313112071869)
            ·
              refine ⟨25808579363383242417026951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68822878302355313112071869 25808579363383242417026951)
              ·
                refine ⟨38712869045074863625540427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25808579363383242417026951 38712869045074863625540427)
                ·
                  refine ⟨58069303567612295438310641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38712869045074863625540427 58069303567612295438310641)
                  ·
                    refine ⟨43551977675709221578732981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58069303567612295438310641 43551977675709221578732981)
                    ·
                      refine ⟨4082997907097739523006217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43551977675709221578732981 4082997907097739523006217)
                      ·
                        rfl

theorem cell23_7951610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 1, 1, 2, 5].length) (baseStart_7951610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7951610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7951610 prefixEnd_7951610 := by exact prefixLift 7951610
  have htrace : WordTrace (prefixWord ++ tailWord_7951610) baseStart_7951610 baseEnd_7951610 := by
    simpa [prefixWord, tailWord_7951610, baseEnd_7951610] using wordTrace_append hprefix tailTrace_7951610
  have hstable : (prefixWord ++ tailWord_7951610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7951610).length < 2 ^ (prefixWord ++ tailWord_7951610).sum := by decide
  have hdescent : baseEnd_7951610 < baseStart_7951610 := by decide
  rcases family_descends (prefixWord ++ tailWord_7951610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7951637 : List Nat := [1, 3, 2, 1, 2, 1, 1, 2, 4, 4, 2]
def baseStart_7951637 : Nat := 118140960795 + 7951637 * 2 ^ 59
def prefixEnd_7951637 : Nat := 4983230072969 + 3 ^ 40 * 7951637 * 2
def baseEnd_7951637 : Nat := 4083011771075410917368593

theorem tailTrace_7951637 : CollatzResearch.WordTrace tailWord_7951637 prefixEnd_7951637 4083011771075410917368593 := by
  unfold tailWord_7951637
  simp only [CollatzResearch.WordTrace]
  refine ⟨290020027493584655326301165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193346684995723103550867443 290020027493584655326301165)
  ·
    refine ⟨108757510310094245747362937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290020027493584655326301165 108757510310094245747362937)
    ·
      refine ⟨81568132732570684310522203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108757510310094245747362937 81568132732570684310522203)
      ·
        refine ⟨122352199098856026465783305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81568132732570684310522203 122352199098856026465783305)
        ·
          refine ⟨91764149324142019849337479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122352199098856026465783305 91764149324142019849337479)
          ·
            refine ⟨137646223986213029774006219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91764149324142019849337479 137646223986213029774006219)
            ·
              refine ⟨206469335979319544661009329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137646223986213029774006219 206469335979319544661009329)
              ·
                refine ⟨154852001984489658495756997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 206469335979319544661009329 154852001984489658495756997)
                ·
                  refine ⟨29034750372091810967954437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 154852001984489658495756997 29034750372091810967954437)
                  ·
                    refine ⟨5444015694767214556491457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29034750372091810967954437 5444015694767214556491457)
                    ·
                      refine ⟨4083011771075410917368593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5444015694767214556491457 4083011771075410917368593)
                      ·
                        rfl

theorem cell23_7951637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 4, 4, 2].length) (baseStart_7951637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7951637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7951637 prefixEnd_7951637 := by exact prefixLift 7951637
  have htrace : WordTrace (prefixWord ++ tailWord_7951637) baseStart_7951637 baseEnd_7951637 := by
    simpa [prefixWord, tailWord_7951637, baseEnd_7951637] using wordTrace_append hprefix tailTrace_7951637
  have hstable : (prefixWord ++ tailWord_7951637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7951637).length < 2 ^ (prefixWord ++ tailWord_7951637).sum := by decide
  have hdescent : baseEnd_7951637 < baseStart_7951637 := by decide
  rcases family_descends (prefixWord ++ tailWord_7951637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7951664 : List Nat := [2, 1, 1, 1, 2, 2, 5, 4, 1, 4]
def baseStart_7951664 : Nat := 118140960795 + 7951664 * 2 ^ 59
def prefixEnd_7951664 : Nat := 4983230072969 + 3 ^ 40 * 7951664 * 2
def baseEnd_7951664 : Nat := 1361008545017694103910323

theorem tailTrace_7951664 : CollatzResearch.WordTrace tailWord_7951664 prefixEnd_7951664 1361008545017694103910323 := by
  unfold tailWord_7951664
  simp only [CollatzResearch.WordTrace]
  refine ⟨145010506132243419468767023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193347341509657892625022697 145010506132243419468767023)
  ·
    refine ⟨217515759198365129203150535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145010506132243419468767023 217515759198365129203150535)
    ·
      refine ⟨326273638797547693804725803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217515759198365129203150535 326273638797547693804725803)
      ·
        refine ⟨489410458196321540707088705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326273638797547693804725803 489410458196321540707088705)
        ·
          refine ⟨367057843647241155530316529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 489410458196321540707088705 367057843647241155530316529)
          ·
            refine ⟨275293382735430866647737397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 367057843647241155530316529 275293382735430866647737397)
            ·
              refine ⟨25808754631446643748225381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 275293382735430866647737397 25808754631446643748225381)
              ·
                refine ⟨4839141493396245702792259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25808754631446643748225381 4839141493396245702792259)
                ·
                  refine ⟨7258712240094368554188389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4839141493396245702792259 7258712240094368554188389)
                  ·
                    refine ⟨1361008545017694103910323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7258712240094368554188389 1361008545017694103910323)
                    ·
                      rfl

theorem cell23_7951664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 4, 1, 4].length) (baseStart_7951664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7951664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7951664 prefixEnd_7951664 := by exact prefixLift 7951664
  have htrace : WordTrace (prefixWord ++ tailWord_7951664) baseStart_7951664 baseEnd_7951664 := by
    simpa [prefixWord, tailWord_7951664, baseEnd_7951664] using wordTrace_append hprefix tailTrace_7951664
  have hstable : (prefixWord ++ tailWord_7951664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7951664).length < 2 ^ (prefixWord ++ tailWord_7951664).sum := by decide
  have hdescent : baseEnd_7951664 < baseStart_7951664 := by decide
  rcases family_descends (prefixWord ++ tailWord_7951664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7951737 : List Nat := [1, 2, 1, 3, 2, 1, 5, 1, 1, 6]
def baseStart_7951737 : Nat := 118140960795 + 7951737 * 2 ^ 59
def prefixEnd_7951737 : Nat := 4983230072969 + 3 ^ 40 * 7951737 * 2
def baseEnd_7951737 : Nat := 1361021039713620175372711

theorem tailTrace_7951737 : CollatzResearch.WordTrace tailWord_7951737 prefixEnd_7951737 1361021039713620175372711 := by
  unfold tailWord_7951737
  simp only [CollatzResearch.WordTrace]
  refine ⟨290023674793222372404941465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193349116528814914936627643 290023674793222372404941465)
  ·
    refine ⟨217517756094916779303706099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290023674793222372404941465 217517756094916779303706099)
    ·
      refine ⟨326276634142375168955559149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217517756094916779303706099 326276634142375168955559149)
      ·
        refine ⟨122353737803390688358334681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 326276634142375168955559149 122353737803390688358334681)
        ·
          refine ⟨91765303352543016268751011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122353737803390688358334681 91765303352543016268751011)
          ·
            refine ⟨137647955028814524403126517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91765303352543016268751011 137647955028814524403126517)
            ·
              refine ⟨12904495783951361662793111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 137647955028814524403126517 12904495783951361662793111)
              ·
                refine ⟨19356743675927042494189667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12904495783951361662793111 19356743675927042494189667)
                ·
                  refine ⟨29035115513890563741284501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19356743675927042494189667 29035115513890563741284501)
                  ·
                    refine ⟨1361021039713620175372711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29035115513890563741284501 1361021039713620175372711)
                    ·
                      rfl

theorem cell23_7951737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 1, 1, 6].length) (baseStart_7951737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7951737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7951737 prefixEnd_7951737 := by exact prefixLift 7951737
  have htrace : WordTrace (prefixWord ++ tailWord_7951737) baseStart_7951737 baseEnd_7951737 := by
    simpa [prefixWord, tailWord_7951737, baseEnd_7951737] using wordTrace_append hprefix tailTrace_7951737
  have hstable : (prefixWord ++ tailWord_7951737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7951737).length < 2 ^ (prefixWord ++ tailWord_7951737).sum := by decide
  have hdescent : baseEnd_7951737 < baseStart_7951737 := by decide
  rcases family_descends (prefixWord ++ tailWord_7951737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7951764 : List Nat := [2, 4, 2, 1, 2, 1, 1, 3, 1, 1, 5]
def baseStart_7951764 : Nat := 118140960795 + 7951764 * 2 ^ 59
def prefixEnd_7951764 : Nat := 4983230072969 + 3 ^ 40 * 7951764 * 2
def baseEnd_7951764 : Nat := 4083076983118531920480509

theorem tailTrace_7951764 : CollatzResearch.WordTrace tailWord_7951764 prefixEnd_7951764 4083076983118531920480509 := by
  unfold tailWord_7951764
  simp only [CollatzResearch.WordTrace]
  refine ⟨145012329782062278008087173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193349773042749704010782897 145012329782062278008087173)
  ·
    refine ⟨27189811834136677126516345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145012329782062278008087173 27189811834136677126516345)
    ·
      refine ⟨20392358875602507844887259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27189811834136677126516345 20392358875602507844887259)
      ·
        refine ⟨30588538313403761767330889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20392358875602507844887259 30588538313403761767330889)
        ·
          refine ⟨22941403735052821325498167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30588538313403761767330889 22941403735052821325498167)
          ·
            refine ⟨34412105602579231988247251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22941403735052821325498167 34412105602579231988247251)
            ·
              refine ⟨51618158403868847982370877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34412105602579231988247251 51618158403868847982370877)
              ·
                refine ⟨19356809401450817993389079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51618158403868847982370877 19356809401450817993389079)
                ·
                  refine ⟨29035214102176226990083619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19356809401450817993389079 29035214102176226990083619)
                  ·
                    refine ⟨43552821153264340485125429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29035214102176226990083619 43552821153264340485125429)
                    ·
                      refine ⟨4083076983118531920480509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43552821153264340485125429 4083076983118531920480509)
                      ·
                        rfl

theorem cell23_7951764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_7951764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7951764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7951764 prefixEnd_7951764 := by exact prefixLift 7951764
  have htrace : WordTrace (prefixWord ++ tailWord_7951764) baseStart_7951764 baseEnd_7951764 := by
    simpa [prefixWord, tailWord_7951764, baseEnd_7951764] using wordTrace_append hprefix tailTrace_7951764
  have hstable : (prefixWord ++ tailWord_7951764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7951764).length < 2 ^ (prefixWord ++ tailWord_7951764).sum := by decide
  have hdescent : baseEnd_7951764 < baseStart_7951764 := by decide
  rcases family_descends (prefixWord ++ tailWord_7951764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7951772 : List Nat := [2, 2, 3, 4, 1, 1, 3, 2, 1, 1, 3]
def baseStart_7951772 : Nat := 118140960795 + 7951772 * 2 ^ 59
def prefixEnd_7951772 : Nat := 4983230072969 + 3 ^ 40 * 7951772 * 2
def baseEnd_7951772 : Nat := 4083081090963767889180473

theorem tailTrace_7951772 : CollatzResearch.WordTrace tailWord_7951772 prefixEnd_7951772 4083081090963767889180473 := by
  unfold tailWord_7951772
  simp only [CollatzResearch.WordTrace]
  refine ⟨145012475674047786691232785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193349967565397048921643713 145012475674047786691232785)
  ·
    refine ⟨108759356755535840018424589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145012475674047786691232785 108759356755535840018424589)
    ·
      refine ⟨40784758783325940006909221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108759356755535840018424589 40784758783325940006909221)
      ·
        refine ⟨7647142271873613751295479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40784758783325940006909221 7647142271873613751295479)
        ·
          refine ⟨11470713407810420626943219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7647142271873613751295479 11470713407810420626943219)
          ·
            refine ⟨17206070111715630940414829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11470713407810420626943219 17206070111715630940414829)
            ·
              refine ⟨6452276291893361602655561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17206070111715630940414829 6452276291893361602655561)
              ·
                refine ⟨4839207218920021201991671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6452276291893361602655561 4839207218920021201991671)
                ·
                  refine ⟨7258810828380031802987507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4839207218920021201991671 7258810828380031802987507)
                  ·
                    refine ⟨10888216242570047704481261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7258810828380031802987507 10888216242570047704481261)
                    ·
                      refine ⟨4083081090963767889180473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10888216242570047704481261 4083081090963767889180473)
                      ·
                        rfl

theorem cell23_7951772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_7951772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7951772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7951772 prefixEnd_7951772 := by exact prefixLift 7951772
  have htrace : WordTrace (prefixWord ++ tailWord_7951772) baseStart_7951772 baseEnd_7951772 := by
    simpa [prefixWord, tailWord_7951772, baseEnd_7951772] using wordTrace_append hprefix tailTrace_7951772
  have hstable : (prefixWord ++ tailWord_7951772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7951772).length < 2 ^ (prefixWord ++ tailWord_7951772).sum := by decide
  have hdescent : baseEnd_7951772 < baseStart_7951772 := by decide
  rcases family_descends (prefixWord ++ tailWord_7951772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7951778 : List Nat := [3, 3, 1, 2, 1, 2, 3, 1, 3, 2, 2]
def baseStart_7951778 : Nat := 118140960795 + 7951778 * 2 ^ 59
def prefixEnd_7951778 : Nat := 4983230072969 + 3 ^ 40 * 7951778 * 2
def baseEnd_7951778 : Nat := 4083084171847694865705445

theorem tailTrace_7951778 : CollatzResearch.WordTrace tailWord_7951778 prefixEnd_7951778 4083084171847694865705445 := by
  unfold tailWord_7951778
  simp only [CollatzResearch.WordTrace]
  refine ⟨72506292546518459101795997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193350113457382557604789325 72506292546518459101795997)
  ·
    refine ⟨27189859704944422163173499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72506292546518459101795997 27189859704944422163173499)
    ·
      refine ⟨40784789557416633244760249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27189859704944422163173499 40784789557416633244760249)
      ·
        refine ⟨30588592168062474933570187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40784789557416633244760249 30588592168062474933570187)
        ·
          refine ⟨45882888252093712400355281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30588592168062474933570187 45882888252093712400355281)
          ·
            refine ⟨34412166189070284300266461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45882888252093712400355281 34412166189070284300266461)
            ·
              refine ⟨12904562320901356612599923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34412166189070284300266461 12904562320901356612599923)
              ·
                refine ⟨19356843481352034918899885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12904562320901356612599923 19356843481352034918899885)
                ·
                  refine ⟨7258816305507013094587457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19356843481352034918899885 7258816305507013094587457)
                  ·
                    refine ⟨5444112229130259820940593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7258816305507013094587457 5444112229130259820940593)
                    ·
                      refine ⟨4083084171847694865705445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5444112229130259820940593 4083084171847694865705445)
                      ·
                        rfl

theorem cell23_7951778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 1, 3, 2, 2].length) (baseStart_7951778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7951778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7951778 prefixEnd_7951778 := by exact prefixLift 7951778
  have htrace : WordTrace (prefixWord ++ tailWord_7951778) baseStart_7951778 baseEnd_7951778 := by
    simpa [prefixWord, tailWord_7951778, baseEnd_7951778] using wordTrace_append hprefix tailTrace_7951778
  have hstable : (prefixWord ++ tailWord_7951778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7951778).length < 2 ^ (prefixWord ++ tailWord_7951778).sum := by decide
  have hdescent : baseEnd_7951778 < baseStart_7951778 := by decide
  rcases family_descends (prefixWord ++ tailWord_7951778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7951794 : List Nat := [3, 2, 1, 1, 1, 1, 2, 2, 6, 1, 3]
def baseStart_7951794 : Nat := 118140960795 + 7951794 * 2 ^ 59
def prefixEnd_7951794 : Nat := 4983230072969 + 3 ^ 40 * 7951794 * 2
def baseEnd_7951794 : Nat := 4083092387538166803105371

theorem tailTrace_7951794 : CollatzResearch.WordTrace tailWord_7951794 prefixEnd_7951794 4083092387538166803105371 := by
  unfold tailWord_7951794
  simp only [CollatzResearch.WordTrace]
  refine ⟨72506438438503967784941609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193350502502677247426510957 72506438438503967784941609)
  ·
    refine ⟨54379828828877975838706207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72506438438503967784941609 54379828828877975838706207)
    ·
      refine ⟨81569743243316963758059311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54379828828877975838706207 81569743243316963758059311)
      ·
        refine ⟨122354614864975445637088967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81569743243316963758059311 122354614864975445637088967)
        ·
          refine ⟨183531922297463168455633451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122354614864975445637088967 183531922297463168455633451)
          ·
            refine ⟨275297883446194752683450177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183531922297463168455633451 275297883446194752683450177)
            ·
              refine ⟨206473412584646064512587633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 275297883446194752683450177 206473412584646064512587633)
              ·
                refine ⟨154855059438484548384440725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 206473412584646064512587633 154855059438484548384440725)
                ·
                  refine ⟨7258830911178963205520659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 154855059438484548384440725 7258830911178963205520659)
                  ·
                    refine ⟨10888246366768444808280989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7258830911178963205520659 10888246366768444808280989)
                    ·
                      refine ⟨4083092387538166803105371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10888246366768444808280989 4083092387538166803105371)
                      ·
                        rfl

theorem cell23_7951794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 6, 1, 3].length) (baseStart_7951794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7951794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7951794 prefixEnd_7951794 := by exact prefixLift 7951794
  have htrace : WordTrace (prefixWord ++ tailWord_7951794) baseStart_7951794 baseEnd_7951794 := by
    simpa [prefixWord, tailWord_7951794, baseEnd_7951794] using wordTrace_append hprefix tailTrace_7951794
  have hstable : (prefixWord ++ tailWord_7951794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7951794).length < 2 ^ (prefixWord ++ tailWord_7951794).sum := by decide
  have hdescent : baseEnd_7951794 < baseStart_7951794 := by decide
  rcases family_descends (prefixWord ++ tailWord_7951794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7951854 : List Nat := [4, 1, 2, 1, 2, 1, 1, 2, 2, 4, 3]
def baseStart_7951854 : Nat := 118140960795 + 7951854 * 2 ^ 59
def prefixEnd_7951854 : Nat := 4983230072969 + 3 ^ 40 * 7951854 * 2
def baseEnd_7951854 : Nat := 4083123196377436568355095

theorem tailTrace_7951854 : CollatzResearch.WordTrace tailWord_7951854 prefixEnd_7951854 4083123196377436568355095 := by
  unfold tailWord_7951854
  simp only [CollatzResearch.WordTrace]
  refine ⟨36253492766724812673368827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193351961422532334257967077 36253492766724812673368827)
  ·
    refine ⟨54380239150087219010053241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36253492766724812673368827 54380239150087219010053241)
    ·
      refine ⟨40785179362565414257539931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54380239150087219010053241 40785179362565414257539931)
      ·
        refine ⟨61177769043848121386309897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40785179362565414257539931 61177769043848121386309897)
        ·
          refine ⟨45883326782886091039732423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61177769043848121386309897 45883326782886091039732423)
          ·
            refine ⟨68824990174329136559598635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45883326782886091039732423 68824990174329136559598635)
            ·
              refine ⟨103237485261493704839397953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68824990174329136559598635 103237485261493704839397953)
              ·
                refine ⟨77428113946120278629548465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103237485261493704839397953 77428113946120278629548465)
                ·
                  refine ⟨58071085459590208972161349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77428113946120278629548465 58071085459590208972161349)
                  ·
                    refine ⟨10888328523673164182280253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58071085459590208972161349 10888328523673164182280253)
                    ·
                      refine ⟨4083123196377436568355095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10888328523673164182280253 4083123196377436568355095)
                      ·
                        rfl

theorem cell23_7951854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 2, 4, 3].length) (baseStart_7951854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7951854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7951854 prefixEnd_7951854 := by exact prefixLift 7951854
  have htrace : WordTrace (prefixWord ++ tailWord_7951854) baseStart_7951854 baseEnd_7951854 := by
    simpa [prefixWord, tailWord_7951854, baseEnd_7951854] using wordTrace_append hprefix tailTrace_7951854
  have hstable : (prefixWord ++ tailWord_7951854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7951854).length < 2 ^ (prefixWord ++ tailWord_7951854).sum := by decide
  have hdescent : baseEnd_7951854 < baseStart_7951854 := by decide
  rcases family_descends (prefixWord ++ tailWord_7951854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7951857 : List Nat := [1, 2, 2, 2, 3, 2, 1, 1, 9]
def baseStart_7951857 : Nat := 118140960795 + 7951857 * 2 ^ 59
def prefixEnd_7951857 : Nat := 4983230072969 + 3 ^ 40 * 7951857 * 2
def baseEnd_7951857 : Nat := 453680526313266672957509

theorem tailTrace_7951857 : CollatzResearch.WordTrace tailWord_7951857 prefixEnd_7951857 453680526313266672957509 := by
  unfold tailWord_7951857
  simp only [CollatzResearch.WordTrace]
  refine ⟨290028051552787632899309825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193352034368525088599539883 290028051552787632899309825)
  ·
    refine ⟨217521038664590724674482369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290028051552787632899309825 217521038664590724674482369)
    ·
      refine ⟨163140778998443043505861777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217521038664590724674482369 163140778998443043505861777)
      ·
        refine ⟨122355584248832282629396333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163140778998443043505861777 122355584248832282629396333)
        ·
          refine ⟨45883344093312105986023625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122355584248832282629396333 45883344093312105986023625)
          ·
            refine ⟨34412508069984079489517719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45883344093312105986023625 34412508069984079489517719)
            ·
              refine ⟨51618762104976119234276579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34412508069984079489517719 51618762104976119234276579)
              ·
                refine ⟨77428143157464178851414869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51618762104976119234276579 77428143157464178851414869)
                ·
                  refine ⟨453680526313266672957509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 77428143157464178851414869 453680526313266672957509)
                  ·
                    rfl

theorem cell23_7951857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 9].length) (baseStart_7951857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7951857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7951857 prefixEnd_7951857 := by exact prefixLift 7951857
  have htrace : WordTrace (prefixWord ++ tailWord_7951857) baseStart_7951857 baseEnd_7951857 := by
    simpa [prefixWord, tailWord_7951857, baseEnd_7951857] using wordTrace_append hprefix tailTrace_7951857
  have hstable : (prefixWord ++ tailWord_7951857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7951857).length < 2 ^ (prefixWord ++ tailWord_7951857).sum := by decide
  have hdescent : baseEnd_7951857 < baseStart_7951857 := by decide
  rcases family_descends (prefixWord ++ tailWord_7951857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7951904 : List Nat := [2, 1, 1, 6, 1, 1, 1, 2, 1, 7]
def baseStart_7951904 : Nat := 118140960795 + 7951904 * 2 ^ 59
def prefixEnd_7951904 : Nat := 4983230072969 + 3 ^ 40 * 7951904 * 2
def baseEnd_7951904 : Nat := 1361049623470053790909955

theorem tailTrace_7951904 : CollatzResearch.WordTrace tailWord_7951904 prefixEnd_7951904 1361049623470053790909955 := by
  unfold tailWord_7951904
  simp only [CollatzResearch.WordTrace]
  refine ⟨145014882891808679963135383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193353177189078239950847177 145014882891808679963135383)
  ·
    refine ⟨217522324337713019944703075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145014882891808679963135383 217522324337713019944703075)
    ·
      refine ⟨326283486506569529917054613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217522324337713019944703075 326283486506569529917054613)
      ·
        refine ⟨15294538429995446714861935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 326283486506569529917054613 15294538429995446714861935)
        ·
          refine ⟨22941807644993170072292903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15294538429995446714861935 22941807644993170072292903)
          ·
            refine ⟨34412711467489755108439355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22941807644993170072292903 34412711467489755108439355)
            ·
              refine ⟨51619067201234632662659033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34412711467489755108439355 51619067201234632662659033)
              ·
                refine ⟨38714300400925974496994275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51619067201234632662659033 38714300400925974496994275)
                ·
                  refine ⟨58071450601388961745491413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38714300400925974496994275 58071450601388961745491413)
                  ·
                    refine ⟨1361049623470053790909955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58071450601388961745491413 1361049623470053790909955)
                    ·
                      rfl

theorem cell23_7951904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 2, 1, 7].length) (baseStart_7951904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7951904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7951904 prefixEnd_7951904 := by exact prefixLift 7951904
  have htrace : WordTrace (prefixWord ++ tailWord_7951904) baseStart_7951904 baseEnd_7951904 := by
    simpa [prefixWord, tailWord_7951904, baseEnd_7951904] using wordTrace_append hprefix tailTrace_7951904
  have hstable : (prefixWord ++ tailWord_7951904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7951904).length < 2 ^ (prefixWord ++ tailWord_7951904).sum := by decide
  have hdescent : baseEnd_7951904 < baseStart_7951904 := by decide
  rcases family_descends (prefixWord ++ tailWord_7951904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7951942 : List Nat := [6, 1, 1, 1, 3, 1, 3, 2, 5]
def baseStart_7951942 : Nat := 118140960795 + 7951942 * 2 ^ 59
def prefixEnd_7951942 : Nat := 4983230072969 + 3 ^ 40 * 7951942 * 2
def baseEnd_7951942 : Nat := 453685375852781358228299

theorem tailTrace_7951942 : CollatzResearch.WordTrace tailWord_7951942 prefixEnd_7951942 453685375852781358228299 := by
  unfold tailWord_7951942
  simp only [CollatzResearch.WordTrace]
  refine ⟨9063473492421240388004815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 193354101171653128277436053 9063473492421240388004815)
  ·
    refine ⟨13595210238631860582007223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9063473492421240388004815 13595210238631860582007223)
    ·
      refine ⟨20392815357947790873010835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13595210238631860582007223 20392815357947790873010835)
      ·
        refine ⟨30589223036921686309516253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20392815357947790873010835 30589223036921686309516253)
        ·
          refine ⟨11470958638845632366068595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30589223036921686309516253 11470958638845632366068595)
          ·
            refine ⟨17206437958268448549102893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11470958638845632366068595 17206437958268448549102893)
            ·
              refine ⟨6452414234350668205913585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17206437958268448549102893 6452414234350668205913585)
              ·
                refine ⟨4839310675763001154435189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6452414234350668205913585 4839310675763001154435189)
                ·
                  refine ⟨453685375852781358228299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4839310675763001154435189 453685375852781358228299)
                  ·
                    rfl

theorem cell23_7951942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 3, 2, 5].length) (baseStart_7951942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7951942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7951942 prefixEnd_7951942 := by exact prefixLift 7951942
  have htrace : WordTrace (prefixWord ++ tailWord_7951942) baseStart_7951942 baseEnd_7951942 := by
    simpa [prefixWord, tailWord_7951942, baseEnd_7951942] using wordTrace_append hprefix tailTrace_7951942
  have hstable : (prefixWord ++ tailWord_7951942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7951942).length < 2 ^ (prefixWord ++ tailWord_7951942).sum := by decide
  have hdescent : baseEnd_7951942 < baseStart_7951942 := by decide
  rcases family_descends (prefixWord ++ tailWord_7951942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7951978 : List Nat := [3, 1, 3, 2, 1, 3, 2, 1, 2, 2, 3]
def baseStart_7951978 : Nat := 118140960795 + 7951978 * 2 ^ 59
def prefixEnd_7951978 : Nat := 4983230072969 + 3 ^ 40 * 7951978 * 2
def baseEnd_7951978 : Nat := 4083186867978594083204525

theorem tailTrace_7951978 : CollatzResearch.WordTrace tailWord_7951978 prefixEnd_7951978 4083186867978594083204525 := by
  unfold tailWord_7951978
  simp only [CollatzResearch.WordTrace]
  refine ⟨72508116196337317641116147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193354976523566180376309725 72508116196337317641116147)
  ·
    refine ⟨108762174294505976461674221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72508116196337317641116147 108762174294505976461674221)
    ·
      refine ⟨40785815360439741173127833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108762174294505976461674221 40785815360439741173127833)
      ·
        refine ⟨30589361520329805879845875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40785815360439741173127833 30589361520329805879845875)
        ·
          refine ⟨45884042280494708819768813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30589361520329805879845875 45884042280494708819768813)
          ·
            refine ⟨17206515855185515807413305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45884042280494708819768813 17206515855185515807413305)
            ·
              refine ⟨12904886891389136855559979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17206515855185515807413305 12904886891389136855559979)
              ·
                refine ⟨19357330337083705283339969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12904886891389136855559979 19357330337083705283339969)
                ·
                  refine ⟨14517997752812778962504977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19357330337083705283339969 14517997752812778962504977)
                  ·
                    refine ⟨10888498314609584221878733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14517997752812778962504977 10888498314609584221878733)
                    ·
                      refine ⟨4083186867978594083204525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10888498314609584221878733 4083186867978594083204525)
                      ·
                        rfl

theorem cell23_7951978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_7951978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7951978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7951978 prefixEnd_7951978 := by exact prefixLift 7951978
  have htrace : WordTrace (prefixWord ++ tailWord_7951978) baseStart_7951978 baseEnd_7951978 := by
    simpa [prefixWord, tailWord_7951978, baseEnd_7951978] using wordTrace_append hprefix tailTrace_7951978
  have hstable : (prefixWord ++ tailWord_7951978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7951978).length < 2 ^ (prefixWord ++ tailWord_7951978).sum := by decide
  have hdescent : baseEnd_7951978 < baseStart_7951978 := by decide
  rcases family_descends (prefixWord ++ tailWord_7951978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7952048 : List Nat := [2, 1, 1, 1, 2, 1, 8, 1, 1, 1, 4]
def baseStart_7952048 : Nat := 118140960795 + 7952048 * 2 ^ 59
def prefixEnd_7952048 : Nat := 4983230072969 + 3 ^ 40 * 7952048 * 2
def baseEnd_7952048 : Nat := 4083222811624408809329203

theorem tailTrace_7952048 : CollatzResearch.WordTrace tailWord_7952048 prefixEnd_7952048 4083222811624408809329203 := by
  unfold tailWord_7952048
  simp only [CollatzResearch.WordTrace]
  refine ⟨145017508947547836259756399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193356678596730448346341865 145017508947547836259756399)
  ·
    refine ⟨217526263421321754389634599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145017508947547836259756399 217526263421321754389634599)
    ·
      refine ⟨326289395131982631584451899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217526263421321754389634599 326289395131982631584451899)
      ·
        refine ⟨489434092697973947376677849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326289395131982631584451899 489434092697973947376677849)
        ·
          refine ⟨367075569523480460532508387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 489434092697973947376677849 367075569523480460532508387)
          ·
            refine ⟨550613354285220690798762581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 367075569523480460532508387 550613354285220690798762581)
            ·
              refine ⟨6452500245529929970297999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 550613354285220690798762581 6452500245529929970297999)
              ·
                refine ⟨9678750368294894955446999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6452500245529929970297999 9678750368294894955446999)
                ·
                  refine ⟨14518125552442342433170499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9678750368294894955446999 14518125552442342433170499)
                  ·
                    refine ⟨21777188328663513649755749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14518125552442342433170499 21777188328663513649755749)
                    ·
                      refine ⟨4083222811624408809329203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21777188328663513649755749 4083222811624408809329203)
                      ·
                        rfl

theorem cell23_7952048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 8, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 8, 1, 1, 1, 4].length) (baseStart_7952048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7952048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7952048 prefixEnd_7952048 := by exact prefixLift 7952048
  have htrace : WordTrace (prefixWord ++ tailWord_7952048) baseStart_7952048 baseEnd_7952048 := by
    simpa [prefixWord, tailWord_7952048, baseEnd_7952048] using wordTrace_append hprefix tailTrace_7952048
  have hstable : (prefixWord ++ tailWord_7952048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7952048).length < 2 ^ (prefixWord ++ tailWord_7952048).sum := by decide
  have hdescent : baseEnd_7952048 < baseStart_7952048 := by decide
  rcases family_descends (prefixWord ++ tailWord_7952048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7952058 : List Nat := [3, 1, 1, 1, 2, 4, 3, 2, 2, 4]
def baseStart_7952058 : Nat := 118140960795 + 7952058 * 2 ^ 59
def prefixEnd_7952058 : Nat := 4983230072969 + 3 ^ 40 * 7952058 * 2
def baseEnd_7952058 : Nat := 1361075982143651256734719

theorem tailTrace_7952058 : CollatzResearch.WordTrace tailWord_7952058 prefixEnd_7952058 1361075982143651256734719 := by
  unfold tailWord_7952058
  simp only [CollatzResearch.WordTrace]
  refine ⟨72508845656264861056844207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193356921750039629484917885 72508845656264861056844207)
  ·
    refine ⟨108763268484397291585266311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72508845656264861056844207 108763268484397291585266311)
    ·
      refine ⟨163144902726595937377899467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108763268484397291585266311 163144902726595937377899467)
      ·
        refine ⟨244717354089893906066849201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163144902726595937377899467 244717354089893906066849201)
        ·
          refine ⟨183538015567420429550136901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244717354089893906066849201 183538015567420429550136901)
          ·
            refine ⟨34413377918891330540650669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 183538015567420429550136901 34413377918891330540650669)
            ·
              refine ⟨12905016719584248952744001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34413377918891330540650669 12905016719584248952744001)
              ·
                refine ⟨9678762539688186714558001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12905016719584248952744001 9678762539688186714558001)
                ·
                  refine ⟨7259071904766140035918501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9678762539688186714558001 7259071904766140035918501)
                  ·
                    refine ⟨1361075982143651256734719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7259071904766140035918501 1361075982143651256734719)
                    ·
                      rfl

theorem cell23_7952058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 2, 2, 4].length) (baseStart_7952058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7952058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7952058 prefixEnd_7952058 := by exact prefixLift 7952058
  have htrace : WordTrace (prefixWord ++ tailWord_7952058) baseStart_7952058 baseEnd_7952058 := by
    simpa [prefixWord, tailWord_7952058, baseEnd_7952058] using wordTrace_append hprefix tailTrace_7952058
  have hstable : (prefixWord ++ tailWord_7952058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7952058).length < 2 ^ (prefixWord ++ tailWord_7952058).sum := by decide
  have hdescent : baseEnd_7952058 < baseStart_7952058 := by decide
  rcases family_descends (prefixWord ++ tailWord_7952058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7952116 : List Nat := [2, 6, 1, 1, 1, 3, 1, 1, 3, 2, 2]
def baseStart_7952116 : Nat := 118140960795 + 7952116 * 2 ^ 59
def prefixEnd_7952116 : Nat := 4983230072969 + 3 ^ 40 * 7952116 * 2
def baseEnd_7952116 : Nat := 4083257728308914543278891

theorem tailTrace_7952116 : CollatzResearch.WordTrace tailWord_7952116 prefixEnd_7952116 4083257728308914543278891 := by
  unfold tailWord_7952116
  simp only [CollatzResearch.WordTrace]
  refine ⟨145018749029424660066494101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193358332039232880088658801 145018749029424660066494101)
  ·
    refine ⟨6797753860754280940616911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 145018749029424660066494101 6797753860754280940616911)
    ·
      refine ⟨10196630791131421410925367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6797753860754280940616911 10196630791131421410925367)
      ·
        refine ⟨15294946186697132116388051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10196630791131421410925367 15294946186697132116388051)
        ·
          refine ⟨22942419280045698174582077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15294946186697132116388051 22942419280045698174582077)
          ·
            refine ⟨8603407230017136815468279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22942419280045698174582077 8603407230017136815468279)
            ·
              refine ⟨12905110845025705223202419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8603407230017136815468279 12905110845025705223202419)
              ·
                refine ⟨19357666267538557834803629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12905110845025705223202419 19357666267538557834803629)
                ·
                  refine ⟨7259124850326959188051361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19357666267538557834803629 7259124850326959188051361)
                  ·
                    refine ⟨5444343637745219391038521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7259124850326959188051361 5444343637745219391038521)
                    ·
                      refine ⟨4083257728308914543278891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5444343637745219391038521 4083257728308914543278891)
                      ·
                        rfl

theorem cell23_7952116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_7952116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7952116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7952116 prefixEnd_7952116 := by exact prefixLift 7952116
  have htrace : WordTrace (prefixWord ++ tailWord_7952116) baseStart_7952116 baseEnd_7952116 := by
    simpa [prefixWord, tailWord_7952116, baseEnd_7952116] using wordTrace_append hprefix tailTrace_7952116
  have hstable : (prefixWord ++ tailWord_7952116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7952116).length < 2 ^ (prefixWord ++ tailWord_7952116).sum := by decide
  have hdescent : baseEnd_7952116 < baseStart_7952116 := by decide
  rcases family_descends (prefixWord ++ tailWord_7952116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7952132 : List Nat := [2, 3, 2, 2, 1, 2, 4, 1, 2, 1, 3]
def baseStart_7952132 : Nat := 118140960795 + 7952132 * 2 ^ 59
def prefixEnd_7952132 : Nat := 4983230072969 + 3 ^ 40 * 7952132 * 2
def baseEnd_7952132 : Nat := 4083265943999386480678817

theorem tailTrace_7952132 : CollatzResearch.WordTrace tailWord_7952132 prefixEnd_7952132 4083265943999386480678817 := by
  unfold tailWord_7952132
  simp only [CollatzResearch.WordTrace]
  refine ⟨145019040813395677432785325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193358721084527569910380433 145019040813395677432785325)
  ·
    refine ⟨54382140305023379037294497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145019040813395677432785325 54382140305023379037294497)
    ·
      refine ⟨40786605228767534277970873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54382140305023379037294497 40786605228767534277970873)
      ·
        refine ⟨30589953921575650708478155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40786605228767534277970873 30589953921575650708478155)
        ·
          refine ⟨45884930882363476062717233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30589953921575650708478155 45884930882363476062717233)
          ·
            refine ⟨34413698161772607047037925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45884930882363476062717233 34413698161772607047037925)
            ·
              refine ⟨6452568405332363821319611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34413698161772607047037925 6452568405332363821319611)
              ·
                refine ⟨9678852607998545731979417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6452568405332363821319611 9678852607998545731979417)
                ·
                  refine ⟨7259139455998909298984563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9678852607998545731979417 7259139455998909298984563)
                  ·
                    refine ⟨10888709183998363948476845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7259139455998909298984563 10888709183998363948476845)
                    ·
                      refine ⟨4083265943999386480678817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10888709183998363948476845 4083265943999386480678817)
                      ·
                        rfl

theorem cell23_7952132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 4, 1, 2, 1, 3].length) (baseStart_7952132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7952132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7952132 prefixEnd_7952132 := by exact prefixLift 7952132
  have htrace : WordTrace (prefixWord ++ tailWord_7952132) baseStart_7952132 baseEnd_7952132 := by
    simpa [prefixWord, tailWord_7952132, baseEnd_7952132] using wordTrace_append hprefix tailTrace_7952132
  have hstable : (prefixWord ++ tailWord_7952132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7952132).length < 2 ^ (prefixWord ++ tailWord_7952132).sum := by decide
  have hdescent : baseEnd_7952132 < baseStart_7952132 := by decide
  rcases family_descends (prefixWord ++ tailWord_7952132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7952172 : List Nat := [2, 2, 1, 1, 1, 6, 2, 2, 2, 2, 2]
def baseStart_7952172 : Nat := 118140960795 + 7952172 * 2 ^ 59
def prefixEnd_7952172 : Nat := 4983230072969 + 3 ^ 40 * 7952172 * 2
def baseEnd_7952172 : Nat := 4083286483225566324178633

theorem tailTrace_7952172 : CollatzResearch.WordTrace tailWord_7952172 prefixEnd_7952172 4083286483225566324178633 := by
  unfold tailWord_7952172
  simp only [CollatzResearch.WordTrace]
  refine ⟨145019770273323220848513385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193359693697764294464684513 145019770273323220848513385)
  ·
    refine ⟨108764827704992415636385039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145019770273323220848513385 108764827704992415636385039)
    ·
      refine ⟨163147241557488623454577559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108764827704992415636385039 163147241557488623454577559)
      ·
        refine ⟨244720862336232935181866339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163147241557488623454577559 244720862336232935181866339)
        ·
          refine ⟨367081293504349402772799509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244720862336232935181866339 367081293504349402772799509)
          ·
            refine ⟨17206935633016378254974977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 367081293504349402772799509 17206935633016378254974977)
            ·
              refine ⟨12905201724762283691231233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17206935633016378254974977 12905201724762283691231233)
              ·
                refine ⟨9678901293571712768423425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12905201724762283691231233 9678901293571712768423425)
                ·
                  refine ⟨7259175970178784576317569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9678901293571712768423425 7259175970178784576317569)
                  ·
                    refine ⟨5444381977634088432238177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7259175970178784576317569 5444381977634088432238177)
                    ·
                      refine ⟨4083286483225566324178633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5444381977634088432238177 4083286483225566324178633)
                      ·
                        rfl

theorem cell23_7952172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 2, 2].length) (baseStart_7952172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7952172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7952172 prefixEnd_7952172 := by exact prefixLift 7952172
  have htrace : WordTrace (prefixWord ++ tailWord_7952172) baseStart_7952172 baseEnd_7952172 := by
    simpa [prefixWord, tailWord_7952172, baseEnd_7952172] using wordTrace_append hprefix tailTrace_7952172
  have hstable : (prefixWord ++ tailWord_7952172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7952172).length < 2 ^ (prefixWord ++ tailWord_7952172).sum := by decide
  have hdescent : baseEnd_7952172 < baseStart_7952172 := by decide
  rcases family_descends (prefixWord ++ tailWord_7952172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7952185 : List Nat := [1, 2, 1, 7, 1, 1, 1, 1, 2, 2, 4]
def baseStart_7952185 : Nat := 118140960795 + 7952185 * 2 ^ 59
def prefixEnd_7952185 : Nat := 4983230072969 + 3 ^ 40 * 7952185 * 2
def baseEnd_7952185 : Nat := 4083293158474074773316073

theorem tailTrace_7952185 : CollatzResearch.WordTrace tailWord_7952185 prefixEnd_7952185 4083293158474074773316073 := by
  unfold tailWord_7952185
  simp only [CollatzResearch.WordTrace]
  refine ⟨290040014695599344917250009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193360009797066229944833339 290040014695599344917250009)
  ·
    refine ⟨217530011021699508687937507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290040014695599344917250009 217530011021699508687937507)
    ·
      refine ⟨326295016532549263031906261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217530011021699508687937507 326295016532549263031906261)
      ·
        refine ⟨7647539449981623352310303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 326295016532549263031906261 7647539449981623352310303)
        ·
          refine ⟨11471309174972435028465455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7647539449981623352310303 11471309174972435028465455)
          ·
            refine ⟨17206963762458652542698183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11471309174972435028465455 17206963762458652542698183)
            ·
              refine ⟨25810445643687978814047275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17206963762458652542698183 25810445643687978814047275)
              ·
                refine ⟨38715668465531968221070913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25810445643687978814047275 38715668465531968221070913)
                ·
                  refine ⟨29036751349148976165803185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38715668465531968221070913 29036751349148976165803185)
                  ·
                    refine ⟨21777563511861732124352389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29036751349148976165803185 21777563511861732124352389)
                    ·
                      refine ⟨4083293158474074773316073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21777563511861732124352389 4083293158474074773316073)
                      ·
                        rfl

theorem cell23_7952185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_7952185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7952185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7952185 prefixEnd_7952185 := by exact prefixLift 7952185
  have htrace : WordTrace (prefixWord ++ tailWord_7952185) baseStart_7952185 baseEnd_7952185 := by
    simpa [prefixWord, tailWord_7952185, baseEnd_7952185] using wordTrace_append hprefix tailTrace_7952185
  have hstable : (prefixWord ++ tailWord_7952185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7952185).length < 2 ^ (prefixWord ++ tailWord_7952185).sum := by decide
  have hdescent : baseEnd_7952185 < baseStart_7952185 := by decide
  rcases family_descends (prefixWord ++ tailWord_7952185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7952241 : List Nat := [1, 2, 2, 2, 1, 3, 1, 2, 2, 1, 6]
def baseStart_7952241 : Nat := 118140960795 + 7952241 * 2 ^ 59
def prefixEnd_7952241 : Nat := 4983230072969 + 3 ^ 40 * 7952241 * 2
def baseEnd_7952241 : Nat := 4083321913390726554215815

theorem tailTrace_7952241 : CollatzResearch.WordTrace tailWord_7952241 prefixEnd_7952241 4083321913390726554215815 := by
  unfold tailWord_7952241
  simp only [CollatzResearch.WordTrace]
  refine ⟨290042057183396466481288577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193361371455597644320859051 290042057183396466481288577)
  ·
    refine ⟨217531542887547349860966433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290042057183396466481288577 217531542887547349860966433)
    ·
      refine ⟨163148657165660512395724825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217531542887547349860966433 163148657165660512395724825)
      ·
        refine ⟨122361492874245384296793619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163148657165660512395724825 122361492874245384296793619)
        ·
          refine ⟨183542239311368076445190429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122361492874245384296793619 183542239311368076445190429)
          ·
            refine ⟨68828339741763028666946411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183542239311368076445190429 68828339741763028666946411)
            ·
              refine ⟨103242509612644543000419617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68828339741763028666946411 103242509612644543000419617)
              ·
                refine ⟨77431882209483407250314713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103242509612644543000419617 77431882209483407250314713)
                ·
                  refine ⟨58073911657112555437736035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77431882209483407250314713 58073911657112555437736035)
                  ·
                    refine ⟨87110867485668833156604053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58073911657112555437736035 87110867485668833156604053)
                    ·
                      refine ⟨4083321913390726554215815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87110867485668833156604053 4083321913390726554215815)
                      ·
                        rfl

theorem cell23_7952241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2, 1, 6].length) (baseStart_7952241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7952241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7952241 prefixEnd_7952241 := by exact prefixLift 7952241
  have htrace : WordTrace (prefixWord ++ tailWord_7952241) baseStart_7952241 baseEnd_7952241 := by
    simpa [prefixWord, tailWord_7952241, baseEnd_7952241] using wordTrace_append hprefix tailTrace_7952241
  have hstable : (prefixWord ++ tailWord_7952241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7952241).length < 2 ^ (prefixWord ++ tailWord_7952241).sum := by decide
  have hdescent : baseEnd_7952241 < baseStart_7952241 := by decide
  rcases family_descends (prefixWord ++ tailWord_7952241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7952245 : List Nat := [1, 3, 4, 1, 1, 1, 1, 3, 2, 4, 2]
def baseStart_7952245 : Nat := 118140960795 + 7952245 * 2 ^ 59
def prefixEnd_7952245 : Nat := 4983230072969 + 3 ^ 40 * 7952245 * 2
def baseEnd_7952245 : Nat := 4083323967313344538565797

theorem tailTrace_7952245 : CollatzResearch.WordTrace tailWord_7952245 prefixEnd_7952245 4083323967313344538565797 := by
  unfold tailWord_7952245
  simp only [CollatzResearch.WordTrace]
  refine ⟨290042203075381975164434189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193361468716921316776289459 290042203075381975164434189)
  ·
    refine ⟨108765826153268240686662821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290042203075381975164434189 108765826153268240686662821)
    ·
      refine ⟨20393592403737795128749279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108765826153268240686662821 20393592403737795128749279)
      ·
        refine ⟨30590388605606692693123919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20393592403737795128749279 30590388605606692693123919)
        ·
          refine ⟨45885582908410039039685879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30590388605606692693123919 45885582908410039039685879)
          ·
            refine ⟨68828374362615058559528819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45885582908410039039685879 68828374362615058559528819)
            ·
              refine ⟨103242561543922587839293229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68828374362615058559528819 103242561543922587839293229)
              ·
                refine ⟨38715960578970970439734961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103242561543922587839293229 38715960578970970439734961)
                ·
                  refine ⟨29036970434228227829801221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38715960578970970439734961 29036970434228227829801221)
                  ·
                    refine ⟨5444431956417792718087729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29036970434228227829801221 5444431956417792718087729)
                    ·
                      refine ⟨4083323967313344538565797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5444431956417792718087729 4083323967313344538565797)
                      ·
                        rfl

theorem cell23_7952245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 3, 2, 4, 2].length) (baseStart_7952245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7952245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7952245 prefixEnd_7952245 := by exact prefixLift 7952245
  have htrace : WordTrace (prefixWord ++ tailWord_7952245) baseStart_7952245 baseEnd_7952245 := by
    simpa [prefixWord, tailWord_7952245, baseEnd_7952245] using wordTrace_append hprefix tailTrace_7952245
  have hstable : (prefixWord ++ tailWord_7952245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7952245).length < 2 ^ (prefixWord ++ tailWord_7952245).sum := by decide
  have hdescent : baseEnd_7952245 < baseStart_7952245 := by decide
  rcases family_descends (prefixWord ++ tailWord_7952245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7952289 : List Nat := [1, 2, 3, 4, 3, 1, 1, 1, 3, 4]
def baseStart_7952289 : Nat := 118140960795 + 7952289 * 2 ^ 59
def prefixEnd_7952289 : Nat := 4983230072969 + 3 ^ 40 * 7952289 * 2
def baseEnd_7952289 : Nat := 1361115520154047455471865

theorem tailTrace_7952289 : CollatzResearch.WordTrace tailWord_7952289 prefixEnd_7952289 1361115520154047455471865 := by
  unfold tailWord_7952289
  simp only [CollatzResearch.WordTrace]
  refine ⟨290043807887222570679035921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193362538591481713786023947 290043807887222570679035921)
  ·
    refine ⟨217532855915416928009276941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290043807887222570679035921 217532855915416928009276941)
    ·
      refine ⟨81574820968281348003478853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217532855915416928009276941 81574820968281348003478853)
      ·
        refine ⟨15295278931552752750652285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81574820968281348003478853 15295278931552752750652285)
        ·
          refine ⟨5735729599332282281494607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15295278931552752750652285 5735729599332282281494607)
          ·
            refine ⟨8603594398998423422241911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5735729599332282281494607 8603594398998423422241911)
            ·
              refine ⟨12905391598497635133362867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8603594398998423422241911 12905391598497635133362867)
              ·
                refine ⟨19358087397746452700044301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12905391598497635133362867 19358087397746452700044301)
                ·
                  refine ⟨7259282774154919762516613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19358087397746452700044301 7259282774154919762516613)
                  ·
                    refine ⟨1361115520154047455471865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7259282774154919762516613 1361115520154047455471865)
                    ·
                      rfl

theorem cell23_7952289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 1, 3, 4].length) (baseStart_7952289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7952289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7952289 prefixEnd_7952289 := by exact prefixLift 7952289
  have htrace : WordTrace (prefixWord ++ tailWord_7952289) baseStart_7952289 baseEnd_7952289 := by
    simpa [prefixWord, tailWord_7952289, baseEnd_7952289] using wordTrace_append hprefix tailTrace_7952289
  have hstable : (prefixWord ++ tailWord_7952289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7952289).length < 2 ^ (prefixWord ++ tailWord_7952289).sum := by decide
  have hdescent : baseEnd_7952289 < baseStart_7952289 := by decide
  rcases family_descends (prefixWord ++ tailWord_7952289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7952291 : List Nat := [1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 7]
def baseStart_7952291 : Nat := 118140960795 + 7952291 * 2 ^ 59
def prefixEnd_7952291 : Nat := 4983230072969 + 3 ^ 40 * 7952291 * 2
def baseEnd_7952291 : Nat := 4083347587423451358590585

theorem tailTrace_7952291 : CollatzResearch.WordTrace tailWord_7952291 prefixEnd_7952291 4083347587423451358590585 := by
  unfold tailWord_7952291
  simp only [CollatzResearch.WordTrace]
  refine ⟨290043880833215325020608727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193362587222143550013739151 290043880833215325020608727)
  ·
    refine ⟨435065821249822987530913091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290043880833215325020608727 435065821249822987530913091)
    ·
      refine ⟨652598731874734481296369637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435065821249822987530913091 652598731874734481296369637)
      ·
        refine ⟨122362262226512715243069307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 652598731874734481296369637 122362262226512715243069307)
        ·
          refine ⟨183543393339769072864603961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122362262226512715243069307 183543393339769072864603961)
          ·
            refine ⟨137657545004826804648452971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183543393339769072864603961 137657545004826804648452971)
            ·
              refine ⟨206486317507240206972679457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137657545004826804648452971 206486317507240206972679457)
              ·
                refine ⟨154864738130430155229509593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 206486317507240206972679457 154864738130430155229509593)
                ·
                  refine ⟨116148553597822616422132195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 154864738130430155229509593 116148553597822616422132195)
                  ·
                    refine ⟨174222830396733924633198293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 116148553597822616422132195 174222830396733924633198293)
                    ·
                      refine ⟨4083347587423451358590585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 174222830396733924633198293 4083347587423451358590585)
                      ·
                        rfl

theorem cell23_7952291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 7].length) (baseStart_7952291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7952291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7952291 prefixEnd_7952291 := by exact prefixLift 7952291
  have htrace : WordTrace (prefixWord ++ tailWord_7952291) baseStart_7952291 baseEnd_7952291 := by
    simpa [prefixWord, tailWord_7952291, baseEnd_7952291] using wordTrace_append hprefix tailTrace_7952291
  have hstable : (prefixWord ++ tailWord_7952291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7952291).length < 2 ^ (prefixWord ++ tailWord_7952291).sum := by decide
  have hdescent : baseEnd_7952291 < baseStart_7952291 := by decide
  rcases family_descends (prefixWord ++ tailWord_7952291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7952328 : List Nat := [2, 1, 3, 1, 4, 1, 1, 1, 3, 6]
def baseStart_7952328 : Nat := 118140960795 + 7952328 * 2 ^ 59
def prefixEnd_7952328 : Nat := 4983230072969 + 3 ^ 40 * 7952328 * 2
def baseEnd_7952328 : Nat := 1361122195402555904609305

theorem tailTrace_7952328 : CollatzResearch.WordTrace tailWord_7952328 prefixEnd_7952328 1361122195402555904609305 := by
  unfold tailWord_7952328
  simp only [CollatzResearch.WordTrace]
  refine ⟨145022615167040640169852819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193363486889387520226470425 145022615167040640169852819)
  ·
    refine ⟨217533922750560960254779229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145022615167040640169852819 217533922750560960254779229)
    ·
      refine ⟨81575221031460360095542211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217533922750560960254779229 81575221031460360095542211)
      ·
        refine ⟨122362831547190540143313317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81575221031460360095542211 122362831547190540143313317)
        ·
          refine ⟨22943030915098226276871247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122362831547190540143313317 22943030915098226276871247)
          ·
            refine ⟨34414546372647339415306871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22943030915098226276871247 34414546372647339415306871)
            ·
              refine ⟨51621819558971009122960307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34414546372647339415306871 51621819558971009122960307)
              ·
                refine ⟨77432729338456513684440461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51621819558971009122960307 77432729338456513684440461)
                ·
                  refine ⟨29037273501921192631665173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77432729338456513684440461 29037273501921192631665173)
                  ·
                    refine ⟨1361122195402555904609305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29037273501921192631665173 1361122195402555904609305)
                    ·
                      rfl

theorem cell23_7952328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 3, 6].length) (baseStart_7952328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7952328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7952328 prefixEnd_7952328 := by exact prefixLift 7952328
  have htrace : WordTrace (prefixWord ++ tailWord_7952328) baseStart_7952328 baseEnd_7952328 := by
    simpa [prefixWord, tailWord_7952328, baseEnd_7952328] using wordTrace_append hprefix tailTrace_7952328
  have hstable : (prefixWord ++ tailWord_7952328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7952328).length < 2 ^ (prefixWord ++ tailWord_7952328).sum := by decide
  have hdescent : baseEnd_7952328 < baseStart_7952328 := by decide
  rcases family_descends (prefixWord ++ tailWord_7952328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7952332 : List Nat := [2, 2, 1, 4, 1, 3, 3, 1, 1, 5]
def baseStart_7952332 : Nat := 118140960795 + 7952332 * 2 ^ 59
def prefixEnd_7952332 : Nat := 4983230072969 + 3 ^ 40 * 7952332 * 2
def baseEnd_7952332 : Nat := 1361122880043428566059299

theorem tailTrace_7952332 : CollatzResearch.WordTrace tailWord_7952332 prefixEnd_7952332 1361122880043428566059299 := by
  unfold tailWord_7952332
  simp only [CollatzResearch.WordTrace]
  refine ⟨145022688113033394511425625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193363584150711192681900833 145022688113033394511425625)
  ·
    refine ⟨108767016084775045883569219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145022688113033394511425625 108767016084775045883569219)
    ·
      refine ⟨163150524127162568825353829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108767016084775045883569219 163150524127162568825353829)
      ·
        refine ⟨30590723273842981654753843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163150524127162568825353829 30590723273842981654753843)
        ·
          refine ⟨45886084910764472482130765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30590723273842981654753843 45886084910764472482130765)
          ·
            refine ⟨17207281841536677180799037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45886084910764472482130765 17207281841536677180799037)
            ·
              refine ⟨6452730690576253942799639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17207281841536677180799037 6452730690576253942799639)
              ·
                refine ⟨9679096035864380914199459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6452730690576253942799639 9679096035864380914199459)
                ·
                  refine ⟨14518644053796571371299189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9679096035864380914199459 14518644053796571371299189)
                  ·
                    refine ⟨1361122880043428566059299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14518644053796571371299189 1361122880043428566059299)
                    ·
                      rfl

theorem cell23_7952332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 3, 1, 1, 5].length) (baseStart_7952332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7952332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7952332 prefixEnd_7952332 := by exact prefixLift 7952332
  have htrace : WordTrace (prefixWord ++ tailWord_7952332) baseStart_7952332 baseEnd_7952332 := by
    simpa [prefixWord, tailWord_7952332, baseEnd_7952332] using wordTrace_append hprefix tailTrace_7952332
  have hstable : (prefixWord ++ tailWord_7952332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7952332).length < 2 ^ (prefixWord ++ tailWord_7952332).sum := by decide
  have hdescent : baseEnd_7952332 < baseStart_7952332 := by decide
  rcases family_descends (prefixWord ++ tailWord_7952332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7952355 : List Nat := [1, 1, 1, 6, 1, 2, 1, 2, 3, 2, 3]
def baseStart_7952355 : Nat := 118140960795 + 7952355 * 2 ^ 59
def prefixEnd_7952355 : Nat := 4983230072969 + 3 ^ 40 * 7952355 * 2
def baseEnd_7952355 : Nat := 4083380450185339108190291

theorem tailTrace_7952355 : CollatzResearch.WordTrace tailWord_7952355 prefixEnd_7952355 4083380450185339108190291 := by
  unfold tailWord_7952355
  simp only [CollatzResearch.WordTrace]
  refine ⟨290046215104983463950938519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193364143403322309300625679 290046215104983463950938519)
  ·
    refine ⟨435069322657475195926407779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290046215104983463950938519 435069322657475195926407779)
    ·
      refine ⟨652603983986212793889611669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435069322657475195926407779 652603983986212793889611669)
      ·
        refine ⟨30590811749353724713575547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 652603983986212793889611669 30590811749353724713575547)
        ·
          refine ⟨45886217624030587070363321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30590811749353724713575547 45886217624030587070363321)
          ·
            refine ⟨34414663218022940302772491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45886217624030587070363321 34414663218022940302772491)
            ·
              refine ⟨51621994827034410454158737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34414663218022940302772491 51621994827034410454158737)
              ·
                refine ⟨38716496120275807840619053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51621994827034410454158737 38716496120275807840619053)
                ·
                  refine ⟨14518686045103427940232145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38716496120275807840619053 14518686045103427940232145)
                  ·
                    refine ⟨10889014533827570955174109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14518686045103427940232145 10889014533827570955174109)
                    ·
                      refine ⟨4083380450185339108190291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10889014533827570955174109 4083380450185339108190291)
                      ·
                        rfl

theorem cell23_7952355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_7952355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7952355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7952355 prefixEnd_7952355 := by exact prefixLift 7952355
  have htrace : WordTrace (prefixWord ++ tailWord_7952355) baseStart_7952355 baseEnd_7952355 := by
    simpa [prefixWord, tailWord_7952355, baseEnd_7952355] using wordTrace_append hprefix tailTrace_7952355
  have hstable : (prefixWord ++ tailWord_7952355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7952355).length < 2 ^ (prefixWord ++ tailWord_7952355).sum := by decide
  have hdescent : baseEnd_7952355 < baseStart_7952355 := by decide
  rcases family_descends (prefixWord ++ tailWord_7952355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7952369 : List Nat := [1, 2, 2, 2, 5, 1, 1, 2, 3, 2, 2]
def baseStart_7952369 : Nat := 118140960795 + 7952369 * 2 ^ 59
def prefixEnd_7952369 : Nat := 4983230072969 + 3 ^ 40 * 7952369 * 2
def baseEnd_7952369 : Nat := 4083387638914502053415227

theorem tailTrace_7952369 : CollatzResearch.WordTrace tailWord_7952369 prefixEnd_7952369 4083387638914502053415227 := by
  unfold tailWord_7952369
  simp only [CollatzResearch.WordTrace]
  refine ⟨290046725726932744341948161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193364483817955162894632107 290046725726932744341948161)
  ·
    refine ⟨217535044295199558256461121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290046725726932744341948161 217535044295199558256461121)
    ·
      refine ⟨163151283221399668692345841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217535044295199558256461121 163151283221399668692345841)
      ·
        refine ⟨122363462416049751519259381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163151283221399668692345841 122363462416049751519259381)
        ·
          refine ⟨11471574601504664204930567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 122363462416049751519259381 11471574601504664204930567)
          ·
            refine ⟨17207361902256996307395851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11471574601504664204930567 17207361902256996307395851)
            ·
              refine ⟨25811042853385494461093777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17207361902256996307395851 25811042853385494461093777)
              ·
                refine ⟨19358282140039120845820333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25811042853385494461093777 19358282140039120845820333)
                ·
                  refine ⟨7259355802514670317182625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19358282140039120845820333 7259355802514670317182625)
                  ·
                    refine ⟨5444516851886002737886969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7259355802514670317182625 5444516851886002737886969)
                    ·
                      refine ⟨4083387638914502053415227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5444516851886002737886969 4083387638914502053415227)
                      ·
                        rfl

theorem cell23_7952369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 2, 3, 2, 2].length) (baseStart_7952369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7952369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7952369 prefixEnd_7952369 := by exact prefixLift 7952369
  have htrace : WordTrace (prefixWord ++ tailWord_7952369) baseStart_7952369 baseEnd_7952369 := by
    simpa [prefixWord, tailWord_7952369, baseEnd_7952369] using wordTrace_append hprefix tailTrace_7952369
  have hstable : (prefixWord ++ tailWord_7952369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7952369).length < 2 ^ (prefixWord ++ tailWord_7952369).sum := by decide
  have hdescent : baseEnd_7952369 < baseStart_7952369 := by decide
  rcases family_descends (prefixWord ++ tailWord_7952369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7952382 : List Nat := [4, 2, 2, 2, 1, 1, 2, 2, 1, 2, 4]
def baseStart_7952382 : Nat := 118140960795 + 7952382 * 2 ^ 59
def prefixEnd_7952382 : Nat := 4983230072969 + 3 ^ 40 * 7952382 * 2
def baseEnd_7952382 : Nat := 4083394314163010502552667

theorem tailTrace_7952382 : CollatzResearch.WordTrace tailWord_7952382 prefixEnd_7952382 4083394314163010502552667 := by
  unfold tailWord_7952382
  simp only [CollatzResearch.WordTrace]
  refine ⟨36255899984485705945271425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193364799917257098374780933 36255899984485705945271425)
  ·
    refine ⟨27191924988364279458953569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36255899984485705945271425 27191924988364279458953569)
    ·
      refine ⟨20393943741273209594215177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27191924988364279458953569 20393943741273209594215177)
      ·
        refine ⟨15295457805954907195661383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20393943741273209594215177 15295457805954907195661383)
        ·
          refine ⟨22943186708932360793492075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15295457805954907195661383 22943186708932360793492075)
          ·
            refine ⟨34414780063398541190238113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22943186708932360793492075 34414780063398541190238113)
            ·
              refine ⟨25811085047548905892678585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34414780063398541190238113 25811085047548905892678585)
              ·
                refine ⟨19358313785661679419508939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25811085047548905892678585 19358313785661679419508939)
                ·
                  refine ⟨29037470678492519129263409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19358313785661679419508939 29037470678492519129263409)
                  ·
                    refine ⟨21778103008869389346947557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29037470678492519129263409 21778103008869389346947557)
                    ·
                      refine ⟨4083394314163010502552667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21778103008869389346947557 4083394314163010502552667)
                      ·
                        rfl

theorem cell23_7952382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_7952382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7952382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7952382 prefixEnd_7952382 := by exact prefixLift 7952382
  have htrace : WordTrace (prefixWord ++ tailWord_7952382) baseStart_7952382 baseEnd_7952382 := by
    simpa [prefixWord, tailWord_7952382, baseEnd_7952382] using wordTrace_append hprefix tailTrace_7952382
  have hstable : (prefixWord ++ tailWord_7952382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7952382).length < 2 ^ (prefixWord ++ tailWord_7952382).sum := by decide
  have hdescent : baseEnd_7952382 < baseStart_7952382 := by decide
  rcases family_descends (prefixWord ++ tailWord_7952382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7952385 : List Nat := [1, 2, 4, 1, 2, 1, 1, 4, 1, 3, 3]
def baseStart_7952385 : Nat := 118140960795 + 7952385 * 2 ^ 59
def prefixEnd_7952385 : Nat := 4983230072969 + 3 ^ 40 * 7952385 * 2
def baseEnd_7952385 : Nat := 4083395854604973990815153

theorem tailTrace_7952385 : CollatzResearch.WordTrace tailWord_7952385 prefixEnd_7952385 4083395854604973990815153 := by
  unfold tailWord_7952385
  simp only [CollatzResearch.WordTrace]
  refine ⟨290047309294874779074530609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193364872863249852716353739 290047309294874779074530609)
  ·
    refine ⟨217535481971156084305897957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290047309294874779074530609 217535481971156084305897957)
    ·
      refine ⟨40787902869591765807355867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 217535481971156084305897957 40787902869591765807355867)
      ·
        refine ⟨61181854304387648711033801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40787902869591765807355867 61181854304387648711033801)
        ·
          refine ⟨45886390728290736533275351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61181854304387648711033801 45886390728290736533275351)
          ·
            refine ⟨68829586092436104799913027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45886390728290736533275351 68829586092436104799913027)
            ·
              refine ⟨103244379138654157199869541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68829586092436104799913027 103244379138654157199869541)
              ·
                refine ⟨19358321088497654474975539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103244379138654157199869541 19358321088497654474975539)
                ·
                  refine ⟨29037481632746481712463309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19358321088497654474975539 29037481632746481712463309)
                  ·
                    refine ⟨10889055612279930642173741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29037481632746481712463309 10889055612279930642173741)
                    ·
                      refine ⟨4083395854604973990815153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10889055612279930642173741 4083395854604973990815153)
                      ·
                        rfl

theorem cell23_7952385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 4, 1, 3, 3].length) (baseStart_7952385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7952385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7952385 prefixEnd_7952385 := by exact prefixLift 7952385
  have htrace : WordTrace (prefixWord ++ tailWord_7952385) baseStart_7952385 baseEnd_7952385 := by
    simpa [prefixWord, tailWord_7952385, baseEnd_7952385] using wordTrace_append hprefix tailTrace_7952385
  have hstable : (prefixWord ++ tailWord_7952385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7952385).length < 2 ^ (prefixWord ++ tailWord_7952385).sum := by decide
  have hdescent : baseEnd_7952385 < baseStart_7952385 := by decide
  rcases family_descends (prefixWord ++ tailWord_7952385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7952389 : List Nat := [1, 3, 1, 1, 2, 6, 2, 1, 1, 2, 3]
def baseStart_7952389 : Nat := 118140960795 + 7952389 * 2 ^ 59
def prefixEnd_7952389 : Nat := 4983230072969 + 3 ^ 40 * 7952389 * 2
def baseEnd_7952389 : Nat := 4083397908527591975165135

theorem tailTrace_7952389 : CollatzResearch.WordTrace tailWord_7952389 prefixEnd_7952389 4083397908527591975165135 := by
  unfold tailWord_7952389
  simp only [CollatzResearch.WordTrace]
  refine ⟨290047455186860287757676221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193364970124573525171784147 290047455186860287757676221)
  ·
    refine ⟨108767795695072607909128583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290047455186860287757676221 108767795695072607909128583)
    ·
      refine ⟨163151693542608911863692875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108767795695072607909128583 163151693542608911863692875)
      ·
        refine ⟨244727540313913367795539313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163151693542608911863692875 244727540313913367795539313)
        ·
          refine ⟨183545655235435025846654485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244727540313913367795539313 183545655235435025846654485)
          ·
            refine ⟨8603702589161016836561929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 183545655235435025846654485 8603702589161016836561929)
            ·
              refine ⟨6452776941870762627421447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8603702589161016836561929 6452776941870762627421447)
              ·
                refine ⟨9679165412806143941132171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6452776941870762627421447 9679165412806143941132171)
                ·
                  refine ⟨14518748119209215911698257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9679165412806143941132171 14518748119209215911698257)
                  ·
                    refine ⟨10889061089406911933773693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14518748119209215911698257 10889061089406911933773693)
                    ·
                      refine ⟨4083397908527591975165135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10889061089406911933773693 4083397908527591975165135)
                      ·
                        rfl

theorem cell23_7952389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 2, 1, 1, 2, 3].length) (baseStart_7952389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7952389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7952389 prefixEnd_7952389 := by exact prefixLift 7952389
  have htrace : WordTrace (prefixWord ++ tailWord_7952389) baseStart_7952389 baseEnd_7952389 := by
    simpa [prefixWord, tailWord_7952389, baseEnd_7952389] using wordTrace_append hprefix tailTrace_7952389
  have hstable : (prefixWord ++ tailWord_7952389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7952389).length < 2 ^ (prefixWord ++ tailWord_7952389).sum := by decide
  have hdescent : baseEnd_7952389 < baseStart_7952389 := by decide
  rcases family_descends (prefixWord ++ tailWord_7952389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7952419 : List Nat := [1, 1, 1, 4, 3, 1, 5, 1, 2, 1, 3]
def baseStart_7952419 : Nat := 118140960795 + 7952419 * 2 ^ 59
def prefixEnd_7952419 : Nat := 4983230072969 + 3 ^ 40 * 7952419 * 2
def baseEnd_7952419 : Nat := 4083413312947226857789997

theorem tailTrace_7952419 : CollatzResearch.WordTrace tailWord_7952419 prefixEnd_7952419 4083413312947226857789997 := by
  unfold tailWord_7952419
  simp only [CollatzResearch.WordTrace]
  refine ⟨290048549376751602881268311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193365699584501068587512207 290048549376751602881268311)
  ·
    refine ⟨435072824065127404321902467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290048549376751602881268311 435072824065127404321902467)
    ·
      refine ⟨652609236097691106482853701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435072824065127404321902467 652609236097691106482853701)
      ·
        refine ⟨122364231768317082465535069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 652609236097691106482853701 122364231768317082465535069)
        ·
          refine ⟨45886586913118905924575651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122364231768317082465535069 45886586913118905924575651)
          ·
            refine ⟨68829880369678358886863477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45886586913118905924575651 68829880369678358886863477)
            ·
              refine ⟨6452801284657346145643451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68829880369678358886863477 6452801284657346145643451)
              ·
                refine ⟨9679201926986019218465177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6452801284657346145643451 9679201926986019218465177)
                ·
                  refine ⟨7259401445239514413848883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9679201926986019218465177 7259401445239514413848883)
                  ·
                    refine ⟨10889102167859271620773325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7259401445239514413848883 10889102167859271620773325)
                    ·
                      refine ⟨4083413312947226857789997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10889102167859271620773325 4083413312947226857789997)
                      ·
                        rfl

theorem cell23_7952419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 5, 1, 2, 1, 3].length) (baseStart_7952419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7952419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7952419 prefixEnd_7952419 := by exact prefixLift 7952419
  have htrace : WordTrace (prefixWord ++ tailWord_7952419) baseStart_7952419 baseEnd_7952419 := by
    simpa [prefixWord, tailWord_7952419, baseEnd_7952419] using wordTrace_append hprefix tailTrace_7952419
  have hstable : (prefixWord ++ tailWord_7952419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7952419).length < 2 ^ (prefixWord ++ tailWord_7952419).sum := by decide
  have hdescent : baseEnd_7952419 < baseStart_7952419 := by decide
  rcases family_descends (prefixWord ++ tailWord_7952419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7952445 : List Nat := [1, 4, 1, 3, 1, 1, 3, 1, 2, 1, 5]
def baseStart_7952445 : Nat := 118140960795 + 7952445 * 2 ^ 59
def prefixEnd_7952445 : Nat := 4983230072969 + 3 ^ 40 * 7952445 * 2
def baseEnd_7952445 : Nat := 4083426663444243756064877

theorem tailTrace_7952445 : CollatzResearch.WordTrace tailWord_7952445 prefixEnd_7952445 4083426663444243756064877 := by
  unfold tailWord_7952445
  simp only [CollatzResearch.WordTrace]
  refine ⟨290049497674657409321714789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193366331783104939547809859 290049497674657409321714789)
  ·
    refine ⟨54384280813998264247821523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 290049497674657409321714789 54384280813998264247821523)
    ·
      refine ⟨81576421220997396371732285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54384280813998264247821523 81576421220997396371732285)
      ·
        refine ⟨30591157957874023639399607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81576421220997396371732285 30591157957874023639399607)
        ·
          refine ⟨45886736936811035459099411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30591157957874023639399607 45886736936811035459099411)
          ·
            refine ⟨68830105405216553188649117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45886736936811035459099411 68830105405216553188649117)
            ·
              refine ⟨25811289526956207445743419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68830105405216553188649117 25811289526956207445743419)
              ·
                refine ⟨38716934290434311168615129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25811289526956207445743419 38716934290434311168615129)
                ·
                  refine ⟨29037700717825733376461347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38716934290434311168615129 29037700717825733376461347)
                  ·
                    refine ⟨43556551076738600064692021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29037700717825733376461347 43556551076738600064692021)
                    ·
                      refine ⟨4083426663444243756064877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43556551076738600064692021 4083426663444243756064877)
                      ·
                        rfl

theorem cell23_7952445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_7952445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7952445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7952445 prefixEnd_7952445 := by exact prefixLift 7952445
  have htrace : WordTrace (prefixWord ++ tailWord_7952445) baseStart_7952445 baseEnd_7952445 := by
    simpa [prefixWord, tailWord_7952445, baseEnd_7952445] using wordTrace_append hprefix tailTrace_7952445
  have hstable : (prefixWord ++ tailWord_7952445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7952445).length < 2 ^ (prefixWord ++ tailWord_7952445).sum := by decide
  have hdescent : baseEnd_7952445 < baseStart_7952445 := by decide
  rcases family_descends (prefixWord ++ tailWord_7952445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7952458 : List Nat := [3, 1, 2, 1, 1, 2, 1, 1, 1, 1, 9]
def baseStart_7952458 : Nat := 118140960795 + 7952458 * 2 ^ 59
def prefixEnd_7952458 : Nat := 4983230072969 + 3 ^ 40 * 7952458 * 2
def baseEnd_7952458 : Nat := 4083433338692752205202317

theorem tailTrace_7952458 : CollatzResearch.WordTrace tailWord_7952458 prefixEnd_7952458 4083433338692752205202317 := by
  unfold tailWord_7952458
  simp only [CollatzResearch.WordTrace]
  refine ⟨72512492955902578135484507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193366647882406875027958685 72512492955902578135484507)
  ·
    refine ⟨108768739433853867203226761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72512492955902578135484507 108768739433853867203226761)
    ·
      refine ⟨81576554575390400402420071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108768739433853867203226761 81576554575390400402420071)
      ·
        refine ⟨122364831863085600603630107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81576554575390400402420071 122364831863085600603630107)
        ·
          refine ⟨183547247794628400905445161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122364831863085600603630107 183547247794628400905445161)
          ·
            refine ⟨137660435845971300679083871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183547247794628400905445161 137660435845971300679083871)
            ·
              refine ⟨206490653768956951018625807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137660435845971300679083871 206490653768956951018625807)
              ·
                refine ⟨309735980653435426527938711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206490653768956951018625807 309735980653435426527938711)
                ·
                  refine ⟨464603970980153139791908067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 309735980653435426527938711 464603970980153139791908067)
                  ·
                    refine ⟨696905956470229709687862101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 464603970980153139791908067 696905956470229709687862101)
                    ·
                      refine ⟨4083433338692752205202317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 696905956470229709687862101 4083433338692752205202317)
                      ·
                        rfl

theorem cell23_7952458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 1, 1, 9].length) (baseStart_7952458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7952458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7952458 prefixEnd_7952458 := by exact prefixLift 7952458
  have htrace : WordTrace (prefixWord ++ tailWord_7952458) baseStart_7952458 baseEnd_7952458 := by
    simpa [prefixWord, tailWord_7952458, baseEnd_7952458] using wordTrace_append hprefix tailTrace_7952458
  have hstable : (prefixWord ++ tailWord_7952458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7952458).length < 2 ^ (prefixWord ++ tailWord_7952458).sum := by decide
  have hdescent : baseEnd_7952458 < baseStart_7952458 := by decide
  rcases family_descends (prefixWord ++ tailWord_7952458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7952470 : List Nat := [5, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3]
def baseStart_7952470 : Nat := 118140960795 + 7952470 * 2 ^ 59
def prefixEnd_7952470 : Nat := 4983230072969 + 3 ^ 40 * 7952470 * 2
def baseEnd_7952470 : Nat := 4083439500460606158252263

theorem tailTrace_7952470 : CollatzResearch.WordTrace tailWord_7952470 prefixEnd_7952470 4083439500460606158252263 := by
  unfold tailWord_7952470
  simp only [CollatzResearch.WordTrace]
  refine ⟨18128150593722927411960929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 193366939666377892394249909 18128150593722927411960929)
  ·
    refine ⟨13596112945292195558970697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18128150593722927411960929 13596112945292195558970697)
    ·
      refine ⟨10197084708969146669228023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13596112945292195558970697 10197084708969146669228023)
      ·
        refine ⟨15295627063453720003842035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10197084708969146669228023 15295627063453720003842035)
        ·
          refine ⟨22943440595180580005763053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15295627063453720003842035 22943440595180580005763053)
          ·
            refine ⟨8603790223192717502161145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22943440595180580005763053 8603790223192717502161145)
            ·
              refine ⟨6452842667394538126620859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8603790223192717502161145 6452842667394538126620859)
              ·
                refine ⟨9679264001091807189931289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6452842667394538126620859 9679264001091807189931289)
                ·
                  refine ⟨7259448000818855392448467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9679264001091807189931289 7259448000818855392448467)
                  ·
                    refine ⟨10889172001228283088672701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7259448000818855392448467 10889172001228283088672701)
                    ·
                      refine ⟨4083439500460606158252263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10889172001228283088672701 4083439500460606158252263)
                      ·
                        rfl

theorem cell23_7952470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_7952470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7952470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7952470 prefixEnd_7952470 := by exact prefixLift 7952470
  have htrace : WordTrace (prefixWord ++ tailWord_7952470) baseStart_7952470 baseEnd_7952470 := by
    simpa [prefixWord, tailWord_7952470, baseEnd_7952470] using wordTrace_append hprefix tailTrace_7952470
  have hstable : (prefixWord ++ tailWord_7952470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7952470).length < 2 ^ (prefixWord ++ tailWord_7952470).sum := by decide
  have hdescent : baseEnd_7952470 < baseStart_7952470 := by decide
  rcases family_descends (prefixWord ++ tailWord_7952470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7952476 : List Nat := [2, 2, 4, 1, 1, 3, 1, 3, 2, 2, 2]
def baseStart_7952476 : Nat := 118140960795 + 7952476 * 2 ^ 59
def prefixEnd_7952476 : Nat := 4983230072969 + 3 ^ 40 * 7952476 * 2
def baseEnd_7952476 : Nat := 4083442581344533134777235

theorem tailTrace_7952476 : CollatzResearch.WordTrace tailWord_7952476 prefixEnd_7952476 4083442581344533134777235 := by
  unfold tailWord_7952476
  simp only [CollatzResearch.WordTrace]
  refine ⟨145025314168772550808046641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193367085558363401077395521 145025314168772550808046641)
  ·
    refine ⟨108768985626579413106034981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145025314168772550808046641 108768985626579413106034981)
    ·
      refine ⟨20394184804983639957381559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108768985626579413106034981 20394184804983639957381559)
      ·
        refine ⟨30591277207475459936072339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20394184804983639957381559 30591277207475459936072339)
        ·
          refine ⟨45886915811213189904108509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30591277207475459936072339 45886915811213189904108509)
          ·
            refine ⟨17207593429204946214040691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45886915811213189904108509 17207593429204946214040691)
            ·
              refine ⟨25811390143807419321061037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17207593429204946214040691 25811390143807419321061037)
              ·
                refine ⟨9679271303927782245397889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25811390143807419321061037 9679271303927782245397889)
                ·
                  refine ⟨7259453477945836684048417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9679271303927782245397889 7259453477945836684048417)
                  ·
                    refine ⟨5444590108459377513036313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7259453477945836684048417 5444590108459377513036313)
                    ·
                      refine ⟨4083442581344533134777235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5444590108459377513036313 4083442581344533134777235)
                      ·
                        rfl

theorem cell23_7952476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 3, 2, 2, 2].length) (baseStart_7952476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7952476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7952476 prefixEnd_7952476 := by exact prefixLift 7952476
  have htrace : WordTrace (prefixWord ++ tailWord_7952476) baseStart_7952476 baseEnd_7952476 := by
    simpa [prefixWord, tailWord_7952476, baseEnd_7952476] using wordTrace_append hprefix tailTrace_7952476
  have hstable : (prefixWord ++ tailWord_7952476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7952476).length < 2 ^ (prefixWord ++ tailWord_7952476).sum := by decide
  have hdescent : baseEnd_7952476 < baseStart_7952476 := by decide
  rcases family_descends (prefixWord ++ tailWord_7952476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7952495 : List Nat := [1, 1, 2, 1, 3, 4, 1, 3, 2, 5]
def baseStart_7952495 : Nat := 118140960795 + 7952495 * 2 ^ 59
def prefixEnd_7952495 : Nat := 4983230072969 + 3 ^ 40 * 7952495 * 2
def baseEnd_7952495 : Nat := 1361150779158989520146549

theorem tailTrace_7952495 : CollatzResearch.WordTrace tailWord_7952495 prefixEnd_7952495 1361150779158989520146549 := by
  unfold tailWord_7952495
  simp only [CollatzResearch.WordTrace]
  refine ⟨290051321324476267861034939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193367547549650845240689959 290051321324476267861034939)
  ·
    refine ⟨435076981986714401791552409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290051321324476267861034939 435076981986714401791552409)
    ·
      refine ⟨326307736490035801343664307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 435076981986714401791552409 326307736490035801343664307)
      ·
        refine ⟨489461604735053702015496461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326307736490035801343664307 489461604735053702015496461)
        ·
          refine ⟨183548101775645138255811173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 489461604735053702015496461 183548101775645138255811173)
          ·
            refine ⟨34415269082933463422964595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 183548101775645138255811173 34415269082933463422964595)
            ·
              refine ⟨51622903624400195134446893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34415269082933463422964595 51622903624400195134446893)
              ·
                refine ⟨19358588859150073175417585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51622903624400195134446893 19358588859150073175417585)
                ·
                  refine ⟨14518941644362554881563189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19358588859150073175417585 14518941644362554881563189)
                  ·
                    refine ⟨1361150779158989520146549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14518941644362554881563189 1361150779158989520146549)
                    ·
                      rfl

theorem cell23_7952495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 3, 2, 5].length) (baseStart_7952495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7952495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7952495 prefixEnd_7952495 := by exact prefixLift 7952495
  have htrace : WordTrace (prefixWord ++ tailWord_7952495) baseStart_7952495 baseEnd_7952495 := by
    simpa [prefixWord, tailWord_7952495, baseEnd_7952495] using wordTrace_append hprefix tailTrace_7952495
  have hstable : (prefixWord ++ tailWord_7952495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7952495).length < 2 ^ (prefixWord ++ tailWord_7952495).sum := by decide
  have hdescent : baseEnd_7952495 < baseStart_7952495 := by decide
  rcases family_descends (prefixWord ++ tailWord_7952495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7952505 : List Nat := [1, 2, 1, 3, 4, 1, 1, 2, 1, 2, 5]
def baseStart_7952505 : Nat := 118140960795 + 7952505 * 2 ^ 59
def prefixEnd_7952505 : Nat := 4983230072969 + 3 ^ 40 * 7952505 * 2
def baseEnd_7952505 : Nat := 4083457472283513521314601

theorem tailTrace_7952505 : CollatzResearch.WordTrace tailWord_7952505 prefixEnd_7952505 4083457472283513521314601 := by
  unfold tailWord_7952505
  simp only [CollatzResearch.WordTrace]
  refine ⟨290051686054440039568898969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193367790702960026379265979 290051686054440039568898969)
  ·
    refine ⟨217538764540830029676674227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290051686054440039568898969 217538764540830029676674227)
    ·
      refine ⟨326308146811245044515011341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217538764540830029676674227 326308146811245044515011341)
      ·
        refine ⟨122365555054216891693129253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 326308146811245044515011341 122365555054216891693129253)
        ·
          refine ⟨22943541572665667192461735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122365555054216891693129253 22943541572665667192461735)
          ·
            refine ⟨34415312358998500788692603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22943541572665667192461735 34415312358998500788692603)
            ·
              refine ⟨51622968538497751183038905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34415312358998500788692603 51622968538497751183038905)
              ·
                refine ⟨38717226403873313387279179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51622968538497751183038905 38717226403873313387279179)
                ·
                  refine ⟨58075839605809970080918769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38717226403873313387279179 58075839605809970080918769)
                  ·
                    refine ⟨43556879704357477560689077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58075839605809970080918769 43556879704357477560689077)
                    ·
                      refine ⟨4083457472283513521314601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43556879704357477560689077 4083457472283513521314601)
                      ·
                        rfl

theorem cell23_7952505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 2, 1, 2, 5].length) (baseStart_7952505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7952505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7952505 prefixEnd_7952505 := by exact prefixLift 7952505
  have htrace : WordTrace (prefixWord ++ tailWord_7952505) baseStart_7952505 baseEnd_7952505 := by
    simpa [prefixWord, tailWord_7952505, baseEnd_7952505] using wordTrace_append hprefix tailTrace_7952505
  have hstable : (prefixWord ++ tailWord_7952505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7952505).length < 2 ^ (prefixWord ++ tailWord_7952505).sum := by decide
  have hdescent : baseEnd_7952505 < baseStart_7952505 := by decide
  rcases family_descends (prefixWord ++ tailWord_7952505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7952572 : List Nat := [2, 2, 2, 3, 3, 1, 1, 1, 8]
def baseStart_7952572 : Nat := 118140960795 + 7952572 * 2 ^ 59
def prefixEnd_7952572 : Nat := 4983230072969 + 3 ^ 40 * 7952572 * 2
def baseEnd_7952572 : Nat := 453721319498596084352977

theorem tailTrace_7952572 : CollatzResearch.WordTrace tailWord_7952572 prefixEnd_7952572 453721319498596084352977 := by
  unfold tailWord_7952572
  simp only [CollatzResearch.WordTrace]
  refine ⟨145027064872598655005793985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193369419830131540007725313 145027064872598655005793985)
  ·
    refine ⟨108770298654448991254345489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145027064872598655005793985 108770298654448991254345489)
    ·
      refine ⟨81577723990836743440759117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108770298654448991254345489 81577723990836743440759117)
      ·
        refine ⟨30591646496563778790284669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81577723990836743440759117 30591646496563778790284669)
        ·
          refine ⟨11471867436211417046356751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30591646496563778790284669 11471867436211417046356751)
          ·
            refine ⟨17207801154317125569535127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11471867436211417046356751 17207801154317125569535127)
            ·
              refine ⟨25811701731475688354302691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17207801154317125569535127 25811701731475688354302691)
              ·
                refine ⟨38717552597213532531454037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25811701731475688354302691 38717552597213532531454037)
                ·
                  refine ⟨453721319498596084352977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38717552597213532531454037 453721319498596084352977)
                  ·
                    rfl

theorem cell23_7952572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 1, 8].length) (baseStart_7952572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7952572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7952572 prefixEnd_7952572 := by exact prefixLift 7952572
  have htrace : WordTrace (prefixWord ++ tailWord_7952572) baseStart_7952572 baseEnd_7952572 := by
    simpa [prefixWord, tailWord_7952572, baseEnd_7952572] using wordTrace_append hprefix tailTrace_7952572
  have hstable : (prefixWord ++ tailWord_7952572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7952572).length < 2 ^ (prefixWord ++ tailWord_7952572).sum := by decide
  have hdescent : baseEnd_7952572 < baseStart_7952572 := by decide
  rcases family_descends (prefixWord ++ tailWord_7952572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7952585 : List Nat := [1, 2, 1, 1, 2, 1, 1, 6, 3, 5]
def baseStart_7952585 : Nat := 118140960795 + 7952585 * 2 ^ 59
def prefixEnd_7952585 : Nat := 4983230072969 + 3 ^ 40 * 7952585 * 2
def baseEnd_7952585 : Nat := 1361166183578624402771411

theorem tailTrace_7952585 : CollatzResearch.WordTrace tailWord_7952585 prefixEnd_7952585 1361166183578624402771411 := by
  unfold tailWord_7952585
  simp only [CollatzResearch.WordTrace]
  refine ⟨290054603894150213231811209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193369735929433475487874139 290054603894150213231811209)
  ·
    refine ⟨217540952920612659923858407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290054603894150213231811209 217540952920612659923858407)
    ·
      refine ⟨326311429380918989885787611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217540952920612659923858407 326311429380918989885787611)
      ·
        refine ⟨489467144071378484828681417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326311429380918989885787611 489467144071378484828681417)
        ·
          refine ⟨367100358053533863621511063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 489467144071378484828681417 367100358053533863621511063)
          ·
            refine ⟨550650537080300795432266595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 367100358053533863621511063 550650537080300795432266595)
            ·
              refine ⟨825975805620451193148399893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 550650537080300795432266595 825975805620451193148399893)
              ·
                refine ⟨38717615888458649678831245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 825975805620451193148399893 38717615888458649678831245)
                ·
                  refine ⟨14519105958171993629561717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38717615888458649678831245 14519105958171993629561717)
                  ·
                    refine ⟨1361166183578624402771411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14519105958171993629561717 1361166183578624402771411)
                    ·
                      rfl

theorem cell23_7952585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6, 3, 5].length) (baseStart_7952585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7952585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7952585 prefixEnd_7952585 := by exact prefixLift 7952585
  have htrace : WordTrace (prefixWord ++ tailWord_7952585) baseStart_7952585 baseEnd_7952585 := by
    simpa [prefixWord, tailWord_7952585, baseEnd_7952585] using wordTrace_append hprefix tailTrace_7952585
  have hstable : (prefixWord ++ tailWord_7952585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7952585).length < 2 ^ (prefixWord ++ tailWord_7952585).sum := by decide
  have hdescent : baseEnd_7952585 < baseStart_7952585 := by decide
  rcases family_descends (prefixWord ++ tailWord_7952585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7952602 : List Nat := [3, 1, 1, 2, 2, 1, 3, 4, 1, 5]
def baseStart_7952602 : Nat := 118140960795 + 7952602 * 2 ^ 59
def prefixEnd_7952602 : Nat := 4983230072969 + 3 ^ 40 * 7952602 * 2
def baseEnd_7952602 : Nat := 1361169093302333213933885

theorem tailTrace_7952602 : CollatzResearch.WordTrace tailWord_7952602 prefixEnd_7952602 1361169093302333213933885 := by
  unfold tailWord_7952602
  simp only [CollatzResearch.WordTrace]
  refine ⟨72513805983772156283795015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193370149290059083423453373 72513805983772156283795015)
  ·
    refine ⟨108770708975658234425692523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72513805983772156283795015 108770708975658234425692523)
    ·
      refine ⟨163156063463487351638538785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108770708975658234425692523 163156063463487351638538785)
      ·
        refine ⟨122367047597615513728904089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163156063463487351638538785 122367047597615513728904089)
        ·
          refine ⟨91775285698211635296678067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122367047597615513728904089 91775285698211635296678067)
          ·
            refine ⟨137662928547317452945017101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91775285698211635296678067 137662928547317452945017101)
            ·
              refine ⟨51623598205244044854381413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137662928547317452945017101 51623598205244044854381413)
              ·
                refine ⟨9679424663483258410196515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51623598205244044854381413 9679424663483258410196515)
                ·
                  refine ⟨14519136995224887615294773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9679424663483258410196515 14519136995224887615294773)
                  ·
                    refine ⟨1361169093302333213933885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14519136995224887615294773 1361169093302333213933885)
                    ·
                      rfl

theorem cell23_7952602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 4, 1, 5].length) (baseStart_7952602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7952602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7952602 prefixEnd_7952602 := by exact prefixLift 7952602
  have htrace : WordTrace (prefixWord ++ tailWord_7952602) baseStart_7952602 baseEnd_7952602 := by
    simpa [prefixWord, tailWord_7952602, baseEnd_7952602] using wordTrace_append hprefix tailTrace_7952602
  have hstable : (prefixWord ++ tailWord_7952602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7952602).length < 2 ^ (prefixWord ++ tailWord_7952602).sum := by decide
  have hdescent : baseEnd_7952602 < baseStart_7952602 := by decide
  rcases family_descends (prefixWord ++ tailWord_7952602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7952609 : List Nat := [1, 2, 3, 1, 3, 1, 2, 3, 2, 3, 2]
def baseStart_7952609 : Nat := 118140960795 + 7952609 * 2 ^ 59
def prefixEnd_7952609 : Nat := 4983230072969 + 3 ^ 40 * 7952609 * 2
def baseEnd_7952609 : Nat := 4083510874271581114414123

theorem tailTrace_7952609 : CollatzResearch.WordTrace tailWord_7952609 prefixEnd_7952609 4083510874271581114414123 := by
  unfold tailWord_7952609
  simp only [CollatzResearch.WordTrace]
  refine ⟨290055479246063265330684881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193370319497375510220456587 290055479246063265330684881)
  ·
    refine ⟨217541609434547448998013661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290055479246063265330684881 217541609434547448998013661)
    ·
      refine ⟨81578103537955293374255123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 217541609434547448998013661 81578103537955293374255123)
      ·
        refine ⟨122367155306932940061382685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81578103537955293374255123 122367155306932940061382685)
        ·
          refine ⟨45887683240099852523018507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122367155306932940061382685 45887683240099852523018507)
          ·
            refine ⟨68831524860149778784527761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45887683240099852523018507 68831524860149778784527761)
            ·
              refine ⟨51623643645112334088395821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68831524860149778784527761 51623643645112334088395821)
              ·
                refine ⟨19358866366917125283148433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51623643645112334088395821 19358866366917125283148433)
                ·
                  refine ⟨14519149775187843962361325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19358866366917125283148433 14519149775187843962361325)
                  ·
                    refine ⟨5444681165695441485885497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14519149775187843962361325 5444681165695441485885497)
                    ·
                      refine ⟨4083510874271581114414123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5444681165695441485885497 4083510874271581114414123)
                      ·
                        rfl

theorem cell23_7952609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 3, 2, 3, 2].length) (baseStart_7952609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7952609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7952609 prefixEnd_7952609 := by exact prefixLift 7952609
  have htrace : WordTrace (prefixWord ++ tailWord_7952609) baseStart_7952609 baseEnd_7952609 := by
    simpa [prefixWord, tailWord_7952609, baseEnd_7952609] using wordTrace_append hprefix tailTrace_7952609
  have hstable : (prefixWord ++ tailWord_7952609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7952609).length < 2 ^ (prefixWord ++ tailWord_7952609).sum := by decide
  have hdescent : baseEnd_7952609 < baseStart_7952609 := by decide
  rcases family_descends (prefixWord ++ tailWord_7952609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7952622 : List Nat := [4, 1, 2, 1, 1, 1, 1, 2, 5, 1, 4]
def baseStart_7952622 : Nat := 118140960795 + 7952622 * 2 ^ 59
def prefixEnd_7952622 : Nat := 4983230072969 + 3 ^ 40 * 7952622 * 2
def baseEnd_7952622 : Nat := 4083517549520089563551563

theorem tailTrace_7952622 : CollatzResearch.WordTrace tailWord_7952622 prefixEnd_7952622 4083517549520089563551563 := by
  unfold tailWord_7952622
  simp only [CollatzResearch.WordTrace]
  refine ⟨36256994174377021068863515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193370635596677445700605413 36256994174377021068863515)
  ·
    refine ⟨54385491261565531603295273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36256994174377021068863515 54385491261565531603295273)
    ·
      refine ⟨40789118446174148702471455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54385491261565531603295273 40789118446174148702471455)
      ·
        refine ⟨61183677669261223053707183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40789118446174148702471455 61183677669261223053707183)
        ·
          refine ⟨91775516503891834580560775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61183677669261223053707183 91775516503891834580560775)
          ·
            refine ⟨137663274755837751870841163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91775516503891834580560775 137663274755837751870841163)
            ·
              refine ⟨206494912133756627806261745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137663274755837751870841163 206494912133756627806261745)
              ·
                refine ⟨154871184100317470854696309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 206494912133756627806261745 154871184100317470854696309)
                ·
                  refine ⟨14519173509404762892627779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 154871184100317470854696309 14519173509404762892627779)
                  ·
                    refine ⟨21778760264107144338941669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14519173509404762892627779 21778760264107144338941669)
                    ·
                      refine ⟨4083517549520089563551563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21778760264107144338941669 4083517549520089563551563)
                      ·
                        rfl

theorem cell23_7952622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_7952622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7952622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7952622 prefixEnd_7952622 := by exact prefixLift 7952622
  have htrace : WordTrace (prefixWord ++ tailWord_7952622) baseStart_7952622 baseEnd_7952622 := by
    simpa [prefixWord, tailWord_7952622, baseEnd_7952622] using wordTrace_append hprefix tailTrace_7952622
  have hstable : (prefixWord ++ tailWord_7952622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7952622).length < 2 ^ (prefixWord ++ tailWord_7952622).sum := by decide
  have hdescent : baseEnd_7952622 < baseStart_7952622 := by decide
  rcases family_descends (prefixWord ++ tailWord_7952622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7952626 : List Nat := [3, 2, 1, 3, 2, 2, 1, 2, 2, 3, 2]
def baseStart_7952626 : Nat := 118140960795 + 7952626 * 2 ^ 59
def prefixEnd_7952626 : Nat := 4983230072969 + 3 ^ 40 * 7952626 * 2
def baseEnd_7952626 : Nat := 4083519603442707547901545

theorem tailTrace_7952626 : CollatzResearch.WordTrace tailWord_7952626 prefixEnd_7952626 4083519603442707547901545 := by
  unfold tailWord_7952626
  simp only [CollatzResearch.WordTrace]
  refine ⟨72514024821750419308513433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193370732858001118156035821 72514024821750419308513433)
  ·
    refine ⟨54385518616312814481385075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72514024821750419308513433 54385518616312814481385075)
    ·
      refine ⟨81578277924469221722077613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54385518616312814481385075 81578277924469221722077613)
      ·
        refine ⟨30591854221675958145779105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81578277924469221722077613 30591854221675958145779105)
        ·
          refine ⟨22943890666256968609334329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30591854221675958145779105 22943890666256968609334329)
          ·
            refine ⟨17207917999692726457000747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22943890666256968609334329 17207917999692726457000747)
            ·
              refine ⟨25811876999539089685501121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17207917999692726457000747 25811876999539089685501121)
              ·
                refine ⟨19358907749654317264125841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25811876999539089685501121 19358907749654317264125841)
                ·
                  refine ⟨14519180812240737948094381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19358907749654317264125841 14519180812240737948094381)
                  ·
                    refine ⟨5444692804590276730535393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14519180812240737948094381 5444692804590276730535393)
                    ·
                      refine ⟨4083519603442707547901545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5444692804590276730535393 4083519603442707547901545)
                      ·
                        rfl

theorem cell23_7952626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 2, 2, 3, 2].length) (baseStart_7952626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7952626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7952626 prefixEnd_7952626 := by exact prefixLift 7952626
  have htrace : WordTrace (prefixWord ++ tailWord_7952626) baseStart_7952626 baseEnd_7952626 := by
    simpa [prefixWord, tailWord_7952626, baseEnd_7952626] using wordTrace_append hprefix tailTrace_7952626
  have hstable : (prefixWord ++ tailWord_7952626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7952626).length < 2 ^ (prefixWord ++ tailWord_7952626).sum := by decide
  have hdescent : baseEnd_7952626 < baseStart_7952626 := by decide
  rcases family_descends (prefixWord ++ tailWord_7952626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7952649 : List Nat := [1, 2, 1, 1, 3, 5, 1, 3, 2, 4]
def baseStart_7952649 : Nat := 118140960795 + 7952649 * 2 ^ 59
def prefixEnd_7952649 : Nat := 4983230072969 + 3 ^ 40 * 7952649 * 2
def baseEnd_7952649 : Nat := 1361177137832586985971313

theorem tailTrace_7952649 : CollatzResearch.WordTrace tailWord_7952649 prefixEnd_7952649 1361177137832586985971313 := by
  unfold tailWord_7952649
  simp only [CollatzResearch.WordTrace]
  refine ⟨290056938165918352162141001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193371292110612234774760667 290056938165918352162141001)
  ·
    refine ⟨217542703624438764121605751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290056938165918352162141001 217542703624438764121605751)
    ·
      refine ⟨326314055436658146182408627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217542703624438764121605751 326314055436658146182408627)
      ·
        refine ⟨489471083154987219273612941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326314055436658146182408627 489471083154987219273612941)
        ·
          refine ⟨183551656183120207227604853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 489471083154987219273612941 183551656183120207227604853)
          ·
            refine ⟨17207967767167519427587955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 183551656183120207227604853 17207967767167519427587955)
            ·
              refine ⟨25811951650751279141381933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17207967767167519427587955 25811951650751279141381933)
              ·
                refine ⟨9679481869031729678018225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25811951650751279141381933 9679481869031729678018225)
                ·
                  refine ⟨7259611401773797258513669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9679481869031729678018225 7259611401773797258513669)
                  ·
                    refine ⟨1361177137832586985971313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7259611401773797258513669 1361177137832586985971313)
                    ·
                      rfl

theorem cell23_7952649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 3, 2, 4].length) (baseStart_7952649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7952649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7952649 prefixEnd_7952649 := by exact prefixLift 7952649
  have htrace : WordTrace (prefixWord ++ tailWord_7952649) baseStart_7952649 baseEnd_7952649 := by
    simpa [prefixWord, tailWord_7952649, baseEnd_7952649] using wordTrace_append hprefix tailTrace_7952649
  have hstable : (prefixWord ++ tailWord_7952649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7952649).length < 2 ^ (prefixWord ++ tailWord_7952649).sum := by decide
  have hdescent : baseEnd_7952649 < baseStart_7952649 := by decide
  rcases family_descends (prefixWord ++ tailWord_7952649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7952652 : List Nat := [2, 2, 1, 2, 2, 2, 2, 3, 1, 2, 4]
def baseStart_7952652 : Nat := 118140960795 + 7952652 * 2 ^ 59
def prefixEnd_7952652 : Nat := 4983230072969 + 3 ^ 40 * 7952652 * 2
def baseEnd_7952652 : Nat := 4083532953939724446176425

theorem tailTrace_7952652 : CollatzResearch.WordTrace tailWord_7952652 prefixEnd_7952652 4083532953939724446176425 := by
  unfold tailWord_7952652
  simp only [CollatzResearch.WordTrace]
  refine ⟨145028523792453741837250105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193371365056604989116333473 145028523792453741837250105)
  ·
    refine ⟨108771392844340306377937579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145028523792453741837250105 108771392844340306377937579)
    ·
      refine ⟨163157089266510459566906369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108771392844340306377937579 163157089266510459566906369)
      ·
        refine ⟨122367816949882844675179777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163157089266510459566906369 122367816949882844675179777)
        ·
          refine ⟨91775862712412133506384833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122367816949882844675179777 91775862712412133506384833)
          ·
            refine ⟨68831897034309100129788625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91775862712412133506384833 68831897034309100129788625)
            ·
              refine ⟨51623922775731825097341469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68831897034309100129788625 51623922775731825097341469)
              ·
                refine ⟨19358971040899434411503051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51623922775731825097341469 19358971040899434411503051)
                ·
                  refine ⟨29038456561349151617254577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19358971040899434411503051 29038456561349151617254577)
                  ·
                    refine ⟨21778842421011863712940933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29038456561349151617254577 21778842421011863712940933)
                    ·
                      refine ⟨4083532953939724446176425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21778842421011863712940933 4083532953939724446176425)
                      ·
                        rfl

theorem cell23_7952652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 3, 1, 2, 4].length) (baseStart_7952652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7952652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7952652 prefixEnd_7952652 := by exact prefixLift 7952652
  have htrace : WordTrace (prefixWord ++ tailWord_7952652) baseStart_7952652 baseEnd_7952652 := by
    simpa [prefixWord, tailWord_7952652, baseEnd_7952652] using wordTrace_append hprefix tailTrace_7952652
  have hstable : (prefixWord ++ tailWord_7952652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7952652).length < 2 ^ (prefixWord ++ tailWord_7952652).sum := by decide
  have hdescent : baseEnd_7952652 < baseStart_7952652 := by decide
  rcases family_descends (prefixWord ++ tailWord_7952652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7952679 : List Nat := [1, 1, 8, 1, 12]
def baseStart_7952679 : Nat := 118140960795 + 7952679 * 2 ^ 59
def prefixEnd_7952679 : Nat := 4983230072969 + 3 ^ 40 * 7952679 * 2
def baseEnd_7952679 : Nat := 5601573138432641756569

theorem tailTrace_7952679 : CollatzResearch.WordTrace tailWord_7952679 prefixEnd_7952679 5601573138432641756569 := by
  unfold tailWord_7952679
  simp only [CollatzResearch.WordTrace]
  refine ⟨290058032355809667285733091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193372021570539778190488727 290058032355809667285733091)
  ·
    refine ⟨435087048533714500928599637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290058032355809667285733091 435087048533714500928599637)
    ·
      refine ⟨5098676350004466807757027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 435087048533714500928599637 5098676350004466807757027)
      ·
        refine ⟨7648014525006700211635541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5098676350004466807757027 7648014525006700211635541)
        ·
          refine ⟨5601573138432641756569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 7648014525006700211635541 5601573138432641756569)
          ·
            rfl

theorem cell23_7952679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 12].length) (baseStart_7952679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7952679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7952679 prefixEnd_7952679 := by exact prefixLift 7952679
  have htrace : WordTrace (prefixWord ++ tailWord_7952679) baseStart_7952679 baseEnd_7952679 := by
    simpa [prefixWord, tailWord_7952679, baseEnd_7952679] using wordTrace_append hprefix tailTrace_7952679
  have hstable : (prefixWord ++ tailWord_7952679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7952679).length < 2 ^ (prefixWord ++ tailWord_7952679).sum := by decide
  have hdescent : baseEnd_7952679 < baseStart_7952679 := by decide
  rcases family_descends (prefixWord ++ tailWord_7952679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7952690 : List Nat := [3, 2, 1, 1, 5, 1, 1, 4, 1, 2, 2]
def baseStart_7952690 : Nat := 118140960795 + 7952690 * 2 ^ 59
def prefixEnd_7952690 : Nat := 4983230072969 + 3 ^ 40 * 7952690 * 2
def baseEnd_7952690 : Nat := 4083552466204595297501251

theorem tailTrace_7952690 : CollatzResearch.WordTrace tailWord_7952690 prefixEnd_7952690 4083552466204595297501251 := by
  unfold tailWord_7952690
  simp only [CollatzResearch.WordTrace]
  refine ⟨72514608389692454041095881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193372289039179877442922349 72514608389692454041095881)
  ·
    refine ⟨54385956292269340530821911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72514608389692454041095881 54385956292269340530821911)
    ·
      refine ⟨81578934438404010796232867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54385956292269340530821911 81578934438404010796232867)
      ·
        refine ⟨122368401657606016194349301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81578934438404010796232867 122368401657606016194349301)
        ·
          refine ⟨11472037655400564018220247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 122368401657606016194349301 11472037655400564018220247)
          ·
            refine ⟨17208056483100846027330371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11472037655400564018220247 17208056483100846027330371)
            ·
              refine ⟨25812084724651269040995557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17208056483100846027330371 25812084724651269040995557)
              ·
                refine ⟨4839765885872112945186667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25812084724651269040995557 4839765885872112945186667)
                ·
                  refine ⟨7259648828808169417780001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4839765885872112945186667 7259648828808169417780001)
                  ·
                    refine ⟨5444736621606127063335001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7259648828808169417780001 5444736621606127063335001)
                    ·
                      refine ⟨4083552466204595297501251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5444736621606127063335001 4083552466204595297501251)
                      ·
                        rfl

theorem cell23_7952690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 4, 1, 2, 2].length) (baseStart_7952690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7952690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7952690 prefixEnd_7952690 := by exact prefixLift 7952690
  have htrace : WordTrace (prefixWord ++ tailWord_7952690) baseStart_7952690 baseEnd_7952690 := by
    simpa [prefixWord, tailWord_7952690, baseEnd_7952690] using wordTrace_append hprefix tailTrace_7952690
  have hstable : (prefixWord ++ tailWord_7952690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7952690).length < 2 ^ (prefixWord ++ tailWord_7952690).sum := by decide
  have hdescent : baseEnd_7952690 < baseStart_7952690 := by decide
  rcases family_descends (prefixWord ++ tailWord_7952690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7952716 : List Nat := [2, 2, 1, 3, 2, 1, 2, 4, 1, 3, 2]
def baseStart_7952716 : Nat := 118140960795 + 7952716 * 2 ^ 59
def prefixEnd_7952716 : Nat := 4983230072969 + 3 ^ 40 * 7952716 * 2
def baseEnd_7952716 : Nat := 4083565816701612195776131

theorem tailTrace_7952716 : CollatzResearch.WordTrace tailWord_7952716 prefixEnd_7952716 4083565816701612195776131 := by
  unfold tailWord_7952716
  simp only [CollatzResearch.WordTrace]
  refine ⟨145029690928337811302415001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193372921237783748403220001 145029690928337811302415001)
  ·
    refine ⟨108772268196253358476811251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145029690928337811302415001 108772268196253358476811251)
    ·
      refine ⟨163158402294380037715216877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108772268196253358476811251 163158402294380037715216877)
      ·
        refine ⟨61184400860392514143206329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163158402294380037715216877 61184400860392514143206329)
        ·
          refine ⟨45888300645294385607404747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61184400860392514143206329 45888300645294385607404747)
          ·
            refine ⟨68832450967941578411107121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45888300645294385607404747 68832450967941578411107121)
            ·
              refine ⟨51624338225956183808330341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68832450967941578411107121 51624338225956183808330341)
              ·
                refine ⟨9679563417366784464061939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51624338225956183808330341 9679563417366784464061939)
                ·
                  refine ⟨14519345126050176696092909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9679563417366784464061939 14519345126050176696092909)
                  ·
                    refine ⟨5444754422268816261034841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14519345126050176696092909 5444754422268816261034841)
                    ·
                      refine ⟨4083565816701612195776131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5444754422268816261034841 4083565816701612195776131)
                      ·
                        rfl

theorem cell23_7952716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 4, 1, 3, 2].length) (baseStart_7952716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7952716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7952716 prefixEnd_7952716 := by exact prefixLift 7952716
  have htrace : WordTrace (prefixWord ++ tailWord_7952716) baseStart_7952716 baseEnd_7952716 := by
    simpa [prefixWord, tailWord_7952716, baseEnd_7952716] using wordTrace_append hprefix tailTrace_7952716
  have hstable : (prefixWord ++ tailWord_7952716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7952716).length < 2 ^ (prefixWord ++ tailWord_7952716).sum := by decide
  have hdescent : baseEnd_7952716 < baseStart_7952716 := by decide
  rcases family_descends (prefixWord ++ tailWord_7952716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7952734 : List Nat := [4, 4, 2, 1, 1, 2, 1, 2, 2, 4]
def baseStart_7952734 : Nat := 118140960795 + 7952734 * 2 ^ 59
def prefixEnd_7952734 : Nat := 4983230072969 + 3 ^ 40 * 7952734 * 2
def baseEnd_7952734 : Nat := 1361191686451131041783683

theorem tailTrace_7952734 : CollatzResearch.WordTrace tailWord_7952734 prefixEnd_7952734 1361191686451131041783683 := by
  unfold tailWord_7952734
  simp only [CollatzResearch.WordTrace]
  refine ⟨36257504796326301459873157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 193373358913740274452656837 36257504796326301459873157)
  ·
    refine ⟨6798282149311181523726217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36257504796326301459873157 6798282149311181523726217)
    ·
      refine ⟨5098711611983386142794663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6798282149311181523726217 5098711611983386142794663)
      ·
        refine ⟨7648067417975079214191995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5098711611983386142794663 7648067417975079214191995)
        ·
          refine ⟨11472101126962618821287993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7648067417975079214191995 11472101126962618821287993)
          ·
            refine ⟨8604075845221964115965995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11472101126962618821287993 8604075845221964115965995)
            ·
              refine ⟨12906113767832946173948993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8604075845221964115965995 12906113767832946173948993)
              ·
                refine ⟨9679585325874709630461745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12906113767832946173948993 9679585325874709630461745)
                ·
                  refine ⟨7259688994406032222846309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9679585325874709630461745 7259688994406032222846309)
                  ·
                    refine ⟨1361191686451131041783683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7259688994406032222846309 1361191686451131041783683)
                    ·
                      rfl

theorem cell23_7952734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_7952734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7952734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7952734 prefixEnd_7952734 := by exact prefixLift 7952734
  have htrace : WordTrace (prefixWord ++ tailWord_7952734) baseStart_7952734 baseEnd_7952734 := by
    simpa [prefixWord, tailWord_7952734, baseEnd_7952734] using wordTrace_append hprefix tailTrace_7952734
  have hstable : (prefixWord ++ tailWord_7952734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7952734).length < 2 ^ (prefixWord ++ tailWord_7952734).sum := by decide
  have hdescent : baseEnd_7952734 < baseStart_7952734 := by decide
  rcases family_descends (prefixWord ++ tailWord_7952734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7952752 : List Nat := [2, 1, 1, 1, 4, 3, 1, 3, 7]
def baseStart_7952752 : Nat := 118140960795 + 7952752 * 2 ^ 59
def prefixEnd_7952752 : Nat := 4983230072969 + 3 ^ 40 * 7952752 * 2
def baseEnd_7952752 : Nat := 453731589111686006102885

theorem tailTrace_7952752 : CollatzResearch.WordTrace tailWord_7952752 prefixEnd_7952752 453731589111686006102885 := by
  unfold tailWord_7952752
  simp only [CollatzResearch.WordTrace]
  refine ⟨145030347442272600376570255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193373796589696800502093673 145030347442272600376570255)
  ·
    refine ⟨217545521163408900564855383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145030347442272600376570255 217545521163408900564855383)
    ·
      refine ⟨326318281745113350847283075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217545521163408900564855383 326318281745113350847283075)
      ·
        refine ⟨489477422617670026270924613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326318281745113350847283075 489477422617670026270924613)
        ·
          refine ⟨91777016740813129925798365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 489477422617670026270924613 91777016740813129925798365)
          ·
            refine ⟨34416381277804923722174387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91777016740813129925798365 34416381277804923722174387)
            ·
              refine ⟨51624571916707385583261581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34416381277804923722174387 51624571916707385583261581)
              ·
                refine ⟨19359214468765269593723093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51624571916707385583261581 19359214468765269593723093)
                ·
                  refine ⟨453731589111686006102885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19359214468765269593723093 453731589111686006102885)
                  ·
                    rfl

theorem cell23_7952752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 3, 7].length) (baseStart_7952752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7952752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7952752 prefixEnd_7952752 := by exact prefixLift 7952752
  have htrace : WordTrace (prefixWord ++ tailWord_7952752) baseStart_7952752 baseEnd_7952752 := by
    simpa [prefixWord, tailWord_7952752, baseEnd_7952752] using wordTrace_append hprefix tailTrace_7952752
  have hstable : (prefixWord ++ tailWord_7952752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7952752).length < 2 ^ (prefixWord ++ tailWord_7952752).sum := by decide
  have hdescent : baseEnd_7952752 < baseStart_7952752 := by decide
  rcases family_descends (prefixWord ++ tailWord_7952752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7952769 : List Nat := [1, 2, 4, 3, 1, 1, 2, 2, 7]
def baseStart_7952769 : Nat := 118140960795 + 7952769 * 2 ^ 59
def prefixEnd_7952769 : Nat := 4983230072969 + 3 ^ 40 * 7952769 * 2
def baseEnd_7952769 : Nat := 453732559019588943157043

theorem tailTrace_7952769 : CollatzResearch.WordTrace tailWord_7952769 prefixEnd_7952769 453732559019588943157043 := by
  unfold tailWord_7952769
  simp only [CollatzResearch.WordTrace]
  refine ⟨290061314925483612656509361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193374209950322408437672907 290061314925483612656509361)
  ·
    refine ⟨217545986194112709492382021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290061314925483612656509361 217545986194112709492382021)
    ·
      refine ⟨40789872411396133029821629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 217545986194112709492382021 40789872411396133029821629)
      ·
        refine ⟨15296202154273549886183111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40789872411396133029821629 15296202154273549886183111)
        ·
          refine ⟨22944303231410324829274667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15296202154273549886183111 22944303231410324829274667)
          ·
            refine ⟨34416454847115487243912001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22944303231410324829274667 34416454847115487243912001)
            ·
              refine ⟨25812341135336615432934001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34416454847115487243912001 25812341135336615432934001)
              ·
                refine ⟨19359255851502461574700501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25812341135336615432934001 19359255851502461574700501)
                ·
                  refine ⟨453732559019588943157043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19359255851502461574700501 453732559019588943157043)
                  ·
                    rfl

theorem cell23_7952769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 2, 7].length) (baseStart_7952769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7952769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7952769 prefixEnd_7952769 := by exact prefixLift 7952769
  have htrace : WordTrace (prefixWord ++ tailWord_7952769) baseStart_7952769 baseEnd_7952769 := by
    simpa [prefixWord, tailWord_7952769, baseEnd_7952769] using wordTrace_append hprefix tailTrace_7952769
  have hstable : (prefixWord ++ tailWord_7952769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7952769).length < 2 ^ (prefixWord ++ tailWord_7952769).sum := by decide
  have hdescent : baseEnd_7952769 < baseStart_7952769 := by decide
  rcases family_descends (prefixWord ++ tailWord_7952769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7952789 : List Nat := [1, 3, 2, 1, 1, 2, 1, 2, 1, 7, 2]
def baseStart_7952789 : Nat := 118140960795 + 7952789 * 2 ^ 59
def prefixEnd_7952789 : Nat := 4983230072969 + 3 ^ 40 * 7952789 * 2
def baseEnd_7952789 : Nat := 4083603300789390410163295

theorem tailTrace_7952789 : CollatzResearch.WordTrace tailWord_7952789 prefixEnd_7952789 4083603300789390410163295 := by
  unfold tailWord_7952789
  simp only [CollatzResearch.WordTrace]
  refine ⟨290062044385411156072237421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193374696256940770714824947 290062044385411156072237421)
  ·
    refine ⟨108773266644529183527089033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290062044385411156072237421 108773266644529183527089033)
    ·
      refine ⟨81579949983396887645316775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108773266644529183527089033 81579949983396887645316775)
      ·
        refine ⟨122369924975095331467975163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81579949983396887645316775 122369924975095331467975163)
        ·
          refine ⟨183554887462642997201962745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122369924975095331467975163 183554887462642997201962745)
          ·
            refine ⟨137666165596982247901472059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183554887462642997201962745 137666165596982247901472059)
            ·
              refine ⟨206499248395473371852208089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137666165596982247901472059 206499248395473371852208089)
              ·
                refine ⟨154874436296605028889156067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 206499248395473371852208089 154874436296605028889156067)
                ·
                  refine ⟨232311654444907543333734101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 154874436296605028889156067 232311654444907543333734101)
                  ·
                    refine ⟨5444804401052520546884393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 232311654444907543333734101 5444804401052520546884393)
                    ·
                      refine ⟨4083603300789390410163295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5444804401052520546884393 4083603300789390410163295)
                      ·
                        rfl

theorem cell23_7952789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 7, 2].length) (baseStart_7952789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7952789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7952789 prefixEnd_7952789 := by exact prefixLift 7952789
  have htrace : WordTrace (prefixWord ++ tailWord_7952789) baseStart_7952789 baseEnd_7952789 := by
    simpa [prefixWord, tailWord_7952789, baseEnd_7952789] using wordTrace_append hprefix tailTrace_7952789
  have hstable : (prefixWord ++ tailWord_7952789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7952789).length < 2 ^ (prefixWord ++ tailWord_7952789).sum := by decide
  have hdescent : baseEnd_7952789 < baseStart_7952789 := by decide
  rcases family_descends (prefixWord ++ tailWord_7952789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7952799 : List Nat := [1, 1, 2, 5, 1, 1, 3, 2, 2, 5]
def baseStart_7952799 : Nat := 118140960795 + 7952799 * 2 ^ 59
def prefixEnd_7952799 : Nat := 4983230072969 + 3 ^ 40 * 7952799 * 2
def baseEnd_7952799 : Nat := 1361202811865311790346083

theorem tailTrace_7952799 : CollatzResearch.WordTrace tailWord_7952799 prefixEnd_7952799 1361202811865311790346083 := by
  unfold tailWord_7952799
  simp only [CollatzResearch.WordTrace]
  refine ⟨290062409115374927780101451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193374939410249951853400967 290062409115374927780101451)
  ·
    refine ⟨435093613673062391670152177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290062409115374927780101451 435093613673062391670152177)
    ·
      refine ⟨326320210254796793752614133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 435093613673062391670152177 326320210254796793752614133)
      ·
        refine ⟨30592519711387199414307575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 326320210254796793752614133 30592519711387199414307575)
        ·
          refine ⟨45888779567080799121461363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30592519711387199414307575 45888779567080799121461363)
          ·
            refine ⟨68833169350621198682192045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45888779567080799121461363 68833169350621198682192045)
            ·
              refine ⟨25812438506482949505822017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68833169350621198682192045 25812438506482949505822017)
              ·
                refine ⟨19359328879862212129366513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25812438506482949505822017 19359328879862212129366513)
                ·
                  refine ⟨14519496659896659097024885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19359328879862212129366513 14519496659896659097024885)
                  ·
                    refine ⟨1361202811865311790346083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14519496659896659097024885 1361202811865311790346083)
                    ·
                      rfl

theorem cell23_7952799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 2, 2, 5].length) (baseStart_7952799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7952799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7952799 prefixEnd_7952799 := by exact prefixLift 7952799
  have htrace : WordTrace (prefixWord ++ tailWord_7952799) baseStart_7952799 baseEnd_7952799 := by
    simpa [prefixWord, tailWord_7952799, baseEnd_7952799] using wordTrace_append hprefix tailTrace_7952799
  have hstable : (prefixWord ++ tailWord_7952799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7952799).length < 2 ^ (prefixWord ++ tailWord_7952799).sum := by decide
  have hdescent : baseEnd_7952799 < baseStart_7952799 := by decide
  rcases family_descends (prefixWord ++ tailWord_7952799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7952832 : List Nat := [2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 6]
def baseStart_7952832 : Nat := 118140960795 + 7952832 * 2 ^ 59
def prefixEnd_7952832 : Nat := 4983230072969 + 3 ^ 40 * 7952832 * 2
def baseEnd_7952832 : Nat := 4083625380457533741925597

theorem tailTrace_7952832 : CollatzResearch.WordTrace tailWord_7952832 prefixEnd_7952832 4083625380457533741925597 := by
  unfold tailWord_7952832
  simp only [CollatzResearch.WordTrace]
  refine ⟨145031806362127687208026375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193375741816170249610701833 145031806362127687208026375)
  ·
    refine ⟨217547709543191530812039563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145031806362127687208026375 217547709543191530812039563)
    ·
      refine ⟨326321564314787296218059345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217547709543191530812039563 326321564314787296218059345)
      ·
        refine ⟨244741173236090472163544509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326321564314787296218059345 244741173236090472163544509)
        ·
          refine ⟨91777939963533927061329191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 244741173236090472163544509 91777939963533927061329191)
          ·
            refine ⟨137666909945300890591993787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91777939963533927061329191 137666909945300890591993787)
            ·
              refine ⟨206500364917951335887990681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137666909945300890591993787 206500364917951335887990681)
              ·
                refine ⟨154875273688463501915993011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 206500364917951335887990681 154875273688463501915993011)
                ·
                  refine ⟨232312910532695252873989517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 154875273688463501915993011 232312910532695252873989517)
                  ·
                    refine ⟨87117341449760719827746069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 232312910532695252873989517 87117341449760719827746069)
                    ·
                      refine ⟨4083625380457533741925597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 87117341449760719827746069 4083625380457533741925597)
                      ·
                        rfl

theorem cell23_7952832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 6].length) (baseStart_7952832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7952832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7952832 prefixEnd_7952832 := by exact prefixLift 7952832
  have htrace : WordTrace (prefixWord ++ tailWord_7952832) baseStart_7952832 baseEnd_7952832 := by
    simpa [prefixWord, tailWord_7952832, baseEnd_7952832] using wordTrace_append hprefix tailTrace_7952832
  have hstable : (prefixWord ++ tailWord_7952832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7952832).length < 2 ^ (prefixWord ++ tailWord_7952832).sum := by decide
  have hdescent : baseEnd_7952832 < baseStart_7952832 := by decide
  rcases family_descends (prefixWord ++ tailWord_7952832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7952863 : List Nat := [1, 1, 2, 3, 3, 3, 1, 4, 1, 4]
def baseStart_7952863 : Nat := 118140960795 + 7952863 * 2 ^ 59
def prefixEnd_7952863 : Nat := 4983230072969 + 3 ^ 40 * 7952863 * 2
def baseEnd_7952863 : Nat := 1361213766119274373545985

theorem tailTrace_7952863 : CollatzResearch.WordTrace tailWord_7952863 prefixEnd_7952863 1361213766119274373545985 := by
  unfold tailWord_7952863
  simp only [CollatzResearch.WordTrace]
  refine ⟨290064743387143066710431243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193376495591428711140287495 290064743387143066710431243)
  ·
    refine ⟨435097115080714600065646865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290064743387143066710431243 435097115080714600065646865)
    ·
      refine ⟨326322836310535950049235149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 435097115080714600065646865 326322836310535950049235149)
      ·
        refine ⟨122371063616450981268463181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 326322836310535950049235149 122371063616450981268463181)
        ·
          refine ⟨45889148856169117975673693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122371063616450981268463181 45889148856169117975673693)
          ·
            refine ⟨17208430821063419240877635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45889148856169117975673693 17208430821063419240877635)
            ·
              refine ⟨25812646231595128861316453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17208430821063419240877635 25812646231595128861316453)
              ·
                refine ⟨4839871168424086661496835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25812646231595128861316453 4839871168424086661496835)
                ·
                  refine ⟨7259806752636129992245253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4839871168424086661496835 7259806752636129992245253)
                  ·
                    refine ⟨1361213766119274373545985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7259806752636129992245253 1361213766119274373545985)
                    ·
                      rfl

theorem cell23_7952863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 4, 1, 4].length) (baseStart_7952863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7952863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7952863 prefixEnd_7952863 := by exact prefixLift 7952863
  have htrace : WordTrace (prefixWord ++ tailWord_7952863) baseStart_7952863 baseEnd_7952863 := by
    simpa [prefixWord, tailWord_7952863, baseEnd_7952863] using wordTrace_append hprefix tailTrace_7952863
  have hstable : (prefixWord ++ tailWord_7952863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7952863).length < 2 ^ (prefixWord ++ tailWord_7952863).sum := by decide
  have hdescent : baseEnd_7952863 < baseStart_7952863 := by decide
  rcases family_descends (prefixWord ++ tailWord_7952863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7952889 : List Nat := [1, 2, 1, 3, 1, 2, 4, 1, 3, 5]
def baseStart_7952889 : Nat := 118140960795 + 7952889 * 2 ^ 59
def prefixEnd_7952889 : Nat := 4983230072969 + 3 ^ 40 * 7952889 * 2
def baseEnd_7952889 : Nat := 1361218216284946672970945

theorem tailTrace_7952889 : CollatzResearch.WordTrace tailWord_7952889 prefixEnd_7952889 1361218216284946672970945 := by
  unfold tailWord_7952889
  simp only [CollatzResearch.WordTrace]
  refine ⟨290065691685048873150877721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193377127790032582100585147 290065691685048873150877721)
  ·
    refine ⟨217549268763786654863158291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290065691685048873150877721 217549268763786654863158291)
    ·
      refine ⟨326323903145679982294737437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217549268763786654863158291 326323903145679982294737437)
      ·
        refine ⟨122371463679629993360526539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 326323903145679982294737437 122371463679629993360526539)
        ·
          refine ⟨183557195519444990040789809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122371463679629993360526539 183557195519444990040789809)
          ·
            refine ⟨137667896639583742530592357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183557195519444990040789809 137667896639583742530592357)
            ·
              refine ⟨25812730619921951724486067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137667896639583742530592357 25812730619921951724486067)
              ·
                refine ⟨38719095929882927586729101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25812730619921951724486067 38719095929882927586729101)
                ·
                  refine ⟨14519660973706097845023413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38719095929882927586729101 14519660973706097845023413)
                  ·
                    refine ⟨1361218216284946672970945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14519660973706097845023413 1361218216284946672970945)
                    ·
                      rfl

theorem cell23_7952889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 1, 3, 5].length) (baseStart_7952889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7952889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7952889 prefixEnd_7952889 := by exact prefixLift 7952889
  have htrace : WordTrace (prefixWord ++ tailWord_7952889) baseStart_7952889 baseEnd_7952889 := by
    simpa [prefixWord, tailWord_7952889, baseEnd_7952889] using wordTrace_append hprefix tailTrace_7952889
  have hstable : (prefixWord ++ tailWord_7952889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7952889).length < 2 ^ (prefixWord ++ tailWord_7952889).sum := by decide
  have hdescent : baseEnd_7952889 < baseStart_7952889 := by decide
  rcases family_descends (prefixWord ++ tailWord_7952889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7952906 : List Nat := [3, 1, 2, 2, 2, 1, 3, 3, 1, 5]
def baseStart_7952906 : Nat := 118140960795 + 7952906 * 2 ^ 59
def prefixEnd_7952906 : Nat := 4983230072969 + 3 ^ 40 * 7952906 * 2
def baseEnd_7952906 : Nat := 1361221126008655484133419

theorem tailTrace_7952906 : CollatzResearch.WordTrace tailWord_7952906 prefixEnd_7952906 1361221126008655484133419 := by
  unfold tailWord_7952906
  simp only [CollatzResearch.WordTrace]
  refine ⟨72516577931496821263561643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193377541150658190036164381 72516577931496821263561643)
  ·
    refine ⟨108774866897245231895342465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72516577931496821263561643 108774866897245231895342465)
    ·
      refine ⟨81581150172933923921506849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108774866897245231895342465 81581150172933923921506849)
      ·
        refine ⟨61185862629700442941130137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81581150172933923921506849 61185862629700442941130137)
        ·
          refine ⟨45889396972275332205847603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61185862629700442941130137 45889396972275332205847603)
          ·
            refine ⟨68834095458412998308771405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45889396972275332205847603 68834095458412998308771405)
            ·
              refine ⟨25812785796904874365789277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68834095458412998308771405 25812785796904874365789277)
              ·
                refine ⟨9679794673839327887170979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25812785796904874365789277 9679794673839327887170979)
                ·
                  refine ⟨14519692010758991830756469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9679794673839327887170979 14519692010758991830756469)
                  ·
                    refine ⟨1361221126008655484133419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14519692010758991830756469 1361221126008655484133419)
                    ·
                      rfl

theorem cell23_7952906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 3, 1, 5].length) (baseStart_7952906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7952906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7952906 prefixEnd_7952906 := by exact prefixLift 7952906
  have htrace : WordTrace (prefixWord ++ tailWord_7952906) baseStart_7952906 baseEnd_7952906 := by
    simpa [prefixWord, tailWord_7952906, baseEnd_7952906] using wordTrace_append hprefix tailTrace_7952906
  have hstable : (prefixWord ++ tailWord_7952906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7952906).length < 2 ^ (prefixWord ++ tailWord_7952906).sum := by decide
  have hdescent : baseEnd_7952906 < baseStart_7952906 := by decide
  rcases family_descends (prefixWord ++ tailWord_7952906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7952920 : List Nat := [2, 1, 2, 3, 3, 1, 2, 4, 1, 1, 3]
def baseStart_7952920 : Nat := 118140960795 + 7952920 * 2 ^ 59
def prefixEnd_7952920 : Nat := 4983230072969 + 3 ^ 40 * 7952920 * 2
def baseEnd_7952920 : Nat := 4083670566755129397625193

theorem tailTrace_7952920 : CollatzResearch.WordTrace tailWord_7952920 prefixEnd_7952920 4083670566755129397625193 := by
  unfold tailWord_7952920
  simp only [CollatzResearch.WordTrace]
  refine ⟨145033411173968282722628107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193377881565291043630170809 145033411173968282722628107)
  ·
    refine ⟨217550116760952424083942161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145033411173968282722628107 217550116760952424083942161)
    ·
      refine ⟨163162587570714318062956621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217550116760952424083942161 163162587570714318062956621)
      ·
        refine ⟨61185970339017869273608733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163162587570714318062956621 61185970339017869273608733)
        ·
          refine ⟨22944738877131700977603275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61185970339017869273608733 22944738877131700977603275)
          ·
            refine ⟨34417108315697551466404913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22944738877131700977603275 34417108315697551466404913)
            ·
              refine ⟨25812831236773163599803685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34417108315697551466404913 25812831236773163599803685)
              ·
                refine ⟨4839905856894968174963191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25812831236773163599803685 4839905856894968174963191)
                ·
                  refine ⟨7259858785342452262444787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4839905856894968174963191 7259858785342452262444787)
                  ·
                    refine ⟨10889788178013678393667181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7259858785342452262444787 10889788178013678393667181)
                    ·
                      refine ⟨4083670566755129397625193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10889788178013678393667181 4083670566755129397625193)
                      ·
                        rfl

theorem cell23_7952920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 4, 1, 1, 3].length) (baseStart_7952920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7952920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7952920 prefixEnd_7952920 := by exact prefixLift 7952920
  have htrace : WordTrace (prefixWord ++ tailWord_7952920) baseStart_7952920 baseEnd_7952920 := by
    simpa [prefixWord, tailWord_7952920, baseEnd_7952920] using wordTrace_append hprefix tailTrace_7952920
  have hstable : (prefixWord ++ tailWord_7952920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7952920).length < 2 ^ (prefixWord ++ tailWord_7952920).sum := by decide
  have hdescent : baseEnd_7952920 < baseStart_7952920 := by decide
  rcases family_descends (prefixWord ++ tailWord_7952920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7952946 : List Nat := [3, 2, 1, 1, 2, 1, 2, 3, 3, 2, 3]
def baseStart_7952946 : Nat := 118140960795 + 7952946 * 2 ^ 59
def prefixEnd_7952946 : Nat := 4983230072969 + 3 ^ 40 * 7952946 * 2
def baseEnd_7952946 : Nat := 4083683917252146295900073

theorem tailTrace_7952946 : CollatzResearch.WordTrace tailWord_7952946 prefixEnd_7952946 4083683917252146295900073 := by
  unfold tailWord_7952946
  simp only [CollatzResearch.WordTrace]
  refine ⟨72516942661460592971425673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193378513763894914590468461 72516942661460592971425673)
  ·
    refine ⟨54387706996095444728569255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72516942661460592971425673 54387706996095444728569255)
    ·
      refine ⟨81581560494143167092853883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54387706996095444728569255 81581560494143167092853883)
      ·
        refine ⟨122372340741214750639280825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81581560494143167092853883 122372340741214750639280825)
        ·
          refine ⟨91779255555911062979460619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122372340741214750639280825 91779255555911062979460619)
          ·
            refine ⟨137668883333866594469190929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91779255555911062979460619 137668883333866594469190929)
            ·
              refine ⟨103251662500399945851893197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137668883333866594469190929 103251662500399945851893197)
              ·
                refine ⟨38719373437649979694459949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103251662500399945851893197 38719373437649979694459949)
                ·
                  refine ⟨14519765039118742385422481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38719373437649979694459949 14519765039118742385422481)
                  ·
                    refine ⟨10889823779339056789066861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14519765039118742385422481 10889823779339056789066861)
                    ·
                      refine ⟨4083683917252146295900073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10889823779339056789066861 4083683917252146295900073)
                      ·
                        rfl

theorem cell23_7952946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3, 3, 2, 3].length) (baseStart_7952946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7952946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7952946 prefixEnd_7952946 := by exact prefixLift 7952946
  have htrace : WordTrace (prefixWord ++ tailWord_7952946) baseStart_7952946 baseEnd_7952946 := by
    simpa [prefixWord, tailWord_7952946, baseEnd_7952946] using wordTrace_append hprefix tailTrace_7952946
  have hstable : (prefixWord ++ tailWord_7952946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7952946).length < 2 ^ (prefixWord ++ tailWord_7952946).sum := by decide
  have hdescent : baseEnd_7952946 < baseStart_7952946 := by decide
  rcases family_descends (prefixWord ++ tailWord_7952946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7952949 : List Nat := [1, 3, 3, 1, 1, 2, 3, 9]
def baseStart_7952949 : Nat := 118140960795 + 7952949 * 2 ^ 59
def prefixEnd_7952949 : Nat := 4983230072969 + 3 ^ 40 * 7952949 * 2
def baseEnd_7952949 : Nat := 151247609544226288302317

theorem tailTrace_7952949 : CollatzResearch.WordTrace tailWord_7952949 prefixEnd_7952949 151247609544226288302317 := by
  unfold tailWord_7952949
  simp only [CollatzResearch.WordTrace]
  refine ⟨290067880064831503398061901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193378586709887668932041267 290067880064831503398061901)
  ·
    refine ⟨108775455024311813774273213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290067880064831503398061901 108775455024311813774273213)
    ·
      refine ⟨40790795634116930165352455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108775455024311813774273213 40790795634116930165352455)
      ·
        refine ⟨61186193451175395248028683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40790795634116930165352455 61186193451175395248028683)
        ·
          refine ⟨91779290176763092872043025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61186193451175395248028683 91779290176763092872043025)
          ·
            refine ⟨68834467632572319654032269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91779290176763092872043025 68834467632572319654032269)
            ·
              refine ⟨25812925362214619870262101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68834467632572319654032269 25812925362214619870262101)
              ·
                refine ⟨151247609544226288302317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25812925362214619870262101 151247609544226288302317)
                ·
                  rfl

theorem cell23_7952949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 9].length) (baseStart_7952949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7952949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7952949 prefixEnd_7952949 := by exact prefixLift 7952949
  have htrace : WordTrace (prefixWord ++ tailWord_7952949) baseStart_7952949 baseEnd_7952949 := by
    simpa [prefixWord, tailWord_7952949, baseEnd_7952949] using wordTrace_append hprefix tailTrace_7952949
  have hstable : (prefixWord ++ tailWord_7952949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7952949).length < 2 ^ (prefixWord ++ tailWord_7952949).sum := by decide
  have hdescent : baseEnd_7952949 < baseStart_7952949 := by decide
  rcases family_descends (prefixWord ++ tailWord_7952949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7952964 : List Nat := [2, 3, 5, 1, 1, 1, 1, 2, 2, 3, 2]
def baseStart_7952964 : Nat := 118140960795 + 7952964 * 2 ^ 59
def prefixEnd_7952964 : Nat := 4983230072969 + 3 ^ 40 * 7952964 * 2
def baseEnd_7952964 : Nat := 4083693159903927225474991

theorem tailTrace_7952964 : CollatzResearch.WordTrace tailWord_7952964 prefixEnd_7952964 4083693159903927225474991 := by
  unfold tailWord_7952964
  simp only [CollatzResearch.WordTrace]
  refine ⟨145034213579888580479928973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193378951439851440639905297 145034213579888580479928973)
  ·
    refine ⟨54387830092458217679973365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145034213579888580479928973 54387830092458217679973365)
    ·
      refine ⟨5098859071167957907497503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54387830092458217679973365 5098859071167957907497503)
      ·
        refine ⟨7648288606751936861246255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5098859071167957907497503 7648288606751936861246255)
        ·
          refine ⟨11472432910127905291869383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7648288606751936861246255 11472432910127905291869383)
          ·
            refine ⟨17208649365191857937804075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11472432910127905291869383 17208649365191857937804075)
            ·
              refine ⟨25812974047787786906706113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17208649365191857937804075 25812974047787786906706113)
              ·
                refine ⟨19359730535840840180029585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25812974047787786906706113 19359730535840840180029585)
                ·
                  refine ⟨14519797901880630135022189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19359730535840840180029585 14519797901880630135022189)
                  ·
                    refine ⟨5444924213205236300633321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14519797901880630135022189 5444924213205236300633321)
                    ·
                      refine ⟨4083693159903927225474991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5444924213205236300633321 4083693159903927225474991)
                      ·
                        rfl

theorem cell23_7952964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_7952964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7952964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7952964 prefixEnd_7952964 := by exact prefixLift 7952964
  have htrace : WordTrace (prefixWord ++ tailWord_7952964) baseStart_7952964 baseEnd_7952964 := by
    simpa [prefixWord, tailWord_7952964, baseEnd_7952964] using wordTrace_append hprefix tailTrace_7952964
  have hstable : (prefixWord ++ tailWord_7952964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7952964).length < 2 ^ (prefixWord ++ tailWord_7952964).sum := by decide
  have hdescent : baseEnd_7952964 < baseStart_7952964 := by decide
  rcases family_descends (prefixWord ++ tailWord_7952964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7952986 : List Nat := [3, 1, 1, 2, 1, 1, 1, 1, 1, 9, 2]
def baseStart_7952986 : Nat := 118140960795 + 7952986 * 2 ^ 59
def prefixEnd_7952986 : Nat := 4983230072969 + 3 ^ 40 * 7952986 * 2
def baseEnd_7952986 : Nat := 4083704456478326139399889

theorem tailTrace_7952986 : CollatzResearch.WordTrace tailWord_7952986 prefixEnd_7952986 4083704456478326139399889 := by
  unfold tailWord_7952986
  simp only [CollatzResearch.WordTrace]
  refine ⟨72517307391424364679289703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193379486377131639144772541 72517307391424364679289703)
  ·
    refine ⟨108775961087136547018934555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72517307391424364679289703 108775961087136547018934555)
    ·
      refine ⟨163163941630704820528401833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108775961087136547018934555 163163941630704820528401833)
      ·
        refine ⟨122372956223028615396301375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163163941630704820528401833 122372956223028615396301375)
        ·
          refine ⟨183559434334542923094452063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122372956223028615396301375 183559434334542923094452063)
          ·
            refine ⟨275339151501814384641678095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183559434334542923094452063 275339151501814384641678095)
            ·
              refine ⟨413008727252721576962517143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275339151501814384641678095 413008727252721576962517143)
              ·
                refine ⟨619513090879082365443775715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 413008727252721576962517143 619513090879082365443775715)
                ·
                  refine ⟨929269636318623548165663573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 619513090879082365443775715 929269636318623548165663573)
                  ·
                    refine ⟨5444939275304434852533185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 929269636318623548165663573 5444939275304434852533185)
                    ·
                      refine ⟨4083704456478326139399889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5444939275304434852533185 4083704456478326139399889)
                      ·
                        rfl

theorem cell23_7952986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 1, 9, 2].length) (baseStart_7952986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7952986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7952986 prefixEnd_7952986 := by exact prefixLift 7952986
  have htrace : WordTrace (prefixWord ++ tailWord_7952986) baseStart_7952986 baseEnd_7952986 := by
    simpa [prefixWord, tailWord_7952986, baseEnd_7952986] using wordTrace_append hprefix tailTrace_7952986
  have hstable : (prefixWord ++ tailWord_7952986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7952986).length < 2 ^ (prefixWord ++ tailWord_7952986).sum := by decide
  have hdescent : baseEnd_7952986 < baseStart_7952986 := by decide
  rcases family_descends (prefixWord ++ tailWord_7952986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7952994 : List Nat := [3, 3, 2, 3, 2, 1, 1, 2, 1, 1, 4]
def baseStart_7952994 : Nat := 118140960795 + 7952994 * 2 ^ 59
def prefixEnd_7952994 : Nat := 4983230072969 + 3 ^ 40 * 7952994 * 2
def baseEnd_7952994 : Nat := 4083708564323562108099853

theorem tailTrace_7952994 : CollatzResearch.WordTrace tailWord_7952994 prefixEnd_7952994 4083708564323562108099853 := by
  unfold tailWord_7952994
  simp only [CollatzResearch.WordTrace]
  refine ⟨72517380337417119020862509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193379680899778984055633357 72517380337417119020862509)
  ·
    refine ⟨27194017626531419632823441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72517380337417119020862509 27194017626531419632823441)
    ·
      refine ⟨20395513219898564724617581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27194017626531419632823441 20395513219898564724617581)
      ·
        refine ⟨7648317457461961771731593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20395513219898564724617581 7648317457461961771731593)
        ·
          refine ⟨5736238093096471328798695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7648317457461961771731593 5736238093096471328798695)
          ·
            refine ⟨8604357139644706993198043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5736238093096471328798695 8604357139644706993198043)
            ·
              refine ⟨12906535709467060489797065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8604357139644706993198043 12906535709467060489797065)
              ·
                refine ⟨9679901782100295367347799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12906535709467060489797065 9679901782100295367347799)
                ·
                  refine ⟨14519852673150443051021699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9679901782100295367347799 14519852673150443051021699)
                  ·
                    refine ⟨21779779009725664576532549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14519852673150443051021699 21779779009725664576532549)
                    ·
                      refine ⟨4083708564323562108099853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21779779009725664576532549 4083708564323562108099853)
                      ·
                        rfl

theorem cell23_7952994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_7952994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7952994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7952994 prefixEnd_7952994 := by exact prefixLift 7952994
  have htrace : WordTrace (prefixWord ++ tailWord_7952994) baseStart_7952994 baseEnd_7952994 := by
    simpa [prefixWord, tailWord_7952994, baseEnd_7952994] using wordTrace_append hprefix tailTrace_7952994
  have hstable : (prefixWord ++ tailWord_7952994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7952994).length < 2 ^ (prefixWord ++ tailWord_7952994).sum := by decide
  have hdescent : baseEnd_7952994 < baseStart_7952994 := by decide
  rcases family_descends (prefixWord ++ tailWord_7952994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7952997 : List Nat := [1, 3, 1, 3, 5, 1, 1, 2, 1, 2, 3]
def baseStart_7952997 : Nat := 118140960795 + 7952997 * 2 ^ 59
def prefixEnd_7952997 : Nat := 4983230072969 + 3 ^ 40 * 7952997 * 2
def baseEnd_7952997 : Nat := 4083710104765525596362339

theorem tailTrace_7952997 : CollatzResearch.WordTrace tailWord_7952997 prefixEnd_7952997 4083710104765525596362339 := by
  unfold tailWord_7952997
  simp only [CollatzResearch.WordTrace]
  refine ⟨290069630768657607595809245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193379753845771738397206163 290069630768657607595809245)
  ·
    refine ⟨108776111538246602848428467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290069630768657607595809245 108776111538246602848428467)
    ·
      refine ⟨163164167307369904272642701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108776111538246602848428467 163164167307369904272642701)
      ·
        refine ⟨61186562740263714102241013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163164167307369904272642701 61186562740263714102241013)
        ·
          refine ⟨5736240256899723197085095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61186562740263714102241013 5736240256899723197085095)
          ·
            refine ⟨8604360385349584795627643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5736240256899723197085095 8604360385349584795627643)
            ·
              refine ⟨12906540578024377193441465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8604360385349584795627643 12906540578024377193441465)
              ·
                refine ⟨9679905433518282895081099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12906540578024377193441465 9679905433518282895081099)
                ·
                  refine ⟨14519858150277424342621649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9679905433518282895081099 14519858150277424342621649)
                  ·
                    refine ⟨10889893612708068256966237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14519858150277424342621649 10889893612708068256966237)
                    ·
                      refine ⟨4083710104765525596362339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10889893612708068256966237 4083710104765525596362339)
                      ·
                        rfl

theorem cell23_7952997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 2, 1, 2, 3].length) (baseStart_7952997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7952997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7952997 prefixEnd_7952997 := by exact prefixLift 7952997
  have htrace : WordTrace (prefixWord ++ tailWord_7952997) baseStart_7952997 baseEnd_7952997 := by
    simpa [prefixWord, tailWord_7952997, baseEnd_7952997] using wordTrace_append hprefix tailTrace_7952997
  have hstable : (prefixWord ++ tailWord_7952997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7952997).length < 2 ^ (prefixWord ++ tailWord_7952997).sum := by decide
  have hdescent : baseEnd_7952997 < baseStart_7952997 := by decide
  rcases family_descends (prefixWord ++ tailWord_7952997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7952999 : List Nat := [1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 8]
def baseStart_7952999 : Nat := 118140960795 + 7952999 * 2 ^ 59
def prefixEnd_7952999 : Nat := 4983230072969 + 3 ^ 40 * 7952999 * 2
def baseEnd_7952999 : Nat := 4083711131726834588537329

theorem tailTrace_7952999 : CollatzResearch.WordTrace tailWord_7952999 prefixEnd_7952999 4083711131726834588537329 := by
  unfold tailWord_7952999
  simp only [CollatzResearch.WordTrace]
  refine ⟨290069703714650361937382051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193379802476433574624921367 290069703714650361937382051)
  ·
    refine ⟨435104555571975542906073077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290069703714650361937382051 435104555571975542906073077)
    ·
      refine ⟨40791052084872707147444351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 435104555571975542906073077 40791052084872707147444351)
      ·
        refine ⟨61186578127309060721166527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40791052084872707147444351 61186578127309060721166527)
        ·
          refine ⟨91779867190963591081749791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61186578127309060721166527 91779867190963591081749791)
          ·
            refine ⟨137669800786445386622624687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91779867190963591081749791 137669800786445386622624687)
            ·
              refine ⟨206504701179668079933937031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137669800786445386622624687 206504701179668079933937031)
              ·
                refine ⟨309757051769502119900905547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206504701179668079933937031 309757051769502119900905547)
                ·
                  refine ⟨464635577654253179851358321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 309757051769502119900905547 464635577654253179851358321)
                  ·
                    refine ⟨348476683240689884888518741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 464635577654253179851358321 348476683240689884888518741)
                    ·
                      refine ⟨4083711131726834588537329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 348476683240689884888518741 4083711131726834588537329)
                      ·
                        rfl

theorem cell23_7952999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_7952999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7952999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7952999 prefixEnd_7952999 := by exact prefixLift 7952999
  have htrace : WordTrace (prefixWord ++ tailWord_7952999) baseStart_7952999 baseEnd_7952999 := by
    simpa [prefixWord, tailWord_7952999, baseEnd_7952999] using wordTrace_append hprefix tailTrace_7952999
  have hstable : (prefixWord ++ tailWord_7952999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7952999).length < 2 ^ (prefixWord ++ tailWord_7952999).sum := by decide
  have hdescent : baseEnd_7952999 < baseStart_7952999 := by decide
  rcases family_descends (prefixWord ++ tailWord_7952999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7953003 : List Nat := [1, 1, 1, 1, 2, 2, 1, 8, 1, 3, 2]
def baseStart_7953003 : Nat := 118140960795 + 7953003 * 2 ^ 59
def prefixEnd_7953003 : Nat := 4983230072969 + 3 ^ 40 * 7953003 * 2
def baseEnd_7953003 : Nat := 4083713185649452572887311

theorem tailTrace_7953003 : CollatzResearch.WordTrace tailWord_7953003 prefixEnd_7953003 4083713185649452572887311 := by
  unfold tailWord_7953003
  simp only [CollatzResearch.WordTrace]
  refine ⟨290069849606635870620527663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193379899737757247080351775 290069849606635870620527663)
  ·
    refine ⟨435104774409953805930791495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290069849606635870620527663 435104774409953805930791495)
    ·
      refine ⟨652657161614930708896187243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435104774409953805930791495 652657161614930708896187243)
      ·
        refine ⟨978985742422396063344280865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 652657161614930708896187243 978985742422396063344280865)
        ·
          refine ⟨734239306816797047508210649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 978985742422396063344280865 734239306816797047508210649)
          ·
            refine ⟨550679480112597785631157987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 734239306816797047508210649 550679480112597785631157987)
            ·
              refine ⟨826019220168896678446736981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 550679480112597785631157987 826019220168896678446736981)
              ·
                refine ⟨9679912736354257950547699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 826019220168896678446736981 9679912736354257950547699)
                ·
                  refine ⟨14519869104531386925821549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9679912736354257950547699 14519869104531386925821549)
                  ·
                    refine ⟨5444950914199270097183081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14519869104531386925821549 5444950914199270097183081)
                    ·
                      refine ⟨4083713185649452572887311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5444950914199270097183081 4083713185649452572887311)
                      ·
                        rfl

theorem cell23_7953003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 8, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 8, 1, 3, 2].length) (baseStart_7953003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7953003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7953003 prefixEnd_7953003 := by exact prefixLift 7953003
  have htrace : WordTrace (prefixWord ++ tailWord_7953003) baseStart_7953003 baseEnd_7953003 := by
    simpa [prefixWord, tailWord_7953003, baseEnd_7953003] using wordTrace_append hprefix tailTrace_7953003
  have hstable : (prefixWord ++ tailWord_7953003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7953003).length < 2 ^ (prefixWord ++ tailWord_7953003).sum := by decide
  have hdescent : baseEnd_7953003 < baseStart_7953003 := by decide
  rcases family_descends (prefixWord ++ tailWord_7953003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7953009 : List Nat := [1, 2, 2, 2, 1, 1, 1, 1, 6, 6]
def baseStart_7953009 : Nat := 118140960795 + 7953009 * 2 ^ 59
def prefixEnd_7953009 : Nat := 4983230072969 + 3 ^ 40 * 7953009 * 2
def baseEnd_7953009 : Nat := 1361238755511126516470761

theorem tailTrace_7953009 : CollatzResearch.WordTrace tailWord_7953009 prefixEnd_7953009 1361238755511126516470761 := by
  unfold tailWord_7953009
  simp only [CollatzResearch.WordTrace]
  refine ⟨290070068444614133645246081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193380045629742755763497387 290070068444614133645246081)
  ·
    refine ⟨217552551333460600233934561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290070068444614133645246081 217552551333460600233934561)
    ·
      refine ⟨163164413500095450175450921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217552551333460600233934561 163164413500095450175450921)
      ·
        refine ⟨122373310125071587631588191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163164413500095450175450921 122373310125071587631588191)
        ·
          refine ⟨183559965187607381447382287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122373310125071587631588191 183559965187607381447382287)
          ·
            refine ⟨275339947781411072171073431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183559965187607381447382287 275339947781411072171073431)
            ·
              refine ⟨413009921672116608256610147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275339947781411072171073431 413009921672116608256610147)
              ·
                refine ⟨619514882508174912384915221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 413009921672116608256610147 619514882508174912384915221)
                ·
                  refine ⟨29039760117570699018042901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 619514882508174912384915221 29039760117570699018042901)
                  ·
                    refine ⟨1361238755511126516470761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29039760117570699018042901 1361238755511126516470761)
                    ·
                      rfl

theorem cell23_7953009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 6, 6].length) (baseStart_7953009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7953009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7953009 prefixEnd_7953009 := by exact prefixLift 7953009
  have htrace : WordTrace (prefixWord ++ tailWord_7953009) baseStart_7953009 baseEnd_7953009 := by
    simpa [prefixWord, tailWord_7953009, baseEnd_7953009] using wordTrace_append hprefix tailTrace_7953009
  have hstable : (prefixWord ++ tailWord_7953009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7953009).length < 2 ^ (prefixWord ++ tailWord_7953009).sum := by decide
  have hdescent : baseEnd_7953009 < baseStart_7953009 := by decide
  rcases family_descends (prefixWord ++ tailWord_7953009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7953019 : List Nat := [1, 1, 1, 1, 1, 4, 2, 3, 1, 3, 5]
def baseStart_7953019 : Nat := 118140960795 + 7953019 * 2 ^ 59
def prefixEnd_7953019 : Nat := 4983230072969 + 3 ^ 40 * 7953019 * 2
def baseEnd_7953019 : Nat := 4083721401339924510287237

theorem tailTrace_7953019 : CollatzResearch.WordTrace tailWord_7953019 prefixEnd_7953019 4083721401339924510287237 := by
  unfold tailWord_7953019
  simp only [CollatzResearch.WordTrace]
  refine ⟨290070433174577905353110111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193380288783051936902073407 290070433174577905353110111)
  ·
    refine ⟨435105649761866858029665167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290070433174577905353110111 435105649761866858029665167)
    ·
      refine ⟨652658474642800287044497751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435105649761866858029665167 652658474642800287044497751)
      ·
        refine ⟨978987711964200430566746627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 652658474642800287044497751 978987711964200430566746627)
        ·
          refine ⟨1468481567946300645850119941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 978987711964200430566746627 1468481567946300645850119941)
          ·
            refine ⟨275340293989931371096897489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1468481567946300645850119941 275340293989931371096897489)
            ·
              refine ⟨206505220492448528322673117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 275340293989931371096897489 206505220492448528322673117)
              ·
                refine ⟨77439457684668198121002419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 206505220492448528322673117 77439457684668198121002419)
                ·
                  refine ⟨116159186527002297181503629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77439457684668198121002419 116159186527002297181503629)
                  ·
                    refine ⟨43559694947625861443063861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 116159186527002297181503629 43559694947625861443063861)
                    ·
                      refine ⟨4083721401339924510287237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43559694947625861443063861 4083721401339924510287237)
                      ·
                        rfl

theorem cell23_7953019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 3, 5].length) (baseStart_7953019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7953019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7953019 prefixEnd_7953019 := by exact prefixLift 7953019
  have htrace : WordTrace (prefixWord ++ tailWord_7953019) baseStart_7953019 baseEnd_7953019 := by
    simpa [prefixWord, tailWord_7953019, baseEnd_7953019] using wordTrace_append hprefix tailTrace_7953019
  have hstable : (prefixWord ++ tailWord_7953019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7953019).length < 2 ^ (prefixWord ++ tailWord_7953019).sum := by decide
  have hdescent : baseEnd_7953019 < baseStart_7953019 := by decide
  rcases family_descends (prefixWord ++ tailWord_7953019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7953101 : List Nat := [1, 6, 2, 1, 3, 1, 1, 1, 1, 4, 2]
def baseStart_7953101 : Nat := 118140960795 + 7953101 * 2 ^ 59
def prefixEnd_7953101 : Nat := 4983230072969 + 3 ^ 40 * 7953101 * 2
def baseEnd_7953101 : Nat := 4083763506753593189461861

theorem tailTrace_7953101 : CollatzResearch.WordTrace tailWord_7953101 prefixEnd_7953101 4083763506753593189461861 := by
  unfold tailWord_7953101
  simp only [CollatzResearch.WordTrace]
  refine ⟨290073423960280833357595157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193382282640187222238396771 290073423960280833357595157)
  ·
    refine ⟨13597191748138164063637273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 290073423960280833357595157 13597191748138164063637273)
    ·
      refine ⟨10197893811103623047727955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13597191748138164063637273 10197893811103623047727955)
      ·
        refine ⟨15296840716655434571591933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10197893811103623047727955 15296840716655434571591933)
        ·
          refine ⟨5736315268745787964346975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15296840716655434571591933 5736315268745787964346975)
          ·
            refine ⟨8604472903118681946520463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5736315268745787964346975 8604472903118681946520463)
            ·
              refine ⟨12906709354678022919780695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8604472903118681946520463 12906709354678022919780695)
              ·
                refine ⟨19360064032017034379671043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12906709354678022919780695 19360064032017034379671043)
                ·
                  refine ⟨29040096048025551569506565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19360064032017034379671043 29040096048025551569506565)
                  ·
                    refine ⟨5445018009004790919282481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29040096048025551569506565 5445018009004790919282481)
                    ·
                      refine ⟨4083763506753593189461861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5445018009004790919282481 4083763506753593189461861)
                      ·
                        rfl

theorem cell23_7953101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_7953101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7953101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7953101 prefixEnd_7953101 := by exact prefixLift 7953101
  have htrace : WordTrace (prefixWord ++ tailWord_7953101) baseStart_7953101 baseEnd_7953101 := by
    simpa [prefixWord, tailWord_7953101, baseEnd_7953101] using wordTrace_append hprefix tailTrace_7953101
  have hstable : (prefixWord ++ tailWord_7953101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7953101).length < 2 ^ (prefixWord ++ tailWord_7953101).sum := by decide
  have hdescent : baseEnd_7953101 < baseStart_7953101 := by decide
  rcases family_descends (prefixWord ++ tailWord_7953101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7953123 : List Nat := [1, 1, 1, 7, 1, 1, 2, 1, 1, 3, 4]
def baseStart_7953123 : Nat := 118140960795 + 7953123 * 2 ^ 59
def prefixEnd_7953123 : Nat := 4983230072969 + 3 ^ 40 * 7953123 * 2
def baseEnd_7953123 : Nat := 4083774803327992103386759

theorem tailTrace_7953123 : CollatzResearch.WordTrace tailWord_7953123 prefixEnd_7953123 4083774803327992103386759 := by
  unfold tailWord_7953123
  simp only [CollatzResearch.WordTrace]
  refine ⟨290074226366201131114896023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193382817577467420743264015 290074226366201131114896023)
  ·
    refine ⟨435111339549301696672344035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290074226366201131114896023 435111339549301696672344035)
    ·
      refine ⟨652667009323952545008516053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435111339549301696672344035 652667009323952545008516053)
      ·
        refine ⟨15296883031030137773637095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 652667009323952545008516053 15296883031030137773637095)
        ·
          refine ⟨22945324546545206660455643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15296883031030137773637095 22945324546545206660455643)
          ·
            refine ⟨34417986819817809990683465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22945324546545206660455643 34417986819817809990683465)
            ·
              refine ⟨25813490114863357493012599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34417986819817809990683465 25813490114863357493012599)
              ·
                refine ⟨38720235172295036239518899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25813490114863357493012599 38720235172295036239518899)
                ·
                  refine ⟨58080352758442554359278349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38720235172295036239518899 58080352758442554359278349)
                  ·
                    refine ⟨21780132284415957884729381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58080352758442554359278349 21780132284415957884729381)
                    ·
                      refine ⟨4083774803327992103386759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21780132284415957884729381 4083774803327992103386759)
                      ·
                        rfl

theorem cell23_7953123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_7953123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7953123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7953123 prefixEnd_7953123 := by exact prefixLift 7953123
  have htrace : WordTrace (prefixWord ++ tailWord_7953123) baseStart_7953123 baseEnd_7953123 := by
    simpa [prefixWord, tailWord_7953123, baseEnd_7953123] using wordTrace_append hprefix tailTrace_7953123
  have hstable : (prefixWord ++ tailWord_7953123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7953123).length < 2 ^ (prefixWord ++ tailWord_7953123).sum := by decide
  have hdescent : baseEnd_7953123 < baseStart_7953123 := by decide
  rcases family_descends (prefixWord ++ tailWord_7953123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7953141 : List Nat := [1, 3, 6, 1, 1, 1, 3, 2, 5]
def baseStart_7953141 : Nat := 118140960795 + 7953141 * 2 ^ 59
def prefixEnd_7953141 : Nat := 4983230072969 + 3 ^ 40 * 7953141 * 2
def baseEnd_7953141 : Nat := 453753782886641448106853

theorem tailTrace_7953141 : CollatzResearch.WordTrace tailWord_7953141 prefixEnd_7953141 453753782886641448106853 := by
  unfold tailWord_7953141
  simp only [CollatzResearch.WordTrace]
  refine ⟨290074882880135920189051277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193383255253423946792700851 290074882880135920189051277)
  ·
    refine ⟨108778081080050970070894229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290074882880135920189051277 108778081080050970070894229)
    ·
      refine ⟨5098972550627389222073167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 108778081080050970070894229 5098972550627389222073167)
      ·
        refine ⟨7648458825941083833109751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5098972550627389222073167 7648458825941083833109751)
        ·
          refine ⟨11472688238911625749664627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7648458825941083833109751 11472688238911625749664627)
          ·
            refine ⟨17209032358367438624496941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11472688238911625749664627 17209032358367438624496941)
            ·
              refine ⟨6453387134387789484186353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17209032358367438624496941 6453387134387789484186353)
              ·
                refine ⟨4840040350790842113139765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6453387134387789484186353 4840040350790842113139765)
                ·
                  refine ⟨453753782886641448106853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4840040350790842113139765 453753782886641448106853)
                  ·
                    rfl

theorem cell23_7953141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 3, 2, 5].length) (baseStart_7953141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7953141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7953141 prefixEnd_7953141 := by exact prefixLift 7953141
  have htrace : WordTrace (prefixWord ++ tailWord_7953141) baseStart_7953141 baseEnd_7953141 := by
    simpa [prefixWord, tailWord_7953141, baseEnd_7953141] using wordTrace_append hprefix tailTrace_7953141
  have hstable : (prefixWord ++ tailWord_7953141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7953141).length < 2 ^ (prefixWord ++ tailWord_7953141).sum := by decide
  have hdescent : baseEnd_7953141 < baseStart_7953141 := by decide
  rcases family_descends (prefixWord ++ tailWord_7953141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7953146 : List Nat := [3, 1, 1, 1, 1, 3, 4, 1, 8]
def baseStart_7953146 : Nat := 118140960795 + 7953146 * 2 ^ 59
def prefixEnd_7953146 : Nat := 4983230072969 + 3 ^ 40 * 7953146 * 2
def baseEnd_7953146 : Nat := 453754068153671723711017

theorem tailTrace_7953146 : CollatzResearch.WordTrace tailWord_7953146 prefixEnd_7953146 453754068153671723711017 := by
  unfold tailWord_7953146
  simp only [CollatzResearch.WordTrace]
  refine ⟨72518766311279451510745823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193383376830078537361988861 72518766311279451510745823)
  ·
    refine ⟨108778149466919177266118735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72518766311279451510745823 108778149466919177266118735)
    ·
      refine ⟨163167224200378765899178103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108778149466919177266118735 163167224200378765899178103)
      ·
        refine ⟨244750836300568148848767155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163167224200378765899178103 244750836300568148848767155)
        ·
          refine ⟨367126254450852223273150733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244750836300568148848767155 367126254450852223273150733)
          ·
            refine ⟨137672345419069583727431525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 367126254450852223273150733 137672345419069583727431525)
            ·
              refine ⟨25813564766075546948893411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137672345419069583727431525 25813564766075546948893411)
              ·
                refine ⟨38720347149113320423340117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25813564766075546948893411 38720347149113320423340117)
                ·
                  refine ⟨453754068153671723711017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38720347149113320423340117 453754068153671723711017)
                  ·
                    rfl

theorem cell23_7953146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 1, 8].length) (baseStart_7953146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7953146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7953146 prefixEnd_7953146 := by exact prefixLift 7953146
  have htrace : WordTrace (prefixWord ++ tailWord_7953146) baseStart_7953146 baseEnd_7953146 := by
    simpa [prefixWord, tailWord_7953146, baseEnd_7953146] using wordTrace_append hprefix tailTrace_7953146
  have hstable : (prefixWord ++ tailWord_7953146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7953146).length < 2 ^ (prefixWord ++ tailWord_7953146).sum := by decide
  have hdescent : baseEnd_7953146 < baseStart_7953146 := by decide
  rcases family_descends (prefixWord ++ tailWord_7953146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7953207 : List Nat := [1, 1, 3, 1, 2, 1, 5, 4, 1, 1, 3]
def baseStart_7953207 : Nat := 118140960795 + 7953207 * 2 ^ 59
def prefixEnd_7953207 : Nat := 4983230072969 + 3 ^ 40 * 7953207 * 2
def baseEnd_7953207 : Nat := 4083817935702969774736373

theorem tailTrace_7953207 : CollatzResearch.WordTrace tailWord_7953207 prefixEnd_7953207 4083817935702969774736373 := by
  unfold tailWord_7953207
  simp only [CollatzResearch.WordTrace]
  refine ⟨290077290097896813460953875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193384860065264542307302583 290077290097896813460953875)
  ·
    refine ⟨435115935146845220191430813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290077290097896813460953875 435115935146845220191430813)
    ·
      refine ⟨163168475680066957571786555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 435115935146845220191430813 163168475680066957571786555)
      ·
        refine ⟨244752713520100436357679833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163168475680066957571786555 244752713520100436357679833)
        ·
          refine ⟨183564535140075327268259875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244752713520100436357679833 183564535140075327268259875)
          ·
            refine ⟨275346802710112990902389813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183564535140075327268259875 275346802710112990902389813)
            ·
              refine ⟨25813762754073092897099045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 275346802710112990902389813 25813762754073092897099045)
              ·
                refine ⟨4840080516388704918206071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25813762754073092897099045 4840080516388704918206071)
                ·
                  refine ⟨7260120774583057377309107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4840080516388704918206071 7260120774583057377309107)
                  ·
                    refine ⟨10890181161874586065963661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7260120774583057377309107 10890181161874586065963661)
                    ·
                      refine ⟨4083817935702969774736373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10890181161874586065963661 4083817935702969774736373)
                      ·
                        rfl

theorem cell23_7953207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 4, 1, 1, 3].length) (baseStart_7953207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7953207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7953207 prefixEnd_7953207 := by exact prefixLift 7953207
  have htrace : WordTrace (prefixWord ++ tailWord_7953207) baseStart_7953207 baseEnd_7953207 := by
    simpa [prefixWord, tailWord_7953207, baseEnd_7953207] using wordTrace_append hprefix tailTrace_7953207
  have hstable : (prefixWord ++ tailWord_7953207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7953207).length < 2 ^ (prefixWord ++ tailWord_7953207).sum := by decide
  have hdescent : baseEnd_7953207 < baseStart_7953207 := by decide
  rcases family_descends (prefixWord ++ tailWord_7953207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7953223 : List Nat := [1, 1, 4, 1, 2, 1, 1, 2, 6, 4]
def baseStart_7953223 : Nat := 118140960795 + 7953223 * 2 ^ 59
def prefixEnd_7953223 : Nat := 4983230072969 + 3 ^ 40 * 7953223 * 2
def baseEnd_7953223 : Nat := 1361275383797813904045433

theorem tailTrace_7953223 : CollatzResearch.WordTrace tailWord_7953223 prefixEnd_7953223 1361275383797813904045433 := by
  unfold tailWord_7953223
  simp only [CollatzResearch.WordTrace]
  refine ⟨290077873665838848193536323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193385249110559232129024215 290077873665838848193536323)
  ·
    refine ⟨435116810498758272290304485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290077873665838848193536323 435116810498758272290304485)
    ·
      refine ⟨81584401968517176054432091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 435116810498758272290304485 81584401968517176054432091)
      ·
        refine ⟨122376602952775764081648137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81584401968517176054432091 122376602952775764081648137)
        ·
          refine ⟨91782452214581823061236103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122376602952775764081648137 91782452214581823061236103)
          ·
            refine ⟨137673678321872734591854155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91782452214581823061236103 137673678321872734591854155)
            ·
              refine ⟨206510517482809101887781233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137673678321872734591854155 206510517482809101887781233)
              ·
                refine ⟨154882888112106826415835925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 206510517482809101887781233 154882888112106826415835925)
                ·
                  refine ⟨7260135380255007488242309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 154882888112106826415835925 7260135380255007488242309)
                  ·
                    refine ⟨1361275383797813904045433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7260135380255007488242309 1361275383797813904045433)
                    ·
                      rfl

theorem cell23_7953223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 6, 4].length) (baseStart_7953223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7953223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7953223 prefixEnd_7953223 := by exact prefixLift 7953223
  have htrace : WordTrace (prefixWord ++ tailWord_7953223) baseStart_7953223 baseEnd_7953223 := by
    simpa [prefixWord, tailWord_7953223, baseEnd_7953223] using wordTrace_append hprefix tailTrace_7953223
  have hstable : (prefixWord ++ tailWord_7953223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7953223).length < 2 ^ (prefixWord ++ tailWord_7953223).sum := by decide
  have hdescent : baseEnd_7953223 < baseStart_7953223 := by decide
  rcases family_descends (prefixWord ++ tailWord_7953223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7953244 : List Nat := [2, 2, 4, 2, 1, 3, 2, 1, 1, 5]
def baseStart_7953244 : Nat := 118140960795 + 7953244 * 2 ^ 59
def prefixEnd_7953244 : Nat := 4983230072969 + 3 ^ 40 * 7953244 * 2
def baseEnd_7953244 : Nat := 1361278978162395376657901

theorem tailTrace_7953244 : CollatzResearch.WordTrace tailWord_7953244 prefixEnd_7953244 1361278978162395376657901 := by
  unfold tailWord_7953244
  simp only [CollatzResearch.WordTrace]
  refine ⟨145039319799381384390025393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193385759732508512520033857 145039319799381384390025393)
  ·
    refine ⟨108779489849536038292519045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145039319799381384390025393 108779489849536038292519045)
    ·
      refine ⟨20396154346788007179847321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108779489849536038292519045 20396154346788007179847321)
      ·
        refine ⟨15297115760091005384885491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20396154346788007179847321 15297115760091005384885491)
        ·
          refine ⟨22945673640136508077328237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15297115760091005384885491 22945673640136508077328237)
          ·
            refine ⟨8604627615051190528998089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22945673640136508077328237 8604627615051190528998089)
            ·
              refine ⟨6453470711288392896748567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8604627615051190528998089 6453470711288392896748567)
              ·
                refine ⟨9680206066932589345122851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6453470711288392896748567 9680206066932589345122851)
                ·
                  refine ⟨14520309100398884017684277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9680206066932589345122851 14520309100398884017684277)
                  ·
                    refine ⟨1361278978162395376657901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14520309100398884017684277 1361278978162395376657901)
                    ·
                      rfl

theorem cell23_7953244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_7953244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7953244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7953244 prefixEnd_7953244 := by exact prefixLift 7953244
  have htrace : WordTrace (prefixWord ++ tailWord_7953244) baseStart_7953244 baseEnd_7953244 := by
    simpa [prefixWord, tailWord_7953244, baseEnd_7953244] using wordTrace_append hprefix tailTrace_7953244
  have hstable : (prefixWord ++ tailWord_7953244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7953244).length < 2 ^ (prefixWord ++ tailWord_7953244).sum := by decide
  have hdescent : baseEnd_7953244 < baseStart_7953244 := by decide
  rcases family_descends (prefixWord ++ tailWord_7953244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7953263 : List Nat := [1, 1, 2, 1, 3, 1, 1, 4, 3, 3, 3]
def baseStart_7953263 : Nat := 118140960795 + 7953263 * 2 ^ 59
def prefixEnd_7953263 : Nat := 4983230072969 + 3 ^ 40 * 7953263 * 2
def baseEnd_7953263 : Nat := 4083846690619621555636115

theorem tailTrace_7953263 : CollatzResearch.WordTrace tailWord_7953263 prefixEnd_7953263 4083846690619621555636115 := by
  unfold tailWord_7953263
  simp only [CollatzResearch.WordTrace]
  refine ⟨290079332585693935024992443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193386221723795956683328295 290079332585693935024992443)
  ·
    refine ⟨435118998878540902537488665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290079332585693935024992443 435118998878540902537488665)
    ·
      refine ⟨326339249158905676903116499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 435118998878540902537488665 326339249158905676903116499)
      ·
        refine ⟨489508873738358515354674749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326339249158905676903116499 489508873738358515354674749)
        ·
          refine ⟨183565827651884443258003031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 489508873738358515354674749 183565827651884443258003031)
          ·
            refine ⟨275348741477826664887004547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183565827651884443258003031 275348741477826664887004547)
            ·
              refine ⟨413023112216739997330506821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275348741477826664887004547 413023112216739997330506821)
              ·
                refine ⟨77441833540638749499470029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 413023112216739997330506821 77441833540638749499470029)
                ·
                  refine ⟨29040687577739531062301261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 77441833540638749499470029 29040687577739531062301261)
                  ·
                    refine ⟨10890257841652324148362973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29040687577739531062301261 10890257841652324148362973)
                    ·
                      refine ⟨4083846690619621555636115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10890257841652324148362973 4083846690619621555636115)
                      ·
                        rfl

theorem cell23_7953263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 3, 3, 3].length) (baseStart_7953263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7953263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7953263 prefixEnd_7953263 := by exact prefixLift 7953263
  have htrace : WordTrace (prefixWord ++ tailWord_7953263) baseStart_7953263 baseEnd_7953263 := by
    simpa [prefixWord, tailWord_7953263, baseEnd_7953263] using wordTrace_append hprefix tailTrace_7953263
  have hstable : (prefixWord ++ tailWord_7953263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7953263).length < 2 ^ (prefixWord ++ tailWord_7953263).sum := by decide
  have hdescent : baseEnd_7953263 < baseStart_7953263 := by decide
  rcases family_descends (prefixWord ++ tailWord_7953263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7953264 : List Nat := [2, 1, 1, 1, 4, 1, 4, 4, 1, 2, 2]
def baseStart_7953264 : Nat := 118140960795 + 7953264 * 2 ^ 59
def prefixEnd_7953264 : Nat := 4983230072969 + 3 ^ 40 * 7953264 * 2
def baseEnd_7953264 : Nat := 4083847204100276051723611

theorem tailTrace_7953264 : CollatzResearch.WordTrace tailWord_7953264 prefixEnd_7953264 4083847204100276051723611 := by
  unfold tailWord_7953264
  simp only [CollatzResearch.WordTrace]
  refine ⟨145039684529345156097889423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193386246039126874797185897 145039684529345156097889423)
  ·
    refine ⟨217559526794017734146834135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145039684529345156097889423 217559526794017734146834135)
    ·
      refine ⟨326339290191026601220251203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217559526794017734146834135 326339290191026601220251203)
      ·
        refine ⟨489508935286539901830376805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326339290191026601220251203 489508935286539901830376805)
        ·
          refine ⟨91782925366226231593195651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 489508935286539901830376805 91782925366226231593195651)
          ·
            refine ⟨137674388049339347389793477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91782925366226231593195651 137674388049339347389793477)
            ·
              refine ⟨25813947759251127635586277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137674388049339347389793477 25813947759251127635586277)
              ·
                refine ⟨4840115204859586431672427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25813947759251127635586277 4840115204859586431672427)
                ·
                  refine ⟨7260172807289379647508641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4840115204859586431672427 7260172807289379647508641)
                  ·
                    refine ⟨5445129605467034735631481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7260172807289379647508641 5445129605467034735631481)
                    ·
                      refine ⟨4083847204100276051723611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5445129605467034735631481 4083847204100276051723611)
                      ·
                        rfl

theorem cell23_7953264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 4, 1, 2, 2].length) (baseStart_7953264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7953264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7953264 prefixEnd_7953264 := by exact prefixLift 7953264
  have htrace : WordTrace (prefixWord ++ tailWord_7953264) baseStart_7953264 baseEnd_7953264 := by
    simpa [prefixWord, tailWord_7953264, baseEnd_7953264] using wordTrace_append hprefix tailTrace_7953264
  have hstable : (prefixWord ++ tailWord_7953264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7953264).length < 2 ^ (prefixWord ++ tailWord_7953264).sum := by decide
  have hdescent : baseEnd_7953264 < baseStart_7953264 := by decide
  rcases family_descends (prefixWord ++ tailWord_7953264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7953323 : List Nat := [1, 1, 1, 1, 2, 1, 1, 5, 1, 6, 3]
def baseStart_7953323 : Nat := 118140960795 + 7953323 * 2 ^ 59
def prefixEnd_7953323 : Nat := 4983230072969 + 3 ^ 40 * 7953323 * 2
def baseEnd_7953323 : Nat := 4083877499458891320885839

theorem tailTrace_7953323 : CollatzResearch.WordTrace tailWord_7953323 prefixEnd_7953323 4083877499458891320885839 := by
  unfold tailWord_7953323
  simp only [CollatzResearch.WordTrace]
  refine ⟨290081520965476565272176623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193387680643651043514784415 290081520965476565272176623)
  ·
    refine ⟨435122281448214847908264935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290081520965476565272176623 435122281448214847908264935)
    ·
      refine ⟨652683422172322271862397403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435122281448214847908264935 652683422172322271862397403)
      ·
        refine ⟨979025133258483407793596105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 652683422172322271862397403 979025133258483407793596105)
        ·
          refine ⟨734268849943862555845197079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 979025133258483407793596105 734268849943862555845197079)
          ·
            refine ⟨1101403274915793833767795619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 734268849943862555845197079 1101403274915793833767795619)
            ·
              refine ⟨1652104912373690750651693429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1101403274915793833767795619 1652104912373690750651693429)
              ·
                refine ⟨154884835535033507873596259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1652104912373690750651693429 154884835535033507873596259)
                ·
                  refine ⟨232327253302550261810394389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 154884835535033507873596259 232327253302550261810394389)
                  ·
                    refine ⟨10890339998557043522362237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 232327253302550261810394389 10890339998557043522362237)
                    ·
                      refine ⟨4083877499458891320885839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10890339998557043522362237 4083877499458891320885839)
                      ·
                        rfl

theorem cell23_7953323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 6, 3].length) (baseStart_7953323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7953323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7953323 prefixEnd_7953323 := by exact prefixLift 7953323
  have htrace : WordTrace (prefixWord ++ tailWord_7953323) baseStart_7953323 baseEnd_7953323 := by
    simpa [prefixWord, tailWord_7953323, baseEnd_7953323] using wordTrace_append hprefix tailTrace_7953323
  have hstable : (prefixWord ++ tailWord_7953323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7953323).length < 2 ^ (prefixWord ++ tailWord_7953323).sum := by decide
  have hdescent : baseEnd_7953323 < baseStart_7953323 := by decide
  rcases family_descends (prefixWord ++ tailWord_7953323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7953341 : List Nat := [1, 4, 1, 2, 4, 2, 1, 2, 1, 3, 2]
def baseStart_7953341 : Nat := 118140960795 + 7953341 * 2 ^ 59
def prefixEnd_7953341 : Nat := 4983230072969 + 3 ^ 40 * 7953341 * 2
def baseEnd_7953341 : Nat := 4083886742110672250460757

theorem tailTrace_7953341 : CollatzResearch.WordTrace tailWord_7953341 prefixEnd_7953341 4083886742110672250460757 := by
  unfold tailWord_7953341
  simp only [CollatzResearch.WordTrace]
  refine ⟨290082177479411354346331877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193388118319607569564221251 290082177479411354346331877)
  ·
    refine ⟨54390408277389628939937227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 290082177479411354346331877 54390408277389628939937227)
    ·
      refine ⟨81585612416084443409905841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54390408277389628939937227 81585612416084443409905841)
      ·
        refine ⟨61189209312063332557429381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81585612416084443409905841 61189209312063332557429381)
        ·
          refine ⟨11472976746011874854518009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61189209312063332557429381 11472976746011874854518009)
          ·
            refine ⟨8604732559508906140888507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11472976746011874854518009 8604732559508906140888507)
            ·
              refine ⟨12907098839263359211332761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8604732559508906140888507 12907098839263359211332761)
              ·
                refine ⟨9680324129447519408499571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12907098839263359211332761 9680324129447519408499571)
                ·
                  refine ⟨14520486194171279112749357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9680324129447519408499571 14520486194171279112749357)
                  ·
                    refine ⟨5445182322814229667281009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14520486194171279112749357 5445182322814229667281009)
                    ·
                      refine ⟨4083886742110672250460757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5445182322814229667281009 4083886742110672250460757)
                      ·
                        rfl

theorem cell23_7953341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 2, 1, 3, 2].length) (baseStart_7953341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7953341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7953341 prefixEnd_7953341 := by exact prefixLift 7953341
  have htrace : WordTrace (prefixWord ++ tailWord_7953341) baseStart_7953341 baseEnd_7953341 := by
    simpa [prefixWord, tailWord_7953341, baseEnd_7953341] using wordTrace_append hprefix tailTrace_7953341
  have hstable : (prefixWord ++ tailWord_7953341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7953341).length < 2 ^ (prefixWord ++ tailWord_7953341).sum := by decide
  have hdescent : baseEnd_7953341 < baseStart_7953341 := by decide
  rcases family_descends (prefixWord ++ tailWord_7953341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7953360 : List Nat := [2, 1, 1, 1, 1, 2, 3, 7, 5]
def baseStart_7953360 : Nat := 118140960795 + 7953360 * 2 ^ 59
def prefixEnd_7953360 : Nat := 4983230072969 + 3 ^ 40 * 7953360 * 2
def baseEnd_7953360 : Nat := 453766277582567519569241

theorem tailTrace_7953360 : CollatzResearch.WordTrace tailWord_7953360 prefixEnd_7953360 453766277582567519569241 := by
  unfold tailWord_7953360
  simp only [CollatzResearch.WordTrace]
  refine ⟨145041435233171260295636767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193388580310895013727515689 145041435233171260295636767)
  ·
    refine ⟨217562152849756890443455151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145041435233171260295636767 217562152849756890443455151)
    ·
      refine ⟨326343229274635335665182727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217562152849756890443455151 326343229274635335665182727)
      ·
        refine ⟨489514843911953003497774091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326343229274635335665182727 489514843911953003497774091)
        ·
          refine ⟨734272265867929505246661137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 489514843911953003497774091 734272265867929505246661137)
          ·
            refine ⟨550704199400947128934995853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 734272265867929505246661137 550704199400947128934995853)
            ·
              refine ⟨206514074775355173350623445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 550704199400947128934995853 206514074775355173350623445)
              ·
                refine ⟨4840173627547386875405237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 206514074775355173350623445 4840173627547386875405237)
                ·
                  refine ⟨453766277582567519569241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4840173627547386875405237 453766277582567519569241)
                  ·
                    rfl

theorem cell23_7953360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 7, 5].length) (baseStart_7953360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7953360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7953360 prefixEnd_7953360 := by exact prefixLift 7953360
  have htrace : WordTrace (prefixWord ++ tailWord_7953360) baseStart_7953360 baseEnd_7953360 := by
    simpa [prefixWord, tailWord_7953360, baseEnd_7953360] using wordTrace_append hprefix tailTrace_7953360
  have hstable : (prefixWord ++ tailWord_7953360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7953360).length < 2 ^ (prefixWord ++ tailWord_7953360).sum := by decide
  have hdescent : baseEnd_7953360 < baseStart_7953360 := by decide
  rcases family_descends (prefixWord ++ tailWord_7953360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7953444 : List Nat := [2, 3, 1, 4, 1, 1, 2, 1, 2, 4, 2]
def baseStart_7953444 : Nat := 118140960795 + 7953444 * 2 ^ 59
def prefixEnd_7953444 : Nat := 4983230072969 + 3 ^ 40 * 7953444 * 2
def baseEnd_7953444 : Nat := 4083939630618085347472783

theorem tailTrace_7953444 : CollatzResearch.WordTrace tailWord_7953444 prefixEnd_7953444 4083939630618085347472783 := by
  unfold tailWord_7953444
  simp only [CollatzResearch.WordTrace]
  refine ⟨145042967099019101468665693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193390622798692135291554257 145042967099019101468665693)
  ·
    refine ⟨54391112662132163050749635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145042967099019101468665693 54391112662132163050749635)
    ·
      refine ⟨81586668993198244576124453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54391112662132163050749635 81586668993198244576124453)
      ·
        refine ⟨15297500436224670858023335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81586668993198244576124453 15297500436224670858023335)
        ·
          refine ⟨22946250654337006287035003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15297500436224670858023335 22946250654337006287035003)
          ·
            refine ⟨34419375981505509430552505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22946250654337006287035003 34419375981505509430552505)
            ·
              refine ⟨25814531986129132072914379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34419375981505509430552505 25814531986129132072914379)
              ·
                refine ⟨38721797979193698109371569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25814531986129132072914379 38721797979193698109371569)
                ·
                  refine ⟨29041348484395273582028677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38721797979193698109371569 29041348484395273582028677)
                  ·
                    refine ⟨5445252840824113796630377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29041348484395273582028677 5445252840824113796630377)
                    ·
                      refine ⟨4083939630618085347472783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5445252840824113796630377 4083939630618085347472783)
                      ·
                        rfl

theorem cell23_7953444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_7953444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7953444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7953444 prefixEnd_7953444 := by exact prefixLift 7953444
  have htrace : WordTrace (prefixWord ++ tailWord_7953444) baseStart_7953444 baseEnd_7953444 := by
    simpa [prefixWord, tailWord_7953444, baseEnd_7953444] using wordTrace_append hprefix tailTrace_7953444
  have hstable : (prefixWord ++ tailWord_7953444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7953444).length < 2 ^ (prefixWord ++ tailWord_7953444).sum := by decide
  have hdescent : baseEnd_7953444 < baseStart_7953444 := by decide
  rcases family_descends (prefixWord ++ tailWord_7953444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7953477 : List Nat := [1, 3, 1, 1, 1, 3, 2, 2, 5, 1, 3]
def baseStart_7953477 : Nat := 118140960795 + 7953477 * 2 ^ 59
def prefixEnd_7953477 : Nat := 4983230072969 + 3 ^ 40 * 7953477 * 2
def baseEnd_7953477 : Nat := 4083956575479683718360131

theorem tailTrace_7953477 : CollatzResearch.WordTrace tailWord_7953477 prefixEnd_7953477 4083956575479683718360131 := by
  unfold tailWord_7953477
  simp only [CollatzResearch.WordTrace]
  refine ⟨290087137806918649573282685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193391425204612433048855123 290087137806918649573282685)
  ·
    refine ⟨108782676677594493589981007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290087137806918649573282685 108782676677594493589981007)
    ·
      refine ⟨163174015016391740384971511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108782676677594493589981007 163174015016391740384971511)
      ·
        refine ⟨244761022524587610577457267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163174015016391740384971511 244761022524587610577457267)
        ·
          refine ⟨367141533786881415866185901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244761022524587610577457267 367141533786881415866185901)
          ·
            refine ⟨137678075170080530949819713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 367141533786881415866185901 137678075170080530949819713)
            ·
              refine ⟨103258556377560398212364785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137678075170080530949819713 103258556377560398212364785)
              ·
                refine ⟨77443917283170298659273589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103258556377560398212364785 77443917283170298659273589)
                ·
                  refine ⟨7260367245297215499306899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77443917283170298659273589 7260367245297215499306899)
                  ·
                    refine ⟨10890550867945823248960349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7260367245297215499306899 10890550867945823248960349)
                    ·
                      refine ⟨4083956575479683718360131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10890550867945823248960349 4083956575479683718360131)
                      ·
                        rfl

theorem cell23_7953477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 5, 1, 3].length) (baseStart_7953477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7953477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7953477 prefixEnd_7953477 := by exact prefixLift 7953477
  have htrace : WordTrace (prefixWord ++ tailWord_7953477) baseStart_7953477 baseEnd_7953477 := by
    simpa [prefixWord, tailWord_7953477, baseEnd_7953477] using wordTrace_append hprefix tailTrace_7953477
  have hstable : (prefixWord ++ tailWord_7953477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7953477).length < 2 ^ (prefixWord ++ tailWord_7953477).sum := by decide
  have hdescent : baseEnd_7953477 < baseStart_7953477 := by decide
  rcases family_descends (prefixWord ++ tailWord_7953477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7953514 : List Nat := [3, 1, 3, 2, 2, 1, 3, 2, 1, 5]
def baseStart_7953514 : Nat := 118140960795 + 7953514 * 2 ^ 59
def prefixEnd_7953514 : Nat := 4983230072969 + 3 ^ 40 * 7953514 * 2
def baseEnd_7953514 : Nat := 1361325191421300024532487

theorem tailTrace_7953514 : CollatzResearch.WordTrace tailWord_7953514 prefixEnd_7953514 1361325191421300024532487 := by
  unfold tailWord_7953514
  simp only [CollatzResearch.WordTrace]
  refine ⟨72522121826946151223094899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193392324871856403261586397 72522121826946151223094899)
  ·
    refine ⟨108783182740419226834642349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72522121826946151223094899 108783182740419226834642349)
    ·
      refine ⟨40793693527657210062990881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108783182740419226834642349 40793693527657210062990881)
      ·
        refine ⟨30595270145742907547243161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40793693527657210062990881 30595270145742907547243161)
        ·
          refine ⟨22946452609307180660432371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30595270145742907547243161 22946452609307180660432371)
          ·
            refine ⟨34419678913960770990648557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22946452609307180660432371 34419678913960770990648557)
            ·
              refine ⟨12907379592735289121493209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34419678913960770990648557 12907379592735289121493209)
              ·
                refine ⟨9680534694551466841119907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12907379592735289121493209 9680534694551466841119907)
                ·
                  refine ⟨14520802041827200261679861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9680534694551466841119907 14520802041827200261679861)
                  ·
                    refine ⟨1361325191421300024532487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14520802041827200261679861 1361325191421300024532487)
                    ·
                      rfl

theorem cell23_7953514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 2, 1, 5].length) (baseStart_7953514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7953514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7953514 prefixEnd_7953514 := by exact prefixLift 7953514
  have htrace : WordTrace (prefixWord ++ tailWord_7953514) baseStart_7953514 baseEnd_7953514 := by
    simpa [prefixWord, tailWord_7953514, baseEnd_7953514] using wordTrace_append hprefix tailTrace_7953514
  have hstable : (prefixWord ++ tailWord_7953514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7953514).length < 2 ^ (prefixWord ++ tailWord_7953514).sum := by decide
  have hdescent : baseEnd_7953514 < baseStart_7953514 := by decide
  rcases family_descends (prefixWord ++ tailWord_7953514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7953540 : List Nat := [2, 3, 2, 1, 2, 13]
def baseStart_7953540 : Nat := 118140960795 + 7953540 * 2 ^ 59
def prefixEnd_7953540 : Nat := 4983230072969 + 3 ^ 40 * 7953540 * 2
def baseEnd_7953540 : Nat := 16806538785024349678487

theorem tailTrace_7953540 : CollatzResearch.WordTrace tailWord_7953540 prefixEnd_7953540 16806538785024349678487 := by
  unfold tailWord_7953540
  simp only [CollatzResearch.WordTrace]
  refine ⟨145044717802845205666413037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193392957070460274221884049 145044717802845205666413037)
  ·
    refine ⟨54391769176066952124904889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 145044717802845205666413037 54391769176066952124904889)
    ·
      refine ⟨40793826882050214093678667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54391769176066952124904889 40793826882050214093678667)
      ·
        refine ⟨61190740323075321140518001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40793826882050214093678667 61190740323075321140518001)
        ·
          refine ⟨45893055242306490855388501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61190740323075321140518001 45893055242306490855388501)
          ·
            refine ⟨16806538785024349678487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 45893055242306490855388501 16806538785024349678487)
            ·
              rfl

theorem cell23_7953540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 13].length) (baseStart_7953540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7953540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7953540 prefixEnd_7953540 := by exact prefixLift 7953540
  have htrace : WordTrace (prefixWord ++ tailWord_7953540) baseStart_7953540 baseEnd_7953540 := by
    simpa [prefixWord, tailWord_7953540, baseEnd_7953540] using wordTrace_append hprefix tailTrace_7953540
  have hstable : (prefixWord ++ tailWord_7953540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7953540).length < 2 ^ (prefixWord ++ tailWord_7953540).sum := by decide
  have hdescent : baseEnd_7953540 < baseStart_7953540 := by decide
  rcases family_descends (prefixWord ++ tailWord_7953540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7953554 : List Nat := [3, 2, 3, 1, 1, 2, 1, 2, 3, 2, 3]
def baseStart_7953554 : Nat := 118140960795 + 7953554 * 2 ^ 59
def prefixEnd_7953554 : Nat := 4983230072969 + 3 ^ 40 * 7953554 * 2
def baseEnd_7953554 : Nat := 4083996113490079917097277

theorem tailTrace_7953554 : CollatzResearch.WordTrace tailWord_7953554 prefixEnd_7953554 4083996113490079917097277 := by
  unfold tailWord_7953554
  simp only [CollatzResearch.WordTrace]
  refine ⟨72522486556909922930958929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193393297485093127815890477 72522486556909922930958929)
  ·
    refine ⟨54391864917682442198219197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72522486556909922930958929 54391864917682442198219197)
    ·
      refine ⟨20396949344130915824332199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54391864917682442198219197 20396949344130915824332199)
      ·
        refine ⟨30595424016196373736498299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20396949344130915824332199 30595424016196373736498299)
        ·
          refine ⟨45893136024294560604747449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30595424016196373736498299 45893136024294560604747449)
          ·
            refine ⟨34419852018220920453560587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45893136024294560604747449 34419852018220920453560587)
            ·
              refine ⟨51629778027331380680340881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34419852018220920453560587 51629778027331380680340881)
              ·
                refine ⟨38722333520498535510255661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51629778027331380680340881 38722333520498535510255661)
                ·
                  refine ⟨14520875070186950816345873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38722333520498535510255661 14520875070186950816345873)
                  ·
                    refine ⟨10890656302640213112259405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14520875070186950816345873 10890656302640213112259405)
                    ·
                      refine ⟨4083996113490079917097277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10890656302640213112259405 4083996113490079917097277)
                      ·
                        rfl

theorem cell23_7953554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_7953554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7953554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7953554 prefixEnd_7953554 := by exact prefixLift 7953554
  have htrace : WordTrace (prefixWord ++ tailWord_7953554) baseStart_7953554 baseEnd_7953554 := by
    simpa [prefixWord, tailWord_7953554, baseEnd_7953554] using wordTrace_append hprefix tailTrace_7953554
  have hstable : (prefixWord ++ tailWord_7953554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7953554).length < 2 ^ (prefixWord ++ tailWord_7953554).sum := by decide
  have hdescent : baseEnd_7953554 < baseStart_7953554 := by decide
  rcases family_descends (prefixWord ++ tailWord_7953554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7953564 : List Nat := [2, 2, 3, 2, 1, 3, 2, 1, 1, 2, 4]
def baseStart_7953564 : Nat := 118140960795 + 7953564 * 2 ^ 59
def prefixEnd_7953564 : Nat := 4983230072969 + 3 ^ 40 * 7953564 * 2
def baseEnd_7953564 : Nat := 4084001248296624877972231

theorem tailTrace_7953564 : CollatzResearch.WordTrace tailWord_7953564 prefixEnd_7953564 4084001248296624877972231 := by
  unfold tailWord_7953564
  simp only [CollatzResearch.WordTrace]
  refine ⟨145045155478801731715849873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193393540638402308954466497 145045155478801731715849873)
  ·
    refine ⟨108783866609101298786887405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 145045155478801731715849873 108783866609101298786887405)
    ·
      refine ⟨40793949978412987045082777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108783866609101298786887405 40793949978412987045082777)
      ·
        refine ⟨30595462483809740283812083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40793949978412987045082777 30595462483809740283812083)
        ·
          refine ⟨45893193725714610425718125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30595462483809740283812083 45893193725714610425718125)
          ·
            refine ⟨17209947647142978909644297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45893193725714610425718125 17209947647142978909644297)
            ·
              refine ⟨12907460735357234182233223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17209947647142978909644297 12907460735357234182233223)
              ·
                refine ⟨19361191103035851273349835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12907460735357234182233223 19361191103035851273349835)
                ·
                  refine ⟨29041786654553776910024753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19361191103035851273349835 29041786654553776910024753)
                  ·
                    refine ⟨21781339990915332682518565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29041786654553776910024753 21781339990915332682518565)
                    ·
                      refine ⟨4084001248296624877972231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21781339990915332682518565 4084001248296624877972231)
                      ·
                        rfl

theorem cell23_7953564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_7953564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7953564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7953564 prefixEnd_7953564 := by exact prefixLift 7953564
  have htrace : WordTrace (prefixWord ++ tailWord_7953564) baseStart_7953564 baseEnd_7953564 := by
    simpa [prefixWord, tailWord_7953564, baseEnd_7953564] using wordTrace_append hprefix tailTrace_7953564
  have hstable : (prefixWord ++ tailWord_7953564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7953564).length < 2 ^ (prefixWord ++ tailWord_7953564).sum := by decide
  have hdescent : baseEnd_7953564 < baseStart_7953564 := by decide
  rcases family_descends (prefixWord ++ tailWord_7953564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7953577 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 4, 7, 2]
def baseStart_7953577 : Nat := 118140960795 + 7953577 * 2 ^ 59
def prefixEnd_7953577 : Nat := 4983230072969 + 3 ^ 40 * 7953577 * 2
def baseEnd_7953577 : Nat := 4084007923545133327109671

theorem tailTrace_7953577 : CollatzResearch.WordTrace tailWord_7953577 prefixEnd_7953577 4084007923545133327109671 := by
  unfold tailWord_7953577
  simp only [CollatzResearch.WordTrace]
  refine ⟨290090785106556366651922985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193393856737704244434615323 290090785106556366651922985)
  ·
    refine ⟨217568088829917274988942239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290090785106556366651922985 217568088829917274988942239)
    ·
      refine ⟨326352133244875912483413359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217568088829917274988942239 326352133244875912483413359)
      ·
        refine ⟨489528199867313868725120039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326352133244875912483413359 489528199867313868725120039)
        ·
          refine ⟨734292299800970803087680059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 489528199867313868725120039 734292299800970803087680059)
          ·
            refine ⟨1101438449701456204631520089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 734292299800970803087680059 1101438449701456204631520089)
            ·
              refine ⟨826078837276092153473640067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1101438449701456204631520089 826078837276092153473640067)
              ·
                refine ⟨1239118255914138230210460101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 826078837276092153473640067 1239118255914138230210460101)
                ·
                  refine ⟨232334672983900918164461269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1239118255914138230210460101 232334672983900918164461269)
                  ·
                    refine ⟨5445343898060177769479561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 232334672983900918164461269 5445343898060177769479561)
                    ·
                      refine ⟨4084007923545133327109671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5445343898060177769479561 4084007923545133327109671)
                      ·
                        rfl

theorem cell23_7953577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 7, 2].length) (baseStart_7953577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7953577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7953577 prefixEnd_7953577 := by exact prefixLift 7953577
  have htrace : WordTrace (prefixWord ++ tailWord_7953577) baseStart_7953577 baseEnd_7953577 := by
    simpa [prefixWord, tailWord_7953577, baseEnd_7953577] using wordTrace_append hprefix tailTrace_7953577
  have hstable : (prefixWord ++ tailWord_7953577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7953577).length < 2 ^ (prefixWord ++ tailWord_7953577).sum := by decide
  have hdescent : baseEnd_7953577 < baseStart_7953577 := by decide
  rcases family_descends (prefixWord ++ tailWord_7953577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7953585 : List Nat := [1, 2, 2, 5, 1, 2, 2, 3, 1, 2, 2]
def baseStart_7953585 : Nat := 118140960795 + 7953585 * 2 ^ 59
def prefixEnd_7953585 : Nat := 4983230072969 + 3 ^ 40 * 7953585 * 2
def baseEnd_7953585 : Nat := 4084012031390369295809635

theorem tailTrace_7953585 : CollatzResearch.WordTrace tailWord_7953585 prefixEnd_7953585 4084012031390369295809635 := by
  unfold tailWord_7953585
  simp only [CollatzResearch.WordTrace]
  refine ⟨290091076890527384018214209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193394051260351589345476139 290091076890527384018214209)
  ·
    refine ⟨217568307667895538013660657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290091076890527384018214209 217568307667895538013660657)
    ·
      refine ⟨163176230750921653510245493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 217568307667895538013660657 163176230750921653510245493)
      ·
        refine ⟨15297771632898905016585515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 163176230750921653510245493 15297771632898905016585515)
        ·
          refine ⟨22946657449348357524878273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15297771632898905016585515 22946657449348357524878273)
          ·
            refine ⟨17209993087011268143658705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22946657449348357524878273 17209993087011268143658705)
            ·
              refine ⟨12907494815258451107744029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17209993087011268143658705 12907494815258451107744029)
              ·
                refine ⟨4840310555721919165404011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12907494815258451107744029 4840310555721919165404011)
                ·
                  refine ⟨7260465833582878748106017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4840310555721919165404011 7260465833582878748106017)
                  ·
                    refine ⟨5445349375187159061079513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7260465833582878748106017 5445349375187159061079513)
                    ·
                      refine ⟨4084012031390369295809635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5445349375187159061079513 4084012031390369295809635)
                      ·
                        rfl

theorem cell23_7953585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_7953585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7953585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7953585 prefixEnd_7953585 := by exact prefixLift 7953585
  have htrace : WordTrace (prefixWord ++ tailWord_7953585) baseStart_7953585 baseEnd_7953585 := by
    simpa [prefixWord, tailWord_7953585, baseEnd_7953585] using wordTrace_append hprefix tailTrace_7953585
  have hstable : (prefixWord ++ tailWord_7953585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7953585).length < 2 ^ (prefixWord ++ tailWord_7953585).sum := by decide
  have hdescent : baseEnd_7953585 < baseStart_7953585 := by decide
  rcases family_descends (prefixWord ++ tailWord_7953585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7953602 : List Nat := [3, 5, 1, 1, 2, 1, 2, 1, 3, 2, 2]
def baseStart_7953602 : Nat := 118140960795 + 7953602 * 2 ^ 59
def prefixEnd_7953602 : Nat := 4983230072969 + 3 ^ 40 * 7953602 * 2
def baseEnd_7953602 : Nat := 4084020760561495729297057

theorem tailTrace_7953602 : CollatzResearch.WordTrace tailWord_7953602 prefixEnd_7953602 4084020760561495729297057 := by
  unfold tailWord_7953602
  simp only [CollatzResearch.WordTrace]
  refine ⟨72522924232866448980395765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193394464620977197281055373 72522924232866448980395765)
  ·
    refine ⟨6799024146831229591912103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72522924232866448980395765 6799024146831229591912103)
    ·
      refine ⟨10198536220246844387868155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6799024146831229591912103 10198536220246844387868155)
      ·
        refine ⟨15297804330370266581802233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10198536220246844387868155 15297804330370266581802233)
        ·
          refine ⟨11473353247777699936351675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15297804330370266581802233 11473353247777699936351675)
          ·
            refine ⟨17210029871666549904527513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11473353247777699936351675 17210029871666549904527513)
            ·
              refine ⟨12907522403749912428395635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17210029871666549904527513 12907522403749912428395635)
              ·
                refine ⟨19361283605624868642593453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12907522403749912428395635 19361283605624868642593453)
                ·
                  refine ⟨7260481352109325740972545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19361283605624868642593453 7260481352109325740972545)
                  ·
                    refine ⟨5445361014081994305729409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7260481352109325740972545 5445361014081994305729409)
                    ·
                      refine ⟨4084020760561495729297057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5445361014081994305729409 4084020760561495729297057)
                      ·
                        rfl

theorem cell23_7953602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_7953602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7953602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7953602 prefixEnd_7953602 := by exact prefixLift 7953602
  have htrace : WordTrace (prefixWord ++ tailWord_7953602) baseStart_7953602 baseEnd_7953602 := by
    simpa [prefixWord, tailWord_7953602, baseEnd_7953602] using wordTrace_append hprefix tailTrace_7953602
  have hstable : (prefixWord ++ tailWord_7953602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7953602).length < 2 ^ (prefixWord ++ tailWord_7953602).sum := by decide
  have hdescent : baseEnd_7953602 < baseStart_7953602 := by decide
  rcases family_descends (prefixWord ++ tailWord_7953602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7953618 : List Nat := [3, 2, 2, 2, 1, 1, 5, 1, 2, 1, 3]
def baseStart_7953618 : Nat := 118140960795 + 7953618 * 2 ^ 59
def prefixEnd_7953618 : Nat := 4983230072969 + 3 ^ 40 * 7953618 * 2
def baseEnd_7953618 : Nat := 4084028976251967666696983

theorem tailTrace_7953618 : CollatzResearch.WordTrace tailWord_7953618 prefixEnd_7953618 4084028976251967666696983 := by
  unfold tailWord_7953618
  simp only [CollatzResearch.WordTrace]
  refine ⟨72523070124851957663541377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 193394853666271887102777005 72523070124851957663541377)
  ·
    refine ⟨54392302593638968247656033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72523070124851957663541377 54392302593638968247656033)
    ·
      refine ⟨40794226945229226185742025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54392302593638968247656033 40794226945229226185742025)
      ·
        refine ⟨30595670208921919639306519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40794226945229226185742025 30595670208921919639306519)
        ·
          refine ⟨45893505313382879458959779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30595670208921919639306519 45893505313382879458959779)
          ·
            refine ⟨68840257970074319188439669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45893505313382879458959779 68840257970074319188439669)
            ·
              refine ⟨6453774184694467423916219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68840257970074319188439669 6453774184694467423916219)
              ·
                refine ⟨9680661277041701135874329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6453774184694467423916219 9680661277041701135874329)
                ·
                  refine ⟨7260495957781275851905747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9680661277041701135874329 7260495957781275851905747)
                  ·
                    refine ⟨10890743936671913777858621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7260495957781275851905747 10890743936671913777858621)
                    ·
                      refine ⟨4084028976251967666696983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10890743936671913777858621 4084028976251967666696983)
                      ·
                        rfl

theorem cell23_7953618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 5, 1, 2, 1, 3].length) (baseStart_7953618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7953618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7953618 prefixEnd_7953618 := by exact prefixLift 7953618
  have htrace : WordTrace (prefixWord ++ tailWord_7953618) baseStart_7953618 baseEnd_7953618 := by
    simpa [prefixWord, tailWord_7953618, baseEnd_7953618] using wordTrace_append hprefix tailTrace_7953618
  have hstable : (prefixWord ++ tailWord_7953618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7953618).length < 2 ^ (prefixWord ++ tailWord_7953618).sum := by decide
  have hdescent : baseEnd_7953618 < baseStart_7953618 := by decide
  rcases family_descends (prefixWord ++ tailWord_7953618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7953675 : List Nat := [1, 1, 1, 1, 5, 5, 2, 1, 2, 2, 2]
def baseStart_7953675 : Nat := 118140960795 + 7953675 * 2 ^ 59
def prefixEnd_7953675 : Nat := 4983230072969 + 3 ^ 40 * 7953675 * 2
def baseEnd_7953675 : Nat := 4084058244649273943684221

theorem tailTrace_7953675 : CollatzResearch.WordTrace tailWord_7953675 prefixEnd_7953675 4084058244649273943684221 := by
  unfold tailWord_7953675
  simp only [CollatzResearch.WordTrace]
  refine ⟨290094359460201329388990479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193396239640134219592660319 290094359460201329388990479)
  ·
    refine ⟨435141539190301994083485719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290094359460201329388990479 435141539190301994083485719)
    ·
      refine ⟨652712308785452991125228579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435141539190301994083485719 652712308785452991125228579)
      ·
        refine ⟨979068463178179486687842869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 652712308785452991125228579 979068463178179486687842869)
        ·
          refine ⟨91787668422954326876985269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 979068463178179486687842869 91787668422954326876985269)
          ·
            refine ⟨8605093914651968144717369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 91787668422954326876985269 8605093914651968144717369)
            ·
              refine ⟨6453820435988976108538027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8605093914651968144717369 6453820435988976108538027)
              ·
                refine ⟨9680730653983464162807041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6453820435988976108538027 9680730653983464162807041)
                ·
                  refine ⟨7260547990487598122105281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9680730653983464162807041 7260547990487598122105281)
                  ·
                    refine ⟨5445410992865698591578961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7260547990487598122105281 5445410992865698591578961)
                    ·
                      refine ⟨4084058244649273943684221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5445410992865698591578961 4084058244649273943684221)
                      ·
                        rfl

theorem cell23_7953675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 2, 1, 2, 2, 2].length) (baseStart_7953675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7953675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7953675 prefixEnd_7953675 := by exact prefixLift 7953675
  have htrace : WordTrace (prefixWord ++ tailWord_7953675) baseStart_7953675 baseEnd_7953675 := by
    simpa [prefixWord, tailWord_7953675, baseEnd_7953675] using wordTrace_append hprefix tailTrace_7953675
  have hstable : (prefixWord ++ tailWord_7953675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7953675).length < 2 ^ (prefixWord ++ tailWord_7953675).sum := by decide
  have hdescent : baseEnd_7953675 < baseStart_7953675 := by decide
  rcases family_descends (prefixWord ++ tailWord_7953675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7953687 : List Nat := [1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 7]
def baseStart_7953687 : Nat := 118140960795 + 7953687 * 2 ^ 59
def prefixEnd_7953687 : Nat := 4983230072969 + 3 ^ 40 * 7953687 * 2
def baseEnd_7953687 : Nat := 4084064406417127896734165

theorem tailTrace_7953687 : CollatzResearch.WordTrace tailWord_7953687 prefixEnd_7953687 4084064406417127896734165 := by
  unfold tailWord_7953687
  simp only [CollatzResearch.WordTrace]
  refine ⟨290094797136157855438427315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193396531424105236958951543 290094797136157855438427315)
  ·
    refine ⟨435142195704236783157640973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290094797136157855438427315 435142195704236783157640973)
    ·
      refine ⟨163178323389088793684115365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 435142195704236783157640973 163178323389088793684115365)
      ·
        refine ⟨30595935635454148815771631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163178323389088793684115365 30595935635454148815771631)
        ·
          refine ⟨45893903453181223223657447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30595935635454148815771631 45893903453181223223657447)
          ·
            refine ⟨68840855179771834835486171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45893903453181223223657447 68840855179771834835486171)
            ·
              refine ⟨103261282769657752253229257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68840855179771834835486171 103261282769657752253229257)
              ·
                refine ⟨77445962077243314189921943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103261282769657752253229257 77445962077243314189921943)
                ·
                  refine ⟨116168943115864971284882915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77445962077243314189921943 116168943115864971284882915)
                  ·
                    refine ⟨174253414673797456927324373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 116168943115864971284882915 174253414673797456927324373)
                    ·
                      refine ⟨4084064406417127896734165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 174253414673797456927324373 4084064406417127896734165)
                      ·
                        rfl

theorem cell23_7953687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_7953687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7953687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7953687 prefixEnd_7953687 := by exact prefixLift 7953687
  have htrace : WordTrace (prefixWord ++ tailWord_7953687) baseStart_7953687 baseEnd_7953687 := by
    simpa [prefixWord, tailWord_7953687, baseEnd_7953687] using wordTrace_append hprefix tailTrace_7953687
  have hstable : (prefixWord ++ tailWord_7953687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7953687).length < 2 ^ (prefixWord ++ tailWord_7953687).sum := by decide
  have hdescent : baseEnd_7953687 < baseStart_7953687 := by decide
  rcases family_descends (prefixWord ++ tailWord_7953687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7953704 : List Nat := [2, 1, 5, 1, 2, 1, 1, 2, 1, 2, 5]
def baseStart_7953704 : Nat := 118140960795 + 7953704 * 2 ^ 59
def prefixEnd_7953704 : Nat := 4983230072969 + 3 ^ 40 * 7953704 * 2
def baseEnd_7953704 : Nat := 4084073135588254330221587

theorem tailTrace_7953704 : CollatzResearch.WordTrace tailWord_7953704 prefixEnd_7953704 4084073135588254330221587 := by
  unfold tailWord_7953704
  simp only [CollatzResearch.WordTrace]
  refine ⟨145047708588548133670898083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193396944784730844894530777 145047708588548133670898083)
  ·
    refine ⟨217571562882822200506347125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 145047708588548133670898083 217571562882822200506347125)
    ·
      refine ⟨20397334020264581297470043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 217571562882822200506347125 20397334020264581297470043)
      ·
        refine ⟨30596001030396871946205065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20397334020264581297470043 30596001030396871946205065)
        ·
          refine ⟨22947000772797653959653799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30596001030396871946205065 22947000772797653959653799)
          ·
            refine ⟨34420501159196480939480699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22947000772797653959653799 34420501159196480939480699)
            ·
              refine ⟨51630751738794721409221049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34420501159196480939480699 51630751738794721409221049)
              ·
                refine ⟨38723063804096041056915787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51630751738794721409221049 38723063804096041056915787)
                ·
                  refine ⟨58084595706144061585373681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38723063804096041056915787 58084595706144061585373681)
                  ·
                    refine ⟨43563446779608046189030261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58084595706144061585373681 43563446779608046189030261)
                    ·
                      refine ⟨4084073135588254330221587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43563446779608046189030261 4084073135588254330221587)
                      ·
                        rfl

theorem cell23_7953704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_7953704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7953704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7953704 prefixEnd_7953704 := by exact prefixLift 7953704
  have htrace : WordTrace (prefixWord ++ tailWord_7953704) baseStart_7953704 baseEnd_7953704 := by
    simpa [prefixWord, tailWord_7953704, baseEnd_7953704] using wordTrace_append hprefix tailTrace_7953704
  have hstable : (prefixWord ++ tailWord_7953704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7953704).length < 2 ^ (prefixWord ++ tailWord_7953704).sum := by decide
  have hdescent : baseEnd_7953704 < baseStart_7953704 := by decide
  rcases family_descends (prefixWord ++ tailWord_7953704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7953751 : List Nat := [1, 1, 3, 2, 3, 2, 3, 1, 2, 2, 3]
def baseStart_7953751 : Nat := 118140960795 + 7953751 * 2 ^ 59
def prefixEnd_7953751 : Nat := 4983230072969 + 3 ^ 40 * 7953751 * 2
def baseEnd_7953751 : Nat := 4084097269179015646333871

theorem tailTrace_7953751 : CollatzResearch.WordTrace tailWord_7953751 prefixEnd_7953751 4084097269179015646333871 := by
  unfold tailWord_7953751
  simp only [CollatzResearch.WordTrace]
  refine ⟨290097131407925994368757107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193398087605283996245838071 290097131407925994368757107)
  ·
    refine ⟨435145697111888991553135661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290097131407925994368757107 435145697111888991553135661)
    ·
      refine ⟨163179636416958371832425873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 435145697111888991553135661 163179636416958371832425873)
      ·
        refine ⟨122384727312718778874319405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 163179636416958371832425873 122384727312718778874319405)
        ·
          refine ⟨45894272742269542077869777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122384727312718778874319405 45894272742269542077869777)
          ·
            refine ⟨34420704556702156558402333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45894272742269542077869777 34420704556702156558402333)
            ·
              refine ⟨12907764208763308709400875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34420704556702156558402333 12907764208763308709400875)
              ·
                refine ⟨19361646313144963064101313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12907764208763308709400875 19361646313144963064101313)
                ·
                  refine ⟨14521234734858722298075985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19361646313144963064101313 14521234734858722298075985)
                  ·
                    refine ⟨10890926051144041723556989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14521234734858722298075985 10890926051144041723556989)
                    ·
                      refine ⟨4084097269179015646333871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10890926051144041723556989 4084097269179015646333871)
                      ·
                        rfl

theorem cell23_7953751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 1, 2, 2, 3].length) (baseStart_7953751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7953751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7953751 prefixEnd_7953751 := by exact prefixLift 7953751
  have htrace : WordTrace (prefixWord ++ tailWord_7953751) baseStart_7953751 baseEnd_7953751 := by
    simpa [prefixWord, tailWord_7953751, baseEnd_7953751] using wordTrace_append hprefix tailTrace_7953751
  have hstable : (prefixWord ++ tailWord_7953751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7953751).length < 2 ^ (prefixWord ++ tailWord_7953751).sum := by decide
  have hdescent : baseEnd_7953751 < baseStart_7953751 := by decide
  rcases family_descends (prefixWord ++ tailWord_7953751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7953831 : List Nat := [1, 1, 6, 1, 1, 1, 1, 3, 4, 4]
def baseStart_7953831 : Nat := 118140960795 + 7953831 * 2 ^ 59
def prefixEnd_7953831 : Nat := 4983230072969 + 3 ^ 40 * 7953831 * 2
def baseEnd_7953831 : Nat := 1361379449210458444444501

theorem tailTrace_7953831 : CollatzResearch.WordTrace tailWord_7953831 prefixEnd_7953831 1361379449210458444444501 := by
  unfold tailWord_7953831
  simp only [CollatzResearch.WordTrace]
  refine ⟨290100049247636168031669347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193400032831757445354446231 290100049247636168031669347)
  ·
    refine ⟨435150073871454252047504021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290100049247636168031669347 435150073871454252047504021)
    ·
      refine ⟨20397659712724418064726751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 435150073871454252047504021 20397659712724418064726751)
      ·
        refine ⟨30596489569086627097090127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20397659712724418064726751 30596489569086627097090127)
        ·
          refine ⟨45894734353629940645635191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30596489569086627097090127 45894734353629940645635191)
          ·
            refine ⟨68842101530444910968452787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45894734353629940645635191 68842101530444910968452787)
            ·
              refine ⟨103263152295667366452679181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68842101530444910968452787 103263152295667366452679181)
              ·
                refine ⟨38723682110875262419754693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103263152295667366452679181 38723682110875262419754693)
                ·
                  refine ⟨7260690395789111703704005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38723682110875262419754693 7260690395789111703704005)
                  ·
                    refine ⟨1361379449210458444444501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7260690395789111703704005 1361379449210458444444501)
                    ·
                      rfl

theorem cell23_7953831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_7953831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7953831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7953831 prefixEnd_7953831 := by exact prefixLift 7953831
  have htrace : WordTrace (prefixWord ++ tailWord_7953831) baseStart_7953831 baseEnd_7953831 := by
    simpa [prefixWord, tailWord_7953831, baseEnd_7953831] using wordTrace_append hprefix tailTrace_7953831
  have hstable : (prefixWord ++ tailWord_7953831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7953831).length < 2 ^ (prefixWord ++ tailWord_7953831).sum := by decide
  have hdescent : baseEnd_7953831 < baseStart_7953831 := by decide
  rcases family_descends (prefixWord ++ tailWord_7953831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
