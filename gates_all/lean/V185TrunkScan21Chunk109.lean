import V185TrunkScan21Chunk108

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1324278 : List Nat := [5, 1, 1, 1, 1, 1, 1, 6, 4]
def baseStart_1324278 : Nat := 118140960795 + 1324278 * 2 ^ 59
def prefixEnd_1324278 : Nat := 4983230072969 + 3 ^ 40 * 1324278 * 2
def baseEnd_1324278 : Nat := 302218281855499995526561

theorem tailTrace_1324278 : CollatzResearch.WordTrace tailWord_1324278 prefixEnd_1324278 302218281855499995526561 := by
  unfold tailWord_1324278
  simp only [CollatzResearch.WordTrace]
  refine ⟨3018774168523403095081343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32200257797582966347534325 3018774168523403095081343)
  ·
    refine ⟨4528161252785104642622015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3018774168523403095081343 4528161252785104642622015)
    ·
      refine ⟨6792241879177656963933023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4528161252785104642622015 6792241879177656963933023)
      ·
        refine ⟨10188362818766485445899535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6792241879177656963933023 10188362818766485445899535)
        ·
          refine ⟨15282544228149728168849303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10188362818766485445899535 15282544228149728168849303)
          ·
            refine ⟨22923816342224592253273955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15282544228149728168849303 22923816342224592253273955)
            ·
              refine ⟨34385724513336888379910933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22923816342224592253273955 34385724513336888379910933)
              ·
                refine ⟨1611830836562666642808325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34385724513336888379910933 1611830836562666642808325)
                ·
                  refine ⟨302218281855499995526561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1611830836562666642808325 302218281855499995526561)
                  ·
                    rfl

theorem cell21_1324278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_1324278 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1324278 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1324278 prefixEnd_1324278 := by exact prefixLift 1324278
  have htrace : WordTrace (prefixWord ++ tailWord_1324278) baseStart_1324278 baseEnd_1324278 := by
    simpa [prefixWord, tailWord_1324278, baseEnd_1324278] using wordTrace_append hprefix tailTrace_1324278
  have hstable : (prefixWord ++ tailWord_1324278).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324278).length < 2 ^ (prefixWord ++ tailWord_1324278).sum := by decide
  have hdescent : baseEnd_1324278 < baseStart_1324278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324292 : List Nat := [2, 3, 2, 2, 2, 1, 1, 8]
def baseStart_1324292 : Nat := 118140960795 + 1324292 * 2 ^ 59
def prefixEnd_1324292 : Nat := 4983230072969 + 3 ^ 40 * 1324292 * 2
def baseEnd_1324292 : Nat := 100740492282079694097733

theorem tailTrace_1324292 : CollatzResearch.WordTrace tailWord_1324292 prefixEnd_1324292 100740492282079694097733 := by
  unfold tailWord_1324292
  simp only [CollatzResearch.WordTrace]
  refine ⟨24150448659161864956155565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32200598212215819941540753 24150448659161864956155565)
  ·
    refine ⟨9056418247185699358558337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24150448659161864956155565 9056418247185699358558337)
    ·
      refine ⟨6792313685389274518918753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9056418247185699358558337 6792313685389274518918753)
      ·
        refine ⟨5094235264041955889189065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6792313685389274518918753 5094235264041955889189065)
        ·
          refine ⟨3820676448031466916891799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5094235264041955889189065 3820676448031466916891799)
          ·
            refine ⟨5731014672047200375337699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3820676448031466916891799 5731014672047200375337699)
            ·
              refine ⟨8596522008070800563006549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5731014672047200375337699 8596522008070800563006549)
              ·
                refine ⟨100740492282079694097733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8596522008070800563006549 100740492282079694097733)
                ·
                  rfl

theorem cell21_1324292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 8].length) (baseStart_1324292 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1324292 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1324292 prefixEnd_1324292 := by exact prefixLift 1324292
  have htrace : WordTrace (prefixWord ++ tailWord_1324292) baseStart_1324292 baseEnd_1324292 := by
    simpa [prefixWord, tailWord_1324292, baseEnd_1324292] using wordTrace_append hprefix tailTrace_1324292
  have hstable : (prefixWord ++ tailWord_1324292).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324292).length < 2 ^ (prefixWord ++ tailWord_1324292).sum := by decide
  have hdescent : baseEnd_1324292 < baseStart_1324292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324368 : List Nat := [2, 1, 1, 1, 1, 5, 5, 5]
def baseStart_1324368 : Nat := 118140960795 + 1324368 * 2 ^ 59
def prefixEnd_1324368 : Nat := 4983230072969 + 3 ^ 40 * 1324368 * 2
def baseEnd_1324368 : Nat := 100746273693893279675459

theorem tailTrace_1324368 : CollatzResearch.WordTrace tailWord_1324368 prefixEnd_1324368 100746273693893279675459 := by
  unfold tailWord_1324368
  simp only [CollatzResearch.WordTrace]
  refine ⟨24151834633024197446038879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32202446177365596594718505 24151834633024197446038879)
  ·
    refine ⟨36227751949536296169058319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24151834633024197446038879 36227751949536296169058319)
    ·
      refine ⟨54341627924304444253587479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36227751949536296169058319 54341627924304444253587479)
      ·
        refine ⟨81512441886456666380381219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54341627924304444253587479 81512441886456666380381219)
        ·
          refine ⟨122268662829684999570571829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81512441886456666380381219 122268662829684999570571829)
          ·
            refine ⟨11462687140282968709741109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 122268662829684999570571829 11462687140282968709741109)
            ·
              refine ⟨1074626919401528316538229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11462687140282968709741109 1074626919401528316538229)
              ·
                refine ⟨100746273693893279675459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1074626919401528316538229 100746273693893279675459)
                ·
                  rfl

theorem cell21_1324368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 5, 5].length) (baseStart_1324368 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1324368 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1324368 prefixEnd_1324368 := by exact prefixLift 1324368
  have htrace : WordTrace (prefixWord ++ tailWord_1324368) baseStart_1324368 baseEnd_1324368 := by
    simpa [prefixWord, tailWord_1324368, baseEnd_1324368] using wordTrace_append hprefix tailTrace_1324368
  have hstable : (prefixWord ++ tailWord_1324368).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324368).length < 2 ^ (prefixWord ++ tailWord_1324368).sum := by decide
  have hdescent : baseEnd_1324368 < baseStart_1324368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324399 : List Nat := [1, 1, 2, 1, 3, 1, 3, 6, 3]
def baseStart_1324399 : Nat := 118140960795 + 1324399 * 2 ^ 59
def prefixEnd_1324399 : Nat := 4983230072969 + 3 ^ 40 * 1324399 * 2
def baseEnd_1324399 : Nat := 302245895704030674009647

theorem tailTrace_1324399 : CollatzResearch.WordTrace tailWord_1324399 prefixEnd_1324399 302245895704030674009647 := by
  unfold tailWord_1324399
  simp only [CollatzResearch.WordTrace]
  refine ⟨48304799928936087186456251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32203199952624058124304167 48304799928936087186456251)
  ·
    refine ⟨72457199893404130779684377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48304799928936087186456251 72457199893404130779684377)
    ·
      refine ⟨54342899920053098084763283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72457199893404130779684377 54342899920053098084763283)
      ·
        refine ⟨81514349880079647127144925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54342899920053098084763283 81514349880079647127144925)
        ·
          refine ⟨30567881205029867672679347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81514349880079647127144925 30567881205029867672679347)
          ·
            refine ⟨45851821807544801509019021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30567881205029867672679347 45851821807544801509019021)
            ·
              refine ⟨17194433177829300565882133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45851821807544801509019021 17194433177829300565882133)
              ·
                refine ⟨805989055210748464025725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17194433177829300565882133 805989055210748464025725)
                ·
                  refine ⟨302245895704030674009647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 805989055210748464025725 302245895704030674009647)
                  ·
                    rfl

theorem cell21_1324399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 6, 3].length) (baseStart_1324399 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1324399 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1324399 prefixEnd_1324399 := by exact prefixLift 1324399
  have htrace : WordTrace (prefixWord ++ tailWord_1324399) baseStart_1324399 baseEnd_1324399 := by
    simpa [prefixWord, tailWord_1324399, baseEnd_1324399] using wordTrace_append hprefix tailTrace_1324399
  have hstable : (prefixWord ++ tailWord_1324399).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324399).length < 2 ^ (prefixWord ++ tailWord_1324399).sum := by decide
  have hdescent : baseEnd_1324399 < baseStart_1324399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324427 : List Nat := [1, 1, 1, 1, 4, 3, 3, 7]
def baseStart_1324427 : Nat := 118140960795 + 1324427 * 2 ^ 59
def prefixEnd_1324427 : Nat := 4983230072969 + 3 ^ 40 * 1324427 * 2
def baseEnd_1324427 : Nat := 100750761895169615847641

theorem tailTrace_1324427 : CollatzResearch.WordTrace tailWord_1324427 prefixEnd_1324427 100750761895169615847641 := by
  unfold tailWord_1324427
  simp only [CollatzResearch.WordTrace]
  refine ⟨48305821172834647968475535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32203880781889765312317023 48305821172834647968475535)
  ·
    refine ⟨72458731759251971952713303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48305821172834647968475535 72458731759251971952713303)
    ·
      refine ⟨108688097638877957929069955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72458731759251971952713303 108688097638877957929069955)
      ·
        refine ⟨163032146458316936893604933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108688097638877957929069955 163032146458316936893604933)
        ·
          refine ⟨30568527460934425667550925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 163032146458316936893604933 30568527460934425667550925)
          ·
            refine ⟨11463197797850409625331597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30568527460934425667550925 11463197797850409625331597)
            ·
              refine ⟨4298699174193903609499349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11463197797850409625331597 4298699174193903609499349)
              ·
                refine ⟨100750761895169615847641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4298699174193903609499349 100750761895169615847641)
                ·
                  rfl

theorem cell21_1324427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 7].length) (baseStart_1324427 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1324427 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1324427 prefixEnd_1324427 := by exact prefixLift 1324427
  have htrace : WordTrace (prefixWord ++ tailWord_1324427) baseStart_1324427 baseEnd_1324427 := by
    simpa [prefixWord, tailWord_1324427, baseEnd_1324427] using wordTrace_append hprefix tailTrace_1324427
  have hstable : (prefixWord ++ tailWord_1324427).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324427).length < 2 ^ (prefixWord ++ tailWord_1324427).sum := by decide
  have hdescent : baseEnd_1324427 < baseStart_1324427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324461 : List Nat := [1, 5, 2, 2, 1, 2, 2, 6]
def baseStart_1324461 : Nat := 118140960795 + 1324461 * 2 ^ 59
def prefixEnd_1324461 : Nat := 4983230072969 + 3 ^ 40 * 1324461 * 2
def baseEnd_1324461 : Nat := 100753348316244114658729

theorem tailTrace_1324461 : CollatzResearch.WordTrace tailWord_1324461 prefixEnd_1324461 100753348316244114658729 := by
  unfold tailWord_1324461
  simp only [CollatzResearch.WordTrace]
  refine ⟨48307061254711471775213237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32204707503140981183475491 48307061254711471775213237)
  ·
    refine ⟨4528786992629200478926241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48307061254711471775213237 4528786992629200478926241)
    ·
      refine ⟨3396590244471900359194681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4528786992629200478926241 3396590244471900359194681)
      ·
        refine ⟨2547442683353925269396011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3396590244471900359194681 2547442683353925269396011)
        ·
          refine ⟨3821164025030887904094017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2547442683353925269396011 3821164025030887904094017)
          ·
            refine ⟨2865873018773165928070513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3821164025030887904094017 2865873018773165928070513)
            ·
              refine ⟨2149404764079874446052885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2865873018773165928070513 2149404764079874446052885)
              ·
                refine ⟨100753348316244114658729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2149404764079874446052885 100753348316244114658729)
                ·
                  rfl

theorem cell21_1324461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 6].length) (baseStart_1324461 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1324461 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1324461 prefixEnd_1324461 := by exact prefixLift 1324461
  have htrace : WordTrace (prefixWord ++ tailWord_1324461) baseStart_1324461 baseEnd_1324461 := by
    simpa [prefixWord, tailWord_1324461, baseEnd_1324461] using wordTrace_append hprefix tailTrace_1324461
  have hstable : (prefixWord ++ tailWord_1324461).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324461).length < 2 ^ (prefixWord ++ tailWord_1324461).sum := by decide
  have hdescent : baseEnd_1324461 < baseStart_1324461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324506 : List Nat := [3, 1, 1, 2, 3, 3, 2, 2, 4]
def baseStart_1324506 : Nat := 118140960795 + 1324506 * 2 ^ 59
def prefixEnd_1324506 : Nat := 4983230072969 + 3 ^ 40 * 1324506 * 2
def baseEnd_1324506 : Nat := 302270314561822265726095

theorem tailTrace_1324506 : CollatzResearch.WordTrace tailWord_1324506 prefixEnd_1324506 302270314561822265726095 := by
  unfold tailWord_1324506
  simp only [CollatzResearch.WordTrace]
  refine ⟨12077175634887111115150343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32205801693032296307067581 12077175634887111115150343)
  ·
    refine ⟨18115763452330666672725515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12077175634887111115150343 18115763452330666672725515)
    ·
      refine ⟨27173645178496000009088273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18115763452330666672725515 27173645178496000009088273)
      ·
        refine ⟨20380233883872000006816205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27173645178496000009088273 20380233883872000006816205)
        ·
          refine ⟨7642587706452000002556077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20380233883872000006816205 7642587706452000002556077)
          ·
            refine ⟨2865970389919500000958529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7642587706452000002556077 2865970389919500000958529)
            ·
              refine ⟨2149477792439625000718897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2865970389919500000958529 2149477792439625000718897)
              ·
                refine ⟨1612108344329718750539173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2149477792439625000718897 1612108344329718750539173)
                ·
                  refine ⟨302270314561822265726095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1612108344329718750539173 302270314561822265726095)
                  ·
                    rfl

theorem cell21_1324506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 2, 4].length) (baseStart_1324506 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1324506 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1324506 prefixEnd_1324506 := by exact prefixLift 1324506
  have htrace : WordTrace (prefixWord ++ tailWord_1324506) baseStart_1324506 baseEnd_1324506 := by
    simpa [prefixWord, tailWord_1324506, baseEnd_1324506] using wordTrace_append hprefix tailTrace_1324506
  have hstable : (prefixWord ++ tailWord_1324506).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324506).length < 2 ^ (prefixWord ++ tailWord_1324506).sum := by decide
  have hdescent : baseEnd_1324506 < baseStart_1324506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324509 : List Nat := [1, 4, 3, 1, 1, 2, 4, 2, 3]
def baseStart_1324509 : Nat := 118140960795 + 1324509 * 2 ^ 59
def prefixEnd_1324509 : Nat := 4983230072969 + 3 ^ 40 * 1324509 * 2
def baseEnd_1324509 : Nat := 302270999202694927176089

theorem tailTrace_1324509 : CollatzResearch.WordTrace tailWord_1324509 prefixEnd_1324509 302270999202694927176089 := by
  unfold tailWord_1324509
  simp only [CollatzResearch.WordTrace]
  refine ⟨48308811958537575972960581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32205874639025050648640387 48308811958537575972960581)
  ·
    refine ⟨9057902242225795494930109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48308811958537575972960581 9057902242225795494930109)
    ·
      refine ⟨3396713340834673310598791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9057902242225795494930109 3396713340834673310598791)
      ·
        refine ⟨5095070011252009965898187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3396713340834673310598791 5095070011252009965898187)
        ·
          refine ⟨7642605016878014948847281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5095070011252009965898187 7642605016878014948847281)
          ·
            refine ⟨5731953762658511211635461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7642605016878014948847281 5731953762658511211635461)
            ·
              refine ⟨1074741330498470852181649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5731953762658511211635461 1074741330498470852181649)
              ·
                refine ⟨806055997873853139136237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1074741330498470852181649 806055997873853139136237)
                ·
                  refine ⟨302270999202694927176089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 806055997873853139136237 302270999202694927176089)
                  ·
                    rfl

theorem cell21_1324509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 4, 2, 3].length) (baseStart_1324509 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1324509 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1324509 prefixEnd_1324509 := by exact prefixLift 1324509
  have htrace : WordTrace (prefixWord ++ tailWord_1324509) baseStart_1324509 baseEnd_1324509 := by
    simpa [prefixWord, tailWord_1324509, baseEnd_1324509] using wordTrace_append hprefix tailTrace_1324509
  have hstable : (prefixWord ++ tailWord_1324509).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324509).length < 2 ^ (prefixWord ++ tailWord_1324509).sum := by decide
  have hdescent : baseEnd_1324509 < baseStart_1324509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324557 : List Nat := [1, 7, 1, 1, 2, 2, 1, 2, 4]
def baseStart_1324557 : Nat := 118140960795 + 1324557 * 2 ^ 59
def prefixEnd_1324557 : Nat := 4983230072969 + 3 ^ 40 * 1324557 * 2
def baseEnd_1324557 : Nat := 302281953456657510375991

theorem tailTrace_1324557 : CollatzResearch.WordTrace tailWord_1324557 prefixEnd_1324557 302281953456657510375991 := by
  unfold tailWord_1324557
  simp only [CollatzResearch.WordTrace]
  refine ⟨48310562662363680170707925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32207041774909120113805283 48310562662363680170707925)
  ·
    refine ⟨1132278812399148754000967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 48310562662363680170707925 1132278812399148754000967)
    ·
      refine ⟨1698418218598723131001451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1132278812399148754000967 1698418218598723131001451)
      ·
        refine ⟨2547627327898084696502177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1698418218598723131001451 2547627327898084696502177)
        ·
          refine ⟨1910720495923563522376633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2547627327898084696502177 1910720495923563522376633)
          ·
            refine ⟨1433040371942672641782475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1910720495923563522376633 1433040371942672641782475)
            ·
              refine ⟨2149560557914008962673713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1433040371942672641782475 2149560557914008962673713)
              ·
                refine ⟨1612170418435506722005285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2149560557914008962673713 1612170418435506722005285)
                ·
                  refine ⟨302281953456657510375991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1612170418435506722005285 302281953456657510375991)
                  ·
                    rfl

theorem cell21_1324557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_1324557 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1324557 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1324557 prefixEnd_1324557 := by exact prefixLift 1324557
  have htrace : WordTrace (prefixWord ++ tailWord_1324557) baseStart_1324557 baseEnd_1324557 := by
    simpa [prefixWord, tailWord_1324557, baseEnd_1324557] using wordTrace_append hprefix tailTrace_1324557
  have hstable : (prefixWord ++ tailWord_1324557).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324557).length < 2 ^ (prefixWord ++ tailWord_1324557).sum := by decide
  have hdescent : baseEnd_1324557 < baseStart_1324557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324565 : List Nat := [1, 3, 2, 1, 3, 3, 1, 1, 6]
def baseStart_1324565 : Nat := 118140960795 + 1324565 * 2 ^ 59
def prefixEnd_1324565 : Nat := 4983230072969 + 3 ^ 40 * 1324565 * 2
def baseEnd_1324565 : Nat := 302283779165651274242641

theorem tailTrace_1324565 : CollatzResearch.WordTrace tailWord_1324565 prefixEnd_1324565 302283779165651274242641 := by
  unfold tailWord_1324565
  simp only [CollatzResearch.WordTrace]
  refine ⟨48310854446334697536999149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32207236297556465024666099 48310854446334697536999149)
  ·
    refine ⟨18116570417375511576374681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48310854446334697536999149 18116570417375511576374681)
    ·
      refine ⟨13587427813031633682281011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18116570417375511576374681 13587427813031633682281011)
      ·
        refine ⟨20381141719547450523421517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13587427813031633682281011 20381141719547450523421517)
        ·
          refine ⟨7642928144830293946283069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20381141719547450523421517 7642928144830293946283069)
          ·
            refine ⟨2866098054311360229856151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7642928144830293946283069 2866098054311360229856151)
            ·
              refine ⟨4299147081467040344784227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2866098054311360229856151 4299147081467040344784227)
              ·
                refine ⟨6448720622200560517176341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4299147081467040344784227 6448720622200560517176341)
                ·
                  refine ⟨302283779165651274242641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6448720622200560517176341 302283779165651274242641)
                  ·
                    rfl

theorem cell21_1324565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 1, 6].length) (baseStart_1324565 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1324565 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1324565 prefixEnd_1324565 := by exact prefixLift 1324565
  have htrace : WordTrace (prefixWord ++ tailWord_1324565) baseStart_1324565 baseEnd_1324565 := by
    simpa [prefixWord, tailWord_1324565, baseEnd_1324565] using wordTrace_append hprefix tailTrace_1324565
  have hstable : (prefixWord ++ tailWord_1324565).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324565).length < 2 ^ (prefixWord ++ tailWord_1324565).sum := by decide
  have hdescent : baseEnd_1324565 < baseStart_1324565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324574 : List Nat := [4, 3, 3, 1, 1, 1, 3, 1, 4]
def baseStart_1324574 : Nat := 118140960795 + 1324574 * 2 ^ 59
def prefixEnd_1324574 : Nat := 4983230072969 + 3 ^ 40 * 1324574 * 2
def baseEnd_1324574 : Nat := 302285833088269258592623

theorem tailTrace_1324574 : CollatzResearch.WordTrace tailWord_1324574 prefixEnd_1324574 302285833088269258592623 := by
  unfold tailWord_1324574
  simp only [CollatzResearch.WordTrace]
  refine ⟨6038897837912761509259597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32207455135534728049384517 6038897837912761509259597)
  ·
    refine ⟨2264586689217285565972349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6038897837912761509259597 2264586689217285565972349)
    ·
      refine ⟨849220008456482087239631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2264586689217285565972349 849220008456482087239631)
      ·
        refine ⟨1273830012684723130859447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 849220008456482087239631 1273830012684723130859447)
        ·
          refine ⟨1910745019027084696289171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1273830012684723130859447 1910745019027084696289171)
          ·
            refine ⟨2866117528540627044433757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1910745019027084696289171 2866117528540627044433757)
            ·
              refine ⟨1074794073202735141662659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2866117528540627044433757 1074794073202735141662659)
              ·
                refine ⟨1612191109804102712493989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1074794073202735141662659 1612191109804102712493989)
                ·
                  refine ⟨302285833088269258592623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1612191109804102712493989 302285833088269258592623)
                  ·
                    rfl

theorem cell21_1324574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_1324574 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1324574 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1324574 prefixEnd_1324574 := by exact prefixLift 1324574
  have htrace : WordTrace (prefixWord ++ tailWord_1324574) baseStart_1324574 baseEnd_1324574 := by
    simpa [prefixWord, tailWord_1324574, baseEnd_1324574] using wordTrace_append hprefix tailTrace_1324574
  have hstable : (prefixWord ++ tailWord_1324574).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324574).length < 2 ^ (prefixWord ++ tailWord_1324574).sum := by decide
  have hdescent : baseEnd_1324574 < baseStart_1324574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324624 : List Nat := [2, 1, 1, 1, 1, 3, 3, 3, 6]
def baseStart_1324624 : Nat := 118140960795 + 1324624 * 2 ^ 59
def prefixEnd_1324624 : Nat := 4983230072969 + 3 ^ 40 * 1324624 * 2
def baseEnd_1324624 : Nat := 302297243769480282759187

theorem tailTrace_1324624 : CollatzResearch.WordTrace tailWord_1324624 prefixEnd_1324624 302297243769480282759187 := by
  unfold tailWord_1324624
  simp only [CollatzResearch.WordTrace]
  refine ⟨24156503176560475306698463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32208670902080633742264617 24156503176560475306698463)
  ·
    refine ⟨36234754764840712960047695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24156503176560475306698463 36234754764840712960047695)
    ·
      refine ⟨54352132147261069440071543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36234754764840712960047695 54352132147261069440071543)
      ·
        refine ⟨81528198220891604160107315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54352132147261069440071543 81528198220891604160107315)
        ·
          refine ⟨122292297331337406240160973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81528198220891604160107315 122292297331337406240160973)
          ·
            refine ⟨45859611499251527340060365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122292297331337406240160973 45859611499251527340060365)
            ·
              refine ⟨17197354312219322752522637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45859611499251527340060365 17197354312219322752522637)
              ·
                refine ⟨6449007867082246032195989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17197354312219322752522637 6449007867082246032195989)
                ·
                  refine ⟨302297243769480282759187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6449007867082246032195989 302297243769480282759187)
                  ·
                    rfl

theorem cell21_1324624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3, 6].length) (baseStart_1324624 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1324624 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1324624 prefixEnd_1324624 := by exact prefixLift 1324624
  have htrace : WordTrace (prefixWord ++ tailWord_1324624) baseStart_1324624 baseEnd_1324624 := by
    simpa [prefixWord, tailWord_1324624, baseEnd_1324624] using wordTrace_append hprefix tailTrace_1324624
  have hstable : (prefixWord ++ tailWord_1324624).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324624).length < 2 ^ (prefixWord ++ tailWord_1324624).sum := by decide
  have hdescent : baseEnd_1324624 < baseStart_1324624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324641 : List Nat := [1, 2, 3, 1, 1, 3, 3, 3, 4]
def baseStart_1324641 : Nat := 118140960795 + 1324641 * 2 ^ 59
def prefixEnd_1324641 : Nat := 4983230072969 + 3 ^ 40 * 1324641 * 2
def baseEnd_1324641 : Nat := 302301123401092030975819

theorem tailTrace_1324641 : CollatzResearch.WordTrace tailWord_1324641 prefixEnd_1324641 302301123401092030975819 := by
  unfold tailWord_1324641
  simp only [CollatzResearch.WordTrace]
  refine ⟨48313626394059362516765777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32209084262706241677843851 48313626394059362516765777)
  ·
    refine ⟨36235219795544521887574333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48313626394059362516765777 36235219795544521887574333)
    ·
      refine ⟨13588207423329195707840375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36235219795544521887574333 13588207423329195707840375)
      ·
        refine ⟨20382311134993793561760563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13588207423329195707840375 20382311134993793561760563)
        ·
          refine ⟨30573466702490690342640845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20382311134993793561760563 30573466702490690342640845)
          ·
            refine ⟨11465050013434008878490317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30573466702490690342640845 11465050013434008878490317)
            ·
              refine ⟨4299393755037753329433869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11465050013434008878490317 4299393755037753329433869)
              ·
                refine ⟨1612272658139157498537701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4299393755037753329433869 1612272658139157498537701)
                ·
                  refine ⟨302301123401092030975819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1612272658139157498537701 302301123401092030975819)
                  ·
                    rfl

theorem cell21_1324641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 3, 4].length) (baseStart_1324641 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1324641 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1324641 prefixEnd_1324641 := by exact prefixLift 1324641
  have htrace : WordTrace (prefixWord ++ tailWord_1324641) baseStart_1324641 baseEnd_1324641 := by
    simpa [prefixWord, tailWord_1324641, baseEnd_1324641] using wordTrace_append hprefix tailTrace_1324641
  have hstable : (prefixWord ++ tailWord_1324641).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324641).length < 2 ^ (prefixWord ++ tailWord_1324641).sum := by decide
  have hdescent : baseEnd_1324641 < baseStart_1324641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324706 : List Nat := [3, 3, 1, 4, 1, 1, 3, 5]
def baseStart_1324706 : Nat := 118140960795 + 1324706 * 2 ^ 59
def prefixEnd_1324706 : Nat := 4983230072969 + 3 ^ 40 * 1324706 * 2
def baseEnd_1324706 : Nat := 100771985762222120797451

theorem tailTrace_1324706 : CollatzResearch.WordTrace tailWord_1324706 prefixEnd_1324706 100771985762222120797451 := by
  unfold tailWord_1324706
  simp only [CollatzResearch.WordTrace]
  refine ⟨12078999284705969654470493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32210664759215919078587981 12078999284705969654470493)
  ·
    refine ⟨4529624731764738620426435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12078999284705969654470493 4529624731764738620426435)
    ·
      refine ⟨6794437097647107930639653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4529624731764738620426435 6794437097647107930639653)
      ·
        refine ⟨1273956955808832736994935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6794437097647107930639653 1273956955808832736994935)
        ·
          refine ⟨1910935433713249105492403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1273956955808832736994935 1910935433713249105492403)
          ·
            refine ⟨2866403150569873658238605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1910935433713249105492403 2866403150569873658238605)
            ·
              refine ⟨1074901181463702621839477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2866403150569873658238605 1074901181463702621839477)
              ·
                refine ⟨100771985762222120797451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1074901181463702621839477 100771985762222120797451)
                ·
                  rfl

theorem cell21_1324706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 3, 5].length) (baseStart_1324706 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1324706 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1324706 prefixEnd_1324706 := by exact prefixLift 1324706
  have htrace : WordTrace (prefixWord ++ tailWord_1324706) baseStart_1324706 baseEnd_1324706 := by
    simpa [prefixWord, tailWord_1324706, baseEnd_1324706] using wordTrace_append hprefix tailTrace_1324706
  have hstable : (prefixWord ++ tailWord_1324706).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324706).length < 2 ^ (prefixWord ++ tailWord_1324706).sum := by decide
  have hdescent : baseEnd_1324706 < baseStart_1324706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324717 : List Nat := [1, 5, 2, 1, 1, 1, 2, 2, 6]
def baseStart_1324717 : Nat := 118140960795 + 1324717 * 2 ^ 59
def prefixEnd_1324717 : Nat := 4983230072969 + 3 ^ 40 * 1324717 * 2
def baseEnd_1324717 : Nat := 302318467636532787708997

theorem tailTrace_1324717 : CollatzResearch.WordTrace tailWord_1324717 prefixEnd_1324717 302318467636532787708997 := by
  unfold tailWord_1324717
  simp only [CollatzResearch.WordTrace]
  refine ⟨48316398341784027496532405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32210932227856018331021603 48316398341784027496532405)
  ·
    refine ⟨4529662344542252577799913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48316398341784027496532405 4529662344542252577799913)
    ·
      refine ⟨3397246758406689433349935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4529662344542252577799913 3397246758406689433349935)
      ·
        refine ⟨5095870137610034150024903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3397246758406689433349935 5095870137610034150024903)
        ·
          refine ⟨7643805206415051225037355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5095870137610034150024903 7643805206415051225037355)
          ·
            refine ⟨11465707809622576837556033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7643805206415051225037355 11465707809622576837556033)
            ·
              refine ⟨8599280857216932628167025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11465707809622576837556033 8599280857216932628167025)
              ·
                refine ⟨6449460642912699471125269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8599280857216932628167025 6449460642912699471125269)
                ·
                  refine ⟨302318467636532787708997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6449460642912699471125269 302318467636532787708997)
                  ·
                    rfl

theorem cell21_1324717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_1324717 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1324717 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1324717 prefixEnd_1324717 := by exact prefixLift 1324717
  have htrace : WordTrace (prefixWord ++ tailWord_1324717) baseStart_1324717 baseEnd_1324717 := by
    simpa [prefixWord, tailWord_1324717, baseEnd_1324717] using wordTrace_append hprefix tailTrace_1324717
  have hstable : (prefixWord ++ tailWord_1324717).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324717).length < 2 ^ (prefixWord ++ tailWord_1324717).sum := by decide
  have hdescent : baseEnd_1324717 < baseStart_1324717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324734 : List Nat := [4, 2, 1, 1, 2, 2, 3, 2, 4]
def baseStart_1324734 : Nat := 118140960795 + 1324734 * 2 ^ 59
def prefixEnd_1324734 : Nat := 4983230072969 + 3 ^ 40 * 1324734 * 2
def baseEnd_1324734 : Nat := 302322347268144535925629

theorem tailTrace_1324734 : CollatzResearch.WordTrace tailWord_1324734 prefixEnd_1324734 302322347268144535925629 := by
  unfold tailWord_1324734
  simp only [CollatzResearch.WordTrace]
  refine ⟨6039627297840304924987657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32211345588481626266600837 6039627297840304924987657)
  ·
    refine ⟨4529720473380228693740743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6039627297840304924987657 4529720473380228693740743)
    ·
      refine ⟨6794580710070343040611115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4529720473380228693740743 6794580710070343040611115)
      ·
        refine ⟨10191871065105514560916673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6794580710070343040611115 10191871065105514560916673)
        ·
          refine ⟨7643903298829135920687505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10191871065105514560916673 7643903298829135920687505)
          ·
            refine ⟨5732927474121851940515629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7643903298829135920687505 5732927474121851940515629)
            ·
              refine ⟨2149847802795694477693361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5732927474121851940515629 2149847802795694477693361)
              ·
                refine ⟨1612385852096770858270021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2149847802795694477693361 1612385852096770858270021)
                ·
                  refine ⟨302322347268144535925629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1612385852096770858270021 302322347268144535925629)
                  ·
                    rfl

theorem cell21_1324734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_1324734 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1324734 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1324734 prefixEnd_1324734 := by exact prefixLift 1324734
  have htrace : WordTrace (prefixWord ++ tailWord_1324734) baseStart_1324734 baseEnd_1324734 := by
    simpa [prefixWord, tailWord_1324734, baseEnd_1324734] using wordTrace_append hprefix tailTrace_1324734
  have hstable : (prefixWord ++ tailWord_1324734).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324734).length < 2 ^ (prefixWord ++ tailWord_1324734).sum := by decide
  have hdescent : baseEnd_1324734 < baseStart_1324734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324762 : List Nat := [3, 1, 1, 2, 2, 3, 2, 2, 5]
def baseStart_1324762 : Nat := 118140960795 + 1324762 * 2 ^ 59
def prefixEnd_1324762 : Nat := 4983230072969 + 3 ^ 40 * 1324762 * 2
def baseEnd_1324762 : Nat := 302328737249622709458905

theorem tailTrace_1324762 : CollatzResearch.WordTrace tailWord_1324762 prefixEnd_1324762 302328737249622709458905 := by
  unfold tailWord_1324762
  simp only [CollatzResearch.WordTrace]
  refine ⟨12079509906655250045480135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32212026417747333454613693 12079509906655250045480135)
  ·
    refine ⟨18119264859982875068220203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12079509906655250045480135 18119264859982875068220203)
    ·
      refine ⟨27178897289974312602330305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18119264859982875068220203 27178897289974312602330305)
      ·
        refine ⟨20384172967480734451747729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27178897289974312602330305 20384172967480734451747729)
        ·
          refine ⟨15288129725610550838810797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20384172967480734451747729 15288129725610550838810797)
          ·
            refine ⟨5733048647103956564554049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15288129725610550838810797 5733048647103956564554049)
            ·
              refine ⟨4299786485327967423415537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5733048647103956564554049 4299786485327967423415537)
              ·
                refine ⟨3224839863995975567561653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4299786485327967423415537 3224839863995975567561653)
                ·
                  refine ⟨302328737249622709458905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3224839863995975567561653 302328737249622709458905)
                  ·
                    rfl

theorem cell21_1324762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 2, 5].length) (baseStart_1324762 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1324762 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1324762 prefixEnd_1324762 := by exact prefixLift 1324762
  have htrace : WordTrace (prefixWord ++ tailWord_1324762) baseStart_1324762 baseEnd_1324762 := by
    simpa [prefixWord, tailWord_1324762, baseEnd_1324762] using wordTrace_append hprefix tailTrace_1324762
  have hstable : (prefixWord ++ tailWord_1324762).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324762).length < 2 ^ (prefixWord ++ tailWord_1324762).sum := by decide
  have hdescent : baseEnd_1324762 < baseStart_1324762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324765 : List Nat := [1, 4, 3, 3, 1, 1, 1, 7]
def baseStart_1324765 : Nat := 118140960795 + 1324765 * 2 ^ 59
def prefixEnd_1324765 : Nat := 4983230072969 + 3 ^ 40 * 1324765 * 2
def baseEnd_1324765 : Nat := 100776473963498456969633

theorem tailTrace_1324765 : CollatzResearch.WordTrace tailWord_1324765 prefixEnd_1324765 100776473963498456969633 := by
  unfold tailWord_1324765
  simp only [CollatzResearch.WordTrace]
  refine ⟨48318149045610131694279749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32212099363740087796186499 48318149045610131694279749)
  ·
    refine ⟨9059652946051899692677453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48318149045610131694279749 9059652946051899692677453)
    ·
      refine ⟨3397369854769462384754045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9059652946051899692677453 3397369854769462384754045)
      ·
        refine ⟨1274013695538548394282767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3397369854769462384754045 1274013695538548394282767)
        ·
          refine ⟨1911020543307822591424151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1274013695538548394282767 1911020543307822591424151)
          ·
            refine ⟨2866530814961733887136227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1911020543307822591424151 2866530814961733887136227)
            ·
              refine ⟨4299796222442600830704341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2866530814961733887136227 4299796222442600830704341)
              ·
                refine ⟨100776473963498456969633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4299796222442600830704341 100776473963498456969633)
                ·
                  rfl

theorem cell21_1324765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 7].length) (baseStart_1324765 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1324765 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1324765 prefixEnd_1324765 := by exact prefixLift 1324765
  have htrace : WordTrace (prefixWord ++ tailWord_1324765) baseStart_1324765 baseEnd_1324765 := by
    simpa [prefixWord, tailWord_1324765, baseEnd_1324765] using wordTrace_append hprefix tailTrace_1324765
  have hstable : (prefixWord ++ tailWord_1324765).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324765).length < 2 ^ (prefixWord ++ tailWord_1324765).sum := by decide
  have hdescent : baseEnd_1324765 < baseStart_1324765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324779 : List Nat := [1, 1, 1, 1, 2, 4, 5, 3, 3]
def baseStart_1324779 : Nat := 118140960795 + 1324779 * 2 ^ 59
def prefixEnd_1324779 : Nat := 4983230072969 + 3 ^ 40 * 1324779 * 2
def baseEnd_1324779 : Nat := 302332616881234457675537

theorem tailTrace_1324779 : CollatzResearch.WordTrace tailWord_1324779 prefixEnd_1324779 302332616881234457675537 := by
  unfold tailWord_1324779
  simp only [CollatzResearch.WordTrace]
  refine ⟨48318659667559412085289391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32212439778372941390192927 48318659667559412085289391)
  ·
    refine ⟨72477989501339118127934087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48318659667559412085289391 72477989501339118127934087)
    ·
      refine ⟨108716984252008677191901131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72477989501339118127934087 108716984252008677191901131)
      ·
        refine ⟨163075476378013015787851697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108716984252008677191901131 163075476378013015787851697)
        ·
          refine ⟨122306607283509761840888773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163075476378013015787851697 122306607283509761840888773)
          ·
            refine ⟨22932488865658080345166645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 122306607283509761840888773 22932488865658080345166645)
            ·
              refine ⟨2149920831155445032359373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22932488865658080345166645 2149920831155445032359373)
              ·
                refine ⟨806220311683291887134765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2149920831155445032359373 806220311683291887134765)
                ·
                  refine ⟨302332616881234457675537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 806220311683291887134765 302332616881234457675537)
                  ·
                    rfl

theorem cell21_1324779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 3, 3].length) (baseStart_1324779 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1324779 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1324779 prefixEnd_1324779 := by exact prefixLift 1324779
  have htrace : WordTrace (prefixWord ++ tailWord_1324779) baseStart_1324779 baseEnd_1324779 := by
    simpa [prefixWord, tailWord_1324779, baseEnd_1324779] using wordTrace_append hprefix tailTrace_1324779
  have hstable : (prefixWord ++ tailWord_1324779).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324779).length < 2 ^ (prefixWord ++ tailWord_1324779).sum := by decide
  have hdescent : baseEnd_1324779 < baseStart_1324779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324796 : List Nat := [2, 2, 2, 1, 3, 1, 5, 2, 3]
def baseStart_1324796 : Nat := 118140960795 + 1324796 * 2 ^ 59
def prefixEnd_1324796 : Nat := 4983230072969 + 3 ^ 40 * 1324796 * 2
def baseEnd_1324796 : Nat := 302336496512846205892169

theorem tailTrace_1324796 : CollatzResearch.WordTrace tailWord_1324796 prefixEnd_1324796 302336496512846205892169 := by
  unfold tailWord_1324796
  simp only [CollatzResearch.WordTrace]
  refine ⟨24159639854248911994329121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32212853138998549325772161 24159639854248911994329121)
  ·
    refine ⟨18119729890686683995746841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24159639854248911994329121 18119729890686683995746841)
    ·
      refine ⟨13589797418015012996810131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18119729890686683995746841 13589797418015012996810131)
      ·
        refine ⟨20384696127022519495215197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13589797418015012996810131 20384696127022519495215197)
        ·
          refine ⟨7644261047633444810705699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20384696127022519495215197 7644261047633444810705699)
          ·
            refine ⟨11466391571450167216058549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7644261047633444810705699 11466391571450167216058549)
            ·
              refine ⟨1074974209823453176505489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11466391571450167216058549 1074974209823453176505489)
              ·
                refine ⟨806230657367589882379117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1074974209823453176505489 806230657367589882379117)
                ·
                  refine ⟨302336496512846205892169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 806230657367589882379117 302336496512846205892169)
                  ·
                    rfl

theorem cell21_1324796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 5, 2, 3].length) (baseStart_1324796 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1324796 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1324796 prefixEnd_1324796 := by exact prefixLift 1324796
  have htrace : WordTrace (prefixWord ++ tailWord_1324796) baseStart_1324796 baseEnd_1324796 := by
    simpa [prefixWord, tailWord_1324796, baseEnd_1324796] using wordTrace_append hprefix tailTrace_1324796
  have hstable : (prefixWord ++ tailWord_1324796).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324796).length < 2 ^ (prefixWord ++ tailWord_1324796).sum := by decide
  have hdescent : baseEnd_1324796 < baseStart_1324796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324810 : List Nat := [3, 1, 2, 2, 1, 3, 4, 1, 4]
def baseStart_1324810 : Nat := 118140960795 + 1324810 * 2 ^ 59
def prefixEnd_1324810 : Nat := 4983230072969 + 3 ^ 40 * 1324810 * 2
def baseEnd_1324810 : Nat := 302339691503585292658807

theorem tailTrace_1324810 : CollatzResearch.WordTrace tailWord_1324810 prefixEnd_1324810 302339691503585292658807 := by
  unfold tailWord_1324810
  simp only [CollatzResearch.WordTrace]
  refine ⟨12079947582611776094916971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32213193553631402919778589 12079947582611776094916971)
  ·
    refine ⟨18119921373917664142375457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12079947582611776094916971 18119921373917664142375457)
    ·
      refine ⟨13589941030438248106781593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18119921373917664142375457 13589941030438248106781593)
      ·
        refine ⟨10192455772828686080086195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13589941030438248106781593 10192455772828686080086195)
        ·
          refine ⟨15288683659243029120129293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10192455772828686080086195 15288683659243029120129293)
          ·
            refine ⟨5733256372216135920048485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15288683659243029120129293 5733256372216135920048485)
            ·
              refine ⟨1074985569790525485009091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5733256372216135920048485 1074985569790525485009091)
              ·
                refine ⟨1612478354685788227513637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1074985569790525485009091 1612478354685788227513637)
                ·
                  refine ⟨302339691503585292658807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1612478354685788227513637 302339691503585292658807)
                  ·
                    rfl

theorem cell21_1324810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 4, 1, 4].length) (baseStart_1324810 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1324810 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1324810 prefixEnd_1324810 := by exact prefixLift 1324810
  have htrace : WordTrace (prefixWord ++ tailWord_1324810) baseStart_1324810 baseEnd_1324810 := by
    simpa [prefixWord, tailWord_1324810, baseEnd_1324810] using wordTrace_append hprefix tailTrace_1324810
  have hstable : (prefixWord ++ tailWord_1324810).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324810).length < 2 ^ (prefixWord ++ tailWord_1324810).sum := by decide
  have hdescent : baseEnd_1324810 < baseStart_1324810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324897 : List Nat := [1, 2, 3, 1, 1, 1, 3, 2, 7]
def baseStart_1324897 : Nat := 118140960795 + 1324897 * 2 ^ 59
def prefixEnd_1324897 : Nat := 4983230072969 + 3 ^ 40 * 1324897 * 2
def baseEnd_1324897 : Nat := 302359546088892474708629

theorem tailTrace_1324897 : CollatzResearch.WordTrace tailWord_1324897 prefixEnd_1324897 302359546088892474708629 := by
  unfold tailWord_1324897
  simp only [CollatzResearch.WordTrace]
  refine ⟨48322963481131918238084945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32215308987421278825389963 48322963481131918238084945)
  ·
    refine ⟨36242222610848938678563709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48322963481131918238084945 36242222610848938678563709)
    ·
      refine ⟨13590833479068352004461391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36242222610848938678563709 13590833479068352004461391)
      ·
        refine ⟨20386250218602528006692087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13590833479068352004461391 20386250218602528006692087)
        ·
          refine ⟨30579375327903792010038131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20386250218602528006692087 30579375327903792010038131)
          ·
            refine ⟨45869062991855688015057197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30579375327903792010038131 45869062991855688015057197)
            ·
              refine ⟨17200898621945883005646449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45869062991855688015057197 17200898621945883005646449)
              ·
                refine ⟨12900673966459412254234837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17200898621945883005646449 12900673966459412254234837)
                ·
                  refine ⟨302359546088892474708629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12900673966459412254234837 302359546088892474708629)
                  ·
                    rfl

theorem cell21_1324897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 7].length) (baseStart_1324897 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1324897 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1324897 prefixEnd_1324897 := by exact prefixLift 1324897
  have htrace : WordTrace (prefixWord ++ tailWord_1324897) baseStart_1324897 baseEnd_1324897 := by
    simpa [prefixWord, tailWord_1324897, baseEnd_1324897] using wordTrace_append hprefix tailTrace_1324897
  have hstable : (prefixWord ++ tailWord_1324897).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324897).length < 2 ^ (prefixWord ++ tailWord_1324897).sum := by decide
  have hdescent : baseEnd_1324897 < baseStart_1324897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1324948 : List Nat := [2, 4, 2, 1, 1, 2, 3, 3, 3]
def baseStart_1324948 : Nat := 118140960795 + 1324948 * 2 ^ 59
def prefixEnd_1324948 : Nat := 4983230072969 + 3 ^ 40 * 1324948 * 2
def baseEnd_1324948 : Nat := 302371184983727719358525

theorem tailTrace_1324948 : CollatzResearch.WordTrace tailWord_1324948 prefixEnd_1324948 302371184983727719358525 := by
  unfold tailWord_1324948
  simp only [CollatzResearch.WordTrace]
  refine ⟨24162411801973576974095749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32216549069298102632127665 24162411801973576974095749)
  ·
    refine ⟨4530452212870045682642953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24162411801973576974095749 4530452212870045682642953)
    ·
      refine ⟨3397839159652534261982215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4530452212870045682642953 3397839159652534261982215)
      ·
        refine ⟨5096758739478801392973323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3397839159652534261982215 5096758739478801392973323)
        ·
          refine ⟨7645138109218202089459985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5096758739478801392973323 7645138109218202089459985)
          ·
            refine ⟨5733853581913651567094989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7645138109218202089459985 5733853581913651567094989)
            ·
              refine ⟨2150195093217619337660621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5733853581913651567094989 2150195093217619337660621)
              ·
                refine ⟨806323159956607251622733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2150195093217619337660621 806323159956607251622733)
                ·
                  refine ⟨302371184983727719358525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 806323159956607251622733 302371184983727719358525)
                  ·
                    rfl

theorem cell21_1324948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 3, 3].length) (baseStart_1324948 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1324948 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1324948 prefixEnd_1324948 := by exact prefixLift 1324948
  have htrace : WordTrace (prefixWord ++ tailWord_1324948) baseStart_1324948 baseEnd_1324948 := by
    simpa [prefixWord, tailWord_1324948, baseEnd_1324948] using wordTrace_append hprefix tailTrace_1324948
  have hstable : (prefixWord ++ tailWord_1324948).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1324948).length < 2 ^ (prefixWord ++ tailWord_1324948).sum := by decide
  have hdescent : baseEnd_1324948 < baseStart_1324948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1324948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325018 : List Nat := [3, 1, 1, 2, 14]
def baseStart_1325018 : Nat := 118140960795 + 1325018 * 2 ^ 59
def prefixEnd_1325018 : Nat := 4983230072969 + 3 ^ 40 * 1325018 * 2
def baseEnd_1325018 : Nat := 3733174814042261150515

theorem tailTrace_1325018 : CollatzResearch.WordTrace tailWord_1325018 prefixEnd_1325018 3733174814042261150515 := by
  unfold tailWord_1325018
  simp only [CollatzResearch.WordTrace]
  refine ⟨12081844178423388975809927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32218251142462370602159805 12081844178423388975809927)
  ·
    refine ⟨18122766267635083463714891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12081844178423388975809927 18122766267635083463714891)
    ·
      refine ⟨27184149401452625195572337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18122766267635083463714891 27184149401452625195572337)
      ·
        refine ⟨20388112051089468896679253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27184149401452625195572337 20388112051089468896679253)
        ·
          refine ⟨3733174814042261150515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 20388112051089468896679253 3733174814042261150515)
          ·
            rfl

theorem cell21_1325018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 14].length) (baseStart_1325018 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1325018 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1325018 prefixEnd_1325018 := by exact prefixLift 1325018
  have htrace : WordTrace (prefixWord ++ tailWord_1325018) baseStart_1325018 baseEnd_1325018 := by
    simpa [prefixWord, tailWord_1325018, baseEnd_1325018] using wordTrace_append hprefix tailTrace_1325018
  have hstable : (prefixWord ++ tailWord_1325018).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325018).length < 2 ^ (prefixWord ++ tailWord_1325018).sum := by decide
  have hdescent : baseEnd_1325018 < baseStart_1325018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325049 : List Nat := [1, 2, 1, 3, 1, 4, 1, 1, 7]
def baseStart_1325049 : Nat := 118140960795 + 1325049 * 2 ^ 59
def prefixEnd_1325049 : Nat := 4983230072969 + 3 ^ 40 * 1325049 * 2
def baseEnd_1325049 : Nat := 302394234559773988174985

theorem tailTrace_1325049 : CollatzResearch.WordTrace tailWord_1325049 prefixEnd_1325049 302394234559773988174985 := by
  unfold tailWord_1325049
  simp only [CollatzResearch.WordTrace]
  refine ⟨48328507376581248197618201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32219004917720832131745467 48328507376581248197618201)
  ·
    refine ⟨36246380532435936148213651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48328507376581248197618201 36246380532435936148213651)
    ·
      refine ⟨54369570798653904222320477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36246380532435936148213651 54369570798653904222320477)
      ·
        refine ⟨20388589049495214083370179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54369570798653904222320477 20388589049495214083370179)
        ·
          refine ⟨30582883574242821125055269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20388589049495214083370179 30582883574242821125055269)
          ·
            refine ⟨5734290670170528960947863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30582883574242821125055269 5734290670170528960947863)
            ·
              refine ⟨8601436005255793441421795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5734290670170528960947863 8601436005255793441421795)
              ·
                refine ⟨12902154007883690162132693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8601436005255793441421795 12902154007883690162132693)
                ·
                  refine ⟨302394234559773988174985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12902154007883690162132693 302394234559773988174985)
                  ·
                    rfl

theorem cell21_1325049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 7].length) (baseStart_1325049 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1325049 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1325049 prefixEnd_1325049 := by exact prefixLift 1325049
  have htrace : WordTrace (prefixWord ++ tailWord_1325049) baseStart_1325049 baseEnd_1325049 := by
    simpa [prefixWord, tailWord_1325049, baseEnd_1325049] using wordTrace_append hprefix tailTrace_1325049
  have hstable : (prefixWord ++ tailWord_1325049).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325049).length < 2 ^ (prefixWord ++ tailWord_1325049).sum := by decide
  have hdescent : baseEnd_1325049 < baseStart_1325049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325080 : List Nat := [2, 1, 2, 3, 2, 1, 3, 1, 6]
def baseStart_1325080 : Nat := 118140960795 + 1325080 * 2 ^ 59
def prefixEnd_1325080 : Nat := 4983230072969 + 3 ^ 40 * 1325080 * 2
def baseEnd_1325080 : Nat := 302401309182124823158255

theorem tailTrace_1325080 : CollatzResearch.WordTrace tailWord_1325080 prefixEnd_1325080 302401309182124823158255 := by
  unfold tailWord_1325080
  simp only [CollatzResearch.WordTrace]
  refine ⟨24164819019734470245998347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32219758692979293661331129 24164819019734470245998347)
  ·
    refine ⟨36247228529601705368997521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24164819019734470245998347 36247228529601705368997521)
    ·
      refine ⟨27185421397201279026748141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36247228529601705368997521 27185421397201279026748141)
      ·
        refine ⟨10194533023950479635030553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27185421397201279026748141 10194533023950479635030553)
        ·
          refine ⟨7645899767962859726272915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10194533023950479635030553 7645899767962859726272915)
          ·
            refine ⟨11468849651944289589409373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7645899767962859726272915 11468849651944289589409373)
            ·
              refine ⟨4300818619479108596028515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11468849651944289589409373 4300818619479108596028515)
              ·
                refine ⟨6451227929218662894042773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4300818619479108596028515 6451227929218662894042773)
                ·
                  refine ⟨302401309182124823158255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6451227929218662894042773 302401309182124823158255)
                  ·
                    rfl

theorem cell21_1325080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 1, 6].length) (baseStart_1325080 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1325080 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1325080 prefixEnd_1325080 := by exact prefixLift 1325080
  have htrace : WordTrace (prefixWord ++ tailWord_1325080) baseStart_1325080 baseEnd_1325080 := by
    simpa [prefixWord, tailWord_1325080, baseEnd_1325080] using wordTrace_append hprefix tailTrace_1325080
  have hstable : (prefixWord ++ tailWord_1325080).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325080).length < 2 ^ (prefixWord ++ tailWord_1325080).sum := by decide
  have hdescent : baseEnd_1325080 < baseStart_1325080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325111 : List Nat := [1, 1, 3, 1, 2, 2, 6, 5]
def baseStart_1325111 : Nat := 118140960795 + 1325111 * 2 ^ 59
def prefixEnd_1325111 : Nat := 4983230072969 + 3 ^ 40 * 1325111 * 2
def baseEnd_1325111 : Nat := 100802794601491886047175

theorem tailTrace_1325111 : CollatzResearch.WordTrace tailWord_1325111 prefixEnd_1325111 100802794601491886047175 := by
  unfold tailWord_1325111
  simp only [CollatzResearch.WordTrace]
  refine ⟨48330768702356632786375187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32220512468237755190916791 48330768702356632786375187)
  ·
    refine ⟨72496153053534949179562781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48330768702356632786375187 72496153053534949179562781)
    ·
      refine ⟨27186057395075605942336043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72496153053534949179562781 27186057395075605942336043)
      ·
        refine ⟨40779086092613408913504065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27186057395075605942336043 40779086092613408913504065)
        ·
          refine ⟨30584314569460056685128049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40779086092613408913504065 30584314569460056685128049)
          ·
            refine ⟨22938235927095042513846037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30584314569460056685128049 22938235927095042513846037)
            ·
              refine ⟨1075229809082580117836533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 22938235927095042513846037 1075229809082580117836533)
              ·
                refine ⟨100802794601491886047175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1075229809082580117836533 100802794601491886047175)
                ·
                  rfl

theorem cell21_1325111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 6, 5].length) (baseStart_1325111 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1325111 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1325111 prefixEnd_1325111 := by exact prefixLift 1325111
  have htrace : WordTrace (prefixWord ++ tailWord_1325111) baseStart_1325111 baseEnd_1325111 := by
    simpa [prefixWord, tailWord_1325111, baseEnd_1325111] using wordTrace_append hprefix tailTrace_1325111
  have hstable : (prefixWord ++ tailWord_1325111).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325111).length < 2 ^ (prefixWord ++ tailWord_1325111).sum := by decide
  have hdescent : baseEnd_1325111 < baseStart_1325111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325139 : List Nat := [1, 1, 1, 2, 1, 1, 2, 2, 10]
def baseStart_1325139 : Nat := 118140960795 + 1325139 * 2 ^ 59
def prefixEnd_1325139 : Nat := 4983230072969 + 3 ^ 40 * 1325139 * 2
def baseEnd_1325139 : Nat := 302414773785953831674801

theorem tailTrace_1325139 : CollatzResearch.WordTrace tailWord_1325139 prefixEnd_1325139 302414773785953831674801 := by
  unfold tailWord_1325139
  simp only [CollatzResearch.WordTrace]
  refine ⟨48331789946255193568394471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32221193297503462378929647 48331789946255193568394471)
  ·
    refine ⟨72497684919382790352591707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48331789946255193568394471 72497684919382790352591707)
    ·
      refine ⟨108746527379074185528887561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72497684919382790352591707 108746527379074185528887561)
      ·
        refine ⟨81559895534305639146665671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108746527379074185528887561 81559895534305639146665671)
        ·
          refine ⟨122339843301458458719998507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81559895534305639146665671 122339843301458458719998507)
          ·
            refine ⟨183509764952187688079997761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122339843301458458719998507 183509764952187688079997761)
            ·
              refine ⟨137632323714140766059998321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 183509764952187688079997761 137632323714140766059998321)
              ·
                refine ⟨103224242785605574544998741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137632323714140766059998321 103224242785605574544998741)
                ·
                  refine ⟨302414773785953831674801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 103224242785605574544998741 302414773785953831674801)
                  ·
                    rfl

theorem cell21_1325139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 10].length) (baseStart_1325139 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1325139 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1325139 prefixEnd_1325139 := by exact prefixLift 1325139
  have htrace : WordTrace (prefixWord ++ tailWord_1325139) baseStart_1325139 baseEnd_1325139 := by
    simpa [prefixWord, tailWord_1325139, baseEnd_1325139] using wordTrace_append hprefix tailTrace_1325139
  have hstable : (prefixWord ++ tailWord_1325139).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325139).length < 2 ^ (prefixWord ++ tailWord_1325139).sum := by decide
  have hdescent : baseEnd_1325139 < baseStart_1325139 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325218 : List Nat := [3, 3, 1, 3, 1, 1, 1, 1, 7]
def baseStart_1325218 : Nat := 118140960795 + 1325218 * 2 ^ 59
def prefixEnd_1325218 : Nat := 4983230072969 + 3 ^ 40 * 1325218 * 2
def baseEnd_1325218 : Nat := 302432802662267249857973

theorem tailTrace_1325218 : CollatzResearch.WordTrace tailWord_1325218 prefixEnd_1325218 302432802662267249857973 := by
  unfold tailWord_1325218
  simp only [CollatzResearch.WordTrace]
  refine ⟨12083667828242247515130077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32223114208645993373680205 12083667828242247515130077)
  ·
    refine ⟨4531375435590842818173779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12083667828242247515130077 4531375435590842818173779)
    ·
      refine ⟨6797063153386264227260669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4531375435590842818173779 6797063153386264227260669)
      ·
        refine ⟨2548898682519849085222751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6797063153386264227260669 2548898682519849085222751)
        ·
          refine ⟨3823348023779773627834127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2548898682519849085222751 3823348023779773627834127)
          ·
            refine ⟨5735022035669660441751191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3823348023779773627834127 5735022035669660441751191)
            ·
              refine ⟨8602533053504490662626787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5735022035669660441751191 8602533053504490662626787)
              ·
                refine ⟨12903799580256735993940181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8602533053504490662626787 12903799580256735993940181)
                ·
                  refine ⟨302432802662267249857973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12903799580256735993940181 302432802662267249857973)
                  ·
                    rfl

theorem cell21_1325218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_1325218 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1325218 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1325218 prefixEnd_1325218 := by exact prefixLift 1325218
  have htrace : WordTrace (prefixWord ++ tailWord_1325218) baseStart_1325218 baseEnd_1325218 := by
    simpa [prefixWord, tailWord_1325218, baseEnd_1325218] using wordTrace_append hprefix tailTrace_1325218
  have hstable : (prefixWord ++ tailWord_1325218).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325218).length < 2 ^ (prefixWord ++ tailWord_1325218).sum := by decide
  have hdescent : baseEnd_1325218 < baseStart_1325218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325266 : List Nat := [3, 2, 2, 2, 1, 3, 3, 1, 4]
def baseStart_1325266 : Nat := 118140960795 + 1325266 * 2 ^ 59
def prefixEnd_1325266 : Nat := 4983230072969 + 3 ^ 40 * 1325266 * 2
def baseEnd_1325266 : Nat := 302443756916229833057875

theorem tailTrace_1325266 : CollatzResearch.WordTrace tailWord_1325266 prefixEnd_1325266 302443756916229833057875 := by
  unfold tailWord_1325266
  simp only [CollatzResearch.WordTrace]
  refine ⟨12084105504198773564566913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32224281344530062838845101 12084105504198773564566913)
  ·
    refine ⟨9063079128149080173425185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12084105504198773564566913 9063079128149080173425185)
    ·
      refine ⟨6797309346111810130068889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9063079128149080173425185 6797309346111810130068889)
      ·
        refine ⟨5097982009583857597551667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6797309346111810130068889 5097982009583857597551667)
        ·
          refine ⟨7646973014375786396327501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5097982009583857597551667 7646973014375786396327501)
          ·
            refine ⟨2867614880390919898622813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7646973014375786396327501 2867614880390919898622813)
            ·
              refine ⟨1075355580146594961983555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2867614880390919898622813 1075355580146594961983555)
              ·
                refine ⟨1613033370219892442975333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1075355580146594961983555 1613033370219892442975333)
                ·
                  refine ⟨302443756916229833057875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1613033370219892442975333 302443756916229833057875)
                  ·
                    rfl

theorem cell21_1325266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 3, 1, 4].length) (baseStart_1325266 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1325266 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1325266 prefixEnd_1325266 := by exact prefixLift 1325266
  have htrace : WordTrace (prefixWord ++ tailWord_1325266) baseStart_1325266 baseEnd_1325266 := by
    simpa [prefixWord, tailWord_1325266, baseEnd_1325266] using wordTrace_append hprefix tailTrace_1325266
  have hstable : (prefixWord ++ tailWord_1325266).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325266).length < 2 ^ (prefixWord ++ tailWord_1325266).sum := by decide
  have hdescent : baseEnd_1325266 < baseStart_1325266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325291 : List Nat := [1, 1, 1, 1, 2, 5, 1, 1, 8]
def baseStart_1325291 : Nat := 118140960795 + 1325291 * 2 ^ 59
def prefixEnd_1325291 : Nat := 4983230072969 + 3 ^ 40 * 1325291 * 2
def baseEnd_1325291 : Nat := 302449462256835345141157

theorem tailTrace_1325291 : CollatzResearch.WordTrace tailWord_1325291 prefixEnd_1325291 302449462256835345141157 := by
  unfold tailWord_1325291
  simp only [CollatzResearch.WordTrace]
  refine ⟨48337333841704523527927727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32224889227803015685285151 48337333841704523527927727)
  ·
    refine ⟨72506000762556785291891591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48337333841704523527927727 72506000762556785291891591)
    ·
      refine ⟨108759001143835177937837387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72506000762556785291891591 108759001143835177937837387)
      ·
        refine ⟨163138501715752766906756081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108759001143835177937837387 163138501715752766906756081)
        ·
          refine ⟨122353876286814575180067061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163138501715752766906756081 122353876286814575180067061)
          ·
            refine ⟨11470675901888866423131287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 122353876286814575180067061 11470675901888866423131287)
            ·
              refine ⟨17206013852833299634696931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11470675901888866423131287 17206013852833299634696931)
              ·
                refine ⟨25809020779249949452045397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17206013852833299634696931 25809020779249949452045397)
                ·
                  refine ⟨302449462256835345141157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25809020779249949452045397 302449462256835345141157)
                  ·
                    rfl

theorem cell21_1325291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 8].length) (baseStart_1325291 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1325291 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1325291 prefixEnd_1325291 := by exact prefixLift 1325291
  have htrace : WordTrace (prefixWord ++ tailWord_1325291) baseStart_1325291 baseEnd_1325291 := by
    simpa [prefixWord, tailWord_1325291, baseEnd_1325291] using wordTrace_append hprefix tailTrace_1325291
  have hstable : (prefixWord ++ tailWord_1325291).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325291).length < 2 ^ (prefixWord ++ tailWord_1325291).sum := by decide
  have hdescent : baseEnd_1325291 < baseStart_1325291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325308 : List Nat := [2, 2, 2, 1, 4, 1, 2, 1, 6]
def baseStart_1325308 : Nat := 118140960795 + 1325308 * 2 ^ 59
def prefixEnd_1325308 : Nat := 4983230072969 + 3 ^ 40 * 1325308 * 2
def baseEnd_1325308 : Nat := 302453341888447093357789

theorem tailTrace_1325308 : CollatzResearch.WordTrace tailWord_1325308 prefixEnd_1325308 302453341888447093357789 := by
  unfold tailWord_1325308
  simp only [CollatzResearch.WordTrace]
  refine ⟨24168976941321467715648289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32225302588428623620864385 24168976941321467715648289)
  ·
    refine ⟨18126732705991100786736217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24168976941321467715648289 18126732705991100786736217)
    ·
      refine ⟨13595049529493325590052163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18126732705991100786736217 13595049529493325590052163)
      ·
        refine ⟨20392574294239988385078245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13595049529493325590052163 20392574294239988385078245)
        ·
          refine ⟨3823607680169997822202171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20392574294239988385078245 3823607680169997822202171)
          ·
            refine ⟨5735411520254996733303257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3823607680169997822202171 5735411520254996733303257)
            ·
              refine ⟨4301558640191247549977443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5735411520254996733303257 4301558640191247549977443)
              ·
                refine ⟨6452337960286871324966165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4301558640191247549977443 6452337960286871324966165)
                ·
                  refine ⟨302453341888447093357789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6452337960286871324966165 302453341888447093357789)
                  ·
                    rfl

theorem cell21_1325308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 1, 6].length) (baseStart_1325308 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1325308 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1325308 prefixEnd_1325308 := by exact prefixLift 1325308
  have htrace : WordTrace (prefixWord ++ tailWord_1325308) baseStart_1325308 baseEnd_1325308 := by
    simpa [prefixWord, tailWord_1325308, baseEnd_1325308] using wordTrace_append hprefix tailTrace_1325308
  have hstable : (prefixWord ++ tailWord_1325308).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325308).length < 2 ^ (prefixWord ++ tailWord_1325308).sum := by decide
  have hdescent : baseEnd_1325308 < baseStart_1325308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325311 : List Nat := [1, 1, 2, 2, 1, 4, 5, 2, 3]
def baseStart_1325311 : Nat := 118140960795 + 1325311 * 2 ^ 59
def prefixEnd_1325311 : Nat := 4983230072969 + 3 ^ 40 * 1325311 * 2
def baseEnd_1325311 : Nat := 302454026529319754807783

theorem tailTrace_1325311 : CollatzResearch.WordTrace tailWord_1325311 prefixEnd_1325311 302454026529319754807783 := by
  unfold tailWord_1325311
  simp only [CollatzResearch.WordTrace]
  refine ⟨48338063301632066943655787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32225375534421377962437191 48338063301632066943655787)
  ·
    refine ⟨72507094952448100415483681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48338063301632066943655787 72507094952448100415483681)
    ·
      refine ⟨54380321214336075311612761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72507094952448100415483681 54380321214336075311612761)
      ·
        refine ⟨40785240910752056483709571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54380321214336075311612761 40785240910752056483709571)
        ·
          refine ⟨61177861366128084725564357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40785240910752056483709571 61177861366128084725564357)
          ·
            refine ⟨11470849006149015886043317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61177861366128084725564357 11470849006149015886043317)
            ·
              refine ⟨1075392094326470239316561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11470849006149015886043317 1075392094326470239316561)
              ·
                refine ⟨806544070744852679487421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1075392094326470239316561 806544070744852679487421)
                ·
                  refine ⟨302454026529319754807783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 806544070744852679487421 302454026529319754807783)
                  ·
                    rfl

theorem cell21_1325311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 5, 2, 3].length) (baseStart_1325311 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1325311 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1325311 prefixEnd_1325311 := by exact prefixLift 1325311
  have htrace : WordTrace (prefixWord ++ tailWord_1325311) baseStart_1325311 baseEnd_1325311 := by
    simpa [prefixWord, tailWord_1325311, baseEnd_1325311] using wordTrace_append hprefix tailTrace_1325311
  have hstable : (prefixWord ++ tailWord_1325311).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325311).length < 2 ^ (prefixWord ++ tailWord_1325311).sum := by decide
  have hdescent : baseEnd_1325311 < baseStart_1325311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325322 : List Nat := [3, 1, 2, 2, 1, 1, 3, 8]
def baseStart_1325322 : Nat := 118140960795 + 1325322 * 2 ^ 59
def prefixEnd_1325322 : Nat := 4983230072969 + 3 ^ 40 * 1325322 * 2
def baseEnd_1325322 : Nat := 100818845626395393374809

theorem tailTrace_1325322 : CollatzResearch.WordTrace tailWord_1325322 prefixEnd_1325322 100818845626395393374809 := by
  unfold tailWord_1325322
  simp only [CollatzResearch.WordTrace]
  refine ⟨12084616126148053955576555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32225643003061477214870813 12084616126148053955576555)
  ·
    refine ⟨18126924189222080933364833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12084616126148053955576555 18126924189222080933364833)
    ·
      refine ⟨13595193141916560700023625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18126924189222080933364833 13595193141916560700023625)
      ·
        refine ⟨10196394856437420525017719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13595193141916560700023625 10196394856437420525017719)
        ·
          refine ⟨15294592284656130787526579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10196394856437420525017719 15294592284656130787526579)
          ·
            refine ⟨22941888426984196181289869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15294592284656130787526579 22941888426984196181289869)
            ·
              refine ⟨8603208160119073567983701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22941888426984196181289869 8603208160119073567983701)
              ·
                refine ⟨100818845626395393374809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8603208160119073567983701 100818845626395393374809)
                ·
                  rfl

theorem cell21_1325322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 8].length) (baseStart_1325322 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1325322 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1325322 prefixEnd_1325322 := by exact prefixLift 1325322
  have htrace : WordTrace (prefixWord ++ tailWord_1325322) baseStart_1325322 baseEnd_1325322 := by
    simpa [prefixWord, tailWord_1325322, baseEnd_1325322] using wordTrace_append hprefix tailTrace_1325322
  have hstable : (prefixWord ++ tailWord_1325322).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325322).length < 2 ^ (prefixWord ++ tailWord_1325322).sum := by decide
  have hdescent : baseEnd_1325322 < baseStart_1325322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325367 : List Nat := [1, 1, 3, 1, 2, 1, 1, 5, 6]
def baseStart_1325367 : Nat := 118140960795 + 1325367 * 2 ^ 59
def prefixEnd_1325367 : Nat := 4983230072969 + 3 ^ 40 * 1325367 * 2
def baseEnd_1325367 : Nat := 302466806492276101874335

theorem tailTrace_1325367 : CollatzResearch.WordTrace tailWord_1325367 prefixEnd_1325367 302466806492276101874335 := by
  unfold tailWord_1325367
  simp only [CollatzResearch.WordTrace]
  refine ⟨48340105789429188507694355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32226737192952792338462903 48340105789429188507694355)
  ·
    refine ⟨72510158684143782761541533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48340105789429188507694355 72510158684143782761541533)
    ·
      refine ⟨27191309506553918535578075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72510158684143782761541533 27191309506553918535578075)
      ·
        refine ⟨40786964259830877803367113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27191309506553918535578075 40786964259830877803367113)
        ·
          refine ⟨30590223194873158352525335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40786964259830877803367113 30590223194873158352525335)
          ·
            refine ⟨45885334792309737528788003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30590223194873158352525335 45885334792309737528788003)
            ·
              refine ⟨68828002188464606293182005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45885334792309737528788003 68828002188464606293182005)
              ·
                refine ⟨6452625205168556839985813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68828002188464606293182005 6452625205168556839985813)
                ·
                  refine ⟨302466806492276101874335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6452625205168556839985813 302466806492276101874335)
                  ·
                    rfl

theorem cell21_1325367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5, 6].length) (baseStart_1325367 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1325367 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1325367 prefixEnd_1325367 := by exact prefixLift 1325367
  have htrace : WordTrace (prefixWord ++ tailWord_1325367) baseStart_1325367 baseEnd_1325367 := by
    simpa [prefixWord, tailWord_1325367, baseEnd_1325367] using wordTrace_append hprefix tailTrace_1325367
  have hstable : (prefixWord ++ tailWord_1325367).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325367).length < 2 ^ (prefixWord ++ tailWord_1325367).sum := by decide
  have hdescent : baseEnd_1325367 < baseStart_1325367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325384 : List Nat := [2, 1, 3, 1, 1, 2, 4, 3, 4]
def baseStart_1325384 : Nat := 118140960795 + 1325384 * 2 ^ 59
def prefixEnd_1325384 : Nat := 4983230072969 + 3 ^ 40 * 1325384 * 2
def baseEnd_1325384 : Nat := 302470686123887850090967

theorem tailTrace_1325384 : CollatzResearch.WordTrace tailWord_1325384 prefixEnd_1325384 302470686123887850090967 := by
  unfold tailWord_1325384
  simp only [CollatzResearch.WordTrace]
  refine ⟨24170362915183800205531603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32227150553578400274042137 24170362915183800205531603)
  ·
    refine ⟨36255544372775700308297405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24170362915183800205531603 36255544372775700308297405)
    ·
      refine ⟨13595829139790887615611527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36255544372775700308297405 13595829139790887615611527)
      ·
        refine ⟨20393743709686331423417291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13595829139790887615611527 20393743709686331423417291)
        ·
          refine ⟨30590615564529497135125937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20393743709686331423417291 30590615564529497135125937)
          ·
            refine ⟨22942961673397122851344453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30590615564529497135125937 22942961673397122851344453)
            ·
              refine ⟨4301805313761960534627085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22942961673397122851344453 4301805313761960534627085)
              ·
                refine ⟨1613176992660735200485157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4301805313761960534627085 1613176992660735200485157)
                ·
                  refine ⟨302470686123887850090967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1613176992660735200485157 302470686123887850090967)
                  ·
                    rfl

theorem cell21_1325384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 3, 4].length) (baseStart_1325384 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1325384 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1325384 prefixEnd_1325384 := by exact prefixLift 1325384
  have htrace : WordTrace (prefixWord ++ tailWord_1325384) baseStart_1325384 baseEnd_1325384 := by
    simpa [prefixWord, tailWord_1325384, baseEnd_1325384] using wordTrace_append hprefix tailTrace_1325384
  have hstable : (prefixWord ++ tailWord_1325384).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325384).length < 2 ^ (prefixWord ++ tailWord_1325384).sum := by decide
  have hdescent : baseEnd_1325384 < baseStart_1325384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325418 : List Nat := [3, 1, 3, 3, 1, 3, 1, 2, 4]
def baseStart_1325418 : Nat := 118140960795 + 1325418 * 2 ^ 59
def prefixEnd_1325418 : Nat := 4983230072969 + 3 ^ 40 * 1325418 * 2
def baseEnd_1325418 : Nat := 302478445387111346524231

theorem tailTrace_1325418 : CollatzResearch.WordTrace tailWord_1325418 prefixEnd_1325418 302478445387111346524231 := by
  unfold tailWord_1325418
  simp only [CollatzResearch.WordTrace]
  refine ⟨12085491478061106054450227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32227977274829616145200605 12085491478061106054450227)
  ·
    refine ⟨18128237217091659081675341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12085491478061106054450227 18128237217091659081675341)
    ·
      refine ⟨6798088956409372155628253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18128237217091659081675341 6798088956409372155628253)
      ·
        refine ⟨2549283358653514558360595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6798088956409372155628253 2549283358653514558360595)
        ·
          refine ⟨3823925037980271837540893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2549283358653514558360595 3823925037980271837540893)
          ·
            refine ⟨1433971889242601939077835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3823925037980271837540893 1433971889242601939077835)
            ·
              refine ⟨2150957833863902908616753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1433971889242601939077835 2150957833863902908616753)
              ·
                refine ⟨1613218375397927181462565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2150957833863902908616753 1613218375397927181462565)
                ·
                  refine ⟨302478445387111346524231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1613218375397927181462565 302478445387111346524231)
                  ·
                    rfl

theorem cell21_1325418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 2, 4].length) (baseStart_1325418 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1325418 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1325418 prefixEnd_1325418 := by exact prefixLift 1325418
  have htrace : WordTrace (prefixWord ++ tailWord_1325418) baseStart_1325418 baseEnd_1325418 := by
    simpa [prefixWord, tailWord_1325418, baseEnd_1325418] using wordTrace_append hprefix tailTrace_1325418
  have hstable : (prefixWord ++ tailWord_1325418).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325418).length < 2 ^ (prefixWord ++ tailWord_1325418).sum := by decide
  have hdescent : baseEnd_1325418 < baseStart_1325418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325536 : List Nat := [2, 1, 1, 3, 1, 1, 6, 2, 4]
def baseStart_1325536 : Nat := 118140960795 + 1325536 * 2 ^ 59
def prefixEnd_1325536 : Nat := 4983230072969 + 3 ^ 40 * 1325536 * 2
def baseEnd_1325536 : Nat := 302505374594769363557323

theorem tailTrace_1325536 : CollatzResearch.WordTrace tailWord_1325536 prefixEnd_1325536 302505374594769363557323 := by
  unfold tailWord_1325536
  simp only [CollatzResearch.WordTrace]
  refine ⟨24173134862908465185298231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32230846483877953580397641 24173134862908465185298231)
  ·
    refine ⟨36259702294362697777947347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24173134862908465185298231 36259702294362697777947347)
    ·
      refine ⟨54389553441544046666921021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36259702294362697777947347 54389553441544046666921021)
      ·
        refine ⟨20396082540579017500095383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54389553441544046666921021 20396082540579017500095383)
        ·
          refine ⟨30594123810868526250143075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20396082540579017500095383 30594123810868526250143075)
          ·
            refine ⟨45891185716302789375214613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30594123810868526250143075 45891185716302789375214613)
            ·
              refine ⟨2151149330451693251963185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 45891185716302789375214613 2151149330451693251963185)
              ·
                refine ⟨1613361997838769938972389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2151149330451693251963185 1613361997838769938972389)
                ·
                  refine ⟨302505374594769363557323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1613361997838769938972389 302505374594769363557323)
                  ·
                    rfl

theorem cell21_1325536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 2, 4].length) (baseStart_1325536 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1325536 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1325536 prefixEnd_1325536 := by exact prefixLift 1325536
  have htrace : WordTrace (prefixWord ++ tailWord_1325536) baseStart_1325536 baseEnd_1325536 := by
    simpa [prefixWord, tailWord_1325536, baseEnd_1325536] using wordTrace_append hprefix tailTrace_1325536
  have hstable : (prefixWord ++ tailWord_1325536).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325536).length < 2 ^ (prefixWord ++ tailWord_1325536).sum := by decide
  have hdescent : baseEnd_1325536 < baseStart_1325536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325539 : List Nat := [1, 1, 1, 6, 3, 1, 1, 4, 3]
def baseStart_1325539 : Nat := 118140960795 + 1325539 * 2 ^ 59
def prefixEnd_1325539 : Nat := 4983230072969 + 3 ^ 40 * 1325539 * 2
def baseEnd_1325539 : Nat := 302506059235642025007317

theorem tailTrace_1325539 : CollatzResearch.WordTrace tailWord_1325539 prefixEnd_1325539 302506059235642025007317 := by
  unfold tailWord_1325539
  simp only [CollatzResearch.WordTrace]
  refine ⟨48346379144806061882955671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32230919429870707921970447 48346379144806061882955671)
  ·
    refine ⟨72519568717209092824433507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48346379144806061882955671 72519568717209092824433507)
    ·
      refine ⟨108779353075813639236650261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72519568717209092824433507 108779353075813639236650261)
      ·
        refine ⟨5099032175428764339217981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 108779353075813639236650261 5099032175428764339217981)
        ·
          refine ⟨1912137065785786627206743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5099032175428764339217981 1912137065785786627206743)
          ·
            refine ⟨2868205598678679940810115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1912137065785786627206743 2868205598678679940810115)
            ·
              refine ⟨4302308398018019911215173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2868205598678679940810115 4302308398018019911215173)
              ·
                refine ⟨806682824628378733352845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4302308398018019911215173 806682824628378733352845)
                ·
                  refine ⟨302506059235642025007317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 806682824628378733352845 302506059235642025007317)
                  ·
                    rfl

theorem cell21_1325539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 4, 3].length) (baseStart_1325539 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1325539 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1325539 prefixEnd_1325539 := by exact prefixLift 1325539
  have htrace : WordTrace (prefixWord ++ tailWord_1325539) baseStart_1325539 baseEnd_1325539 := by
    simpa [prefixWord, tailWord_1325539, baseEnd_1325539] using wordTrace_append hprefix tailTrace_1325539
  have hstable : (prefixWord ++ tailWord_1325539).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325539).length < 2 ^ (prefixWord ++ tailWord_1325539).sum := by decide
  have hdescent : baseEnd_1325539 < baseStart_1325539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325626 : List Nat := [3, 1, 1, 1, 3, 4, 1, 7]
def baseStart_1325626 : Nat := 118140960795 + 1325626 * 2 ^ 59
def prefixEnd_1325626 : Nat := 4983230072969 + 3 ^ 40 * 1325626 * 2
def baseEnd_1325626 : Nat := 100841971273649735685713

theorem tailTrace_1325626 : CollatzResearch.WordTrace tailWord_1325626 prefixEnd_1325626 100841971273649735685713 := by
  unfold tailWord_1325626
  simp only [CollatzResearch.WordTrace]
  refine ⟨12087388073872718935343183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32233034863660583827581821 12087388073872718935343183)
  ·
    refine ⟨18131082110809078403014775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12087388073872718935343183 18131082110809078403014775)
    ·
      refine ⟨27196623166213617604522163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18131082110809078403014775 27196623166213617604522163)
      ·
        refine ⟨40794934749320426406783245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27196623166213617604522163 40794934749320426406783245)
        ·
          refine ⟨15298100530995159902543717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40794934749320426406783245 15298100530995159902543717)
          ·
            refine ⟨2868393849561592481726947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15298100530995159902543717 2868393849561592481726947)
            ·
              refine ⟨4302590774342388722590421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2868393849561592481726947 4302590774342388722590421)
              ·
                refine ⟨100841971273649735685713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4302590774342388722590421 100841971273649735685713)
                ·
                  rfl

theorem cell21_1325626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 7].length) (baseStart_1325626 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1325626 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1325626 prefixEnd_1325626 := by exact prefixLift 1325626
  have htrace : WordTrace (prefixWord ++ tailWord_1325626) baseStart_1325626 baseEnd_1325626 := by
    simpa [prefixWord, tailWord_1325626, baseEnd_1325626] using wordTrace_append hprefix tailTrace_1325626
  have hstable : (prefixWord ++ tailWord_1325626).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325626).length < 2 ^ (prefixWord ++ tailWord_1325626).sum := by decide
  have hdescent : baseEnd_1325626 < baseStart_1325626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325640 : List Nat := [2, 1, 3, 1, 1, 1, 1, 4, 7]
def baseStart_1325640 : Nat := 118140960795 + 1325640 * 2 ^ 59
def prefixEnd_1325640 : Nat := 4983230072969 + 3 ^ 40 * 1325640 * 2
def baseEnd_1325640 : Nat := 302529108811688293823777

theorem tailTrace_1325640 : CollatzResearch.WordTrace tailWord_1325640 prefixEnd_1325640 302529108811688293823777 := by
  unfold tailWord_1325640
  simp only [CollatzResearch.WordTrace]
  refine ⟨24175031458720078066191187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32233375278293437421588249 24175031458720078066191187)
  ·
    refine ⟨36262547188080117099286781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24175031458720078066191187 36262547188080117099286781)
    ·
      refine ⟨13598455195530043912232543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36262547188080117099286781 13598455195530043912232543)
      ·
        refine ⟨20397682793295065868348815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13598455195530043912232543 20397682793295065868348815)
        ·
          refine ⟨30596524189942598802523223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20397682793295065868348815 30596524189942598802523223)
          ·
            refine ⟨45894786284913898203784835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30596524189942598802523223 45894786284913898203784835)
            ·
              refine ⟨68842179427370847305677253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45894786284913898203784835 68842179427370847305677253)
              ·
                refine ⟨12907908642632033869814485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68842179427370847305677253 12907908642632033869814485)
                ·
                  refine ⟨302529108811688293823777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12907908642632033869814485 302529108811688293823777)
                  ·
                    rfl

theorem cell21_1325640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 7].length) (baseStart_1325640 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1325640 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1325640 prefixEnd_1325640 := by exact prefixLift 1325640
  have htrace : WordTrace (prefixWord ++ tailWord_1325640) baseStart_1325640 baseEnd_1325640 := by
    simpa [prefixWord, tailWord_1325640, baseEnd_1325640] using wordTrace_append hprefix tailTrace_1325640
  have hstable : (prefixWord ++ tailWord_1325640).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325640).length < 2 ^ (prefixWord ++ tailWord_1325640).sum := by decide
  have hdescent : baseEnd_1325640 < baseStart_1325640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325764 : List Nat := [2, 3, 3, 1, 1, 3, 1, 1, 6]
def baseStart_1325764 : Nat := 118140960795 + 1325764 * 2 ^ 59
def prefixEnd_1325764 : Nat := 4983230072969 + 3 ^ 40 * 1325764 * 2
def baseEnd_1325764 : Nat := 302557407301091633756857

theorem tailTrace_1325764 : CollatzResearch.WordTrace tailWord_1325764 prefixEnd_1325764 302557407301091633756857 := by
  unfold tailWord_1325764
  simp only [CollatzResearch.WordTrace]
  refine ⟨24177292784495462654948173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32236390379327283539930897 24177292784495462654948173)
  ·
    refine ⟨9066484794185798495605565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24177292784495462654948173 9066484794185798495605565)
    ·
      refine ⟨3399931797819674435852087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9066484794185798495605565 3399931797819674435852087)
      ·
        refine ⟨5099897696729511653778131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3399931797819674435852087 5099897696729511653778131)
        ·
          refine ⟨7649846545094267480667197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5099897696729511653778131 7649846545094267480667197)
          ·
            refine ⟨2868692454410350305250199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7649846545094267480667197 2868692454410350305250199)
            ·
              refine ⟨4303038681615525457875299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2868692454410350305250199 4303038681615525457875299)
              ·
                refine ⟨6454558022423288186812949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4303038681615525457875299 6454558022423288186812949)
                ·
                  refine ⟨302557407301091633756857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6454558022423288186812949 302557407301091633756857)
                  ·
                    rfl

theorem cell21_1325764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 1, 6].length) (baseStart_1325764 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1325764 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1325764 prefixEnd_1325764 := by exact prefixLift 1325764
  have htrace : WordTrace (prefixWord ++ tailWord_1325764) baseStart_1325764 baseEnd_1325764 := by
    simpa [prefixWord, tailWord_1325764, baseEnd_1325764] using wordTrace_append hprefix tailTrace_1325764
  have hstable : (prefixWord ++ tailWord_1325764).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325764).length < 2 ^ (prefixWord ++ tailWord_1325764).sum := by decide
  have hdescent : baseEnd_1325764 < baseStart_1325764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325795 : List Nat := [1, 1, 1, 7, 1, 1, 4, 5]
def baseStart_1325795 : Nat := 118140960795 + 1325795 * 2 ^ 59
def prefixEnd_1325795 : Nat := 4983230072969 + 3 ^ 40 * 1325795 * 2
def baseEnd_1325795 : Nat := 100854827307814156246709

theorem tailTrace_1325795 : CollatzResearch.WordTrace tailWord_1325795 prefixEnd_1325795 100854827307814156246709 := by
  unfold tailWord_1325795
  simp only [CollatzResearch.WordTrace]
  refine ⟨48355716231878617604274839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32237144154585745069516559 48355716231878617604274839)
  ·
    refine ⟨72533574347817926406412259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48355716231878617604274839 72533574347817926406412259)
    ·
      refine ⟨108800361521726889609618389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72533574347817926406412259 108800361521726889609618389)
      ·
        refine ⟨2550008473165473975225431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 108800361521726889609618389 2550008473165473975225431)
        ·
          refine ⟨3825012709748210962838147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2550008473165473975225431 3825012709748210962838147)
          ·
            refine ⟨5737519064622316444257221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3825012709748210962838147 5737519064622316444257221)
            ·
              refine ⟨1075784824616684333298229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5737519064622316444257221 1075784824616684333298229)
              ·
                refine ⟨100854827307814156246709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1075784824616684333298229 100854827307814156246709)
                ·
                  rfl

theorem cell21_1325795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 4, 5].length) (baseStart_1325795 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1325795 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1325795 prefixEnd_1325795 := by exact prefixLift 1325795
  have htrace : WordTrace (prefixWord ++ tailWord_1325795) baseStart_1325795 baseEnd_1325795 := by
    simpa [prefixWord, tailWord_1325795, baseEnd_1325795] using wordTrace_append hprefix tailTrace_1325795
  have hstable : (prefixWord ++ tailWord_1325795).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325795).length < 2 ^ (prefixWord ++ tailWord_1325795).sum := by decide
  have hdescent : baseEnd_1325795 < baseStart_1325795 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325823 : List Nat := [1, 1, 2, 2, 1, 3, 1, 6, 4]
def baseStart_1325823 : Nat := 118140960795 + 1325823 * 2 ^ 59
def prefixEnd_1325823 : Nat := 4983230072969 + 3 ^ 40 * 1325823 * 2
def baseEnd_1325823 : Nat := 302570871904920642273403

theorem tailTrace_1325823 : CollatzResearch.WordTrace tailWord_1325823 prefixEnd_1325823 302570871904920642273403 := by
  unfold tailWord_1325823
  simp only [CollatzResearch.WordTrace]
  refine ⟨48356737475777178386294123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32237824983851452257529415 48356737475777178386294123)
  ·
    refine ⟨72535106213665767579441185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48356737475777178386294123 72535106213665767579441185)
    ·
      refine ⟨54401329660249325684580889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72535106213665767579441185 54401329660249325684580889)
      ·
        refine ⟨40800997245186994263435667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54401329660249325684580889 40800997245186994263435667)
        ·
          refine ⟨61201495867780491395153501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40800997245186994263435667 61201495867780491395153501)
          ·
            refine ⟨22950560950417684273182563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61201495867780491395153501 22950560950417684273182563)
            ·
              refine ⟨34425841425626526409773845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22950560950417684273182563 34425841425626526409773845)
              ·
                refine ⟨1613711316826243425458149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34425841425626526409773845 1613711316826243425458149)
                ·
                  refine ⟨302570871904920642273403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1613711316826243425458149 302570871904920642273403)
                  ·
                    rfl

theorem cell21_1325823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 6, 4].length) (baseStart_1325823 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1325823 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1325823 prefixEnd_1325823 := by exact prefixLift 1325823
  have htrace : WordTrace (prefixWord ++ tailWord_1325823) baseStart_1325823 baseEnd_1325823 := by
    simpa [prefixWord, tailWord_1325823, baseEnd_1325823] using wordTrace_append hprefix tailTrace_1325823
  have hstable : (prefixWord ++ tailWord_1325823).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325823).length < 2 ^ (prefixWord ++ tailWord_1325823).sum := by decide
  have hdescent : baseEnd_1325823 < baseStart_1325823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1325826 : List Nat := [3, 4, 1, 1, 1, 2, 3, 1, 5]
def baseStart_1325826 : Nat := 118140960795 + 1325826 * 2 ^ 59
def prefixEnd_1325826 : Nat := 4983230072969 + 3 ^ 40 * 1325826 * 2
def baseEnd_1325826 : Nat := 302571556545793303723397

theorem tailTrace_1325826 : CollatzResearch.WordTrace tailWord_1325826 prefixEnd_1325826 302571556545793303723397 := by
  unfold tailWord_1325826
  simp only [CollatzResearch.WordTrace]
  refine ⟨12089211723691577474663333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32237897929844206599102221 12089211723691577474663333)
  ·
    refine ⟨2266727198192170776499375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12089211723691577474663333 2266727198192170776499375)
    ·
      refine ⟨3400090797288256164749063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2266727198192170776499375 3400090797288256164749063)
      ·
        refine ⟨5100136195932384247123595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3400090797288256164749063 5100136195932384247123595)
        ·
          refine ⟨7650204293898576370685393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5100136195932384247123595 7650204293898576370685393)
          ·
            refine ⟨5737653220423932278014045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7650204293898576370685393 5737653220423932278014045)
            ·
              refine ⟨2151619957658974604255267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5737653220423932278014045 2151619957658974604255267)
              ·
                refine ⟨3227429936488461906382901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2151619957658974604255267 3227429936488461906382901)
                ·
                  refine ⟨302571556545793303723397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3227429936488461906382901 302571556545793303723397)
                  ·
                    rfl

theorem cell21_1325826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_1325826 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1325826 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1325826 prefixEnd_1325826 := by exact prefixLift 1325826
  have htrace : WordTrace (prefixWord ++ tailWord_1325826) baseStart_1325826 baseEnd_1325826 := by
    simpa [prefixWord, tailWord_1325826, baseEnd_1325826] using wordTrace_append hprefix tailTrace_1325826
  have hstable : (prefixWord ++ tailWord_1325826).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1325826).length < 2 ^ (prefixWord ++ tailWord_1325826).sum := by decide
  have hdescent : baseEnd_1325826 < baseStart_1325826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1325826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326009 : List Nat := [1, 2, 1, 4, 2, 4, 2, 1, 4]
def baseStart_1326009 : Nat := 118140960795 + 1326009 * 2 ^ 59
def prefixEnd_1326009 : Nat := 4983230072969 + 3 ^ 40 * 1326009 * 2
def baseEnd_1326009 : Nat := 302613319639025652173023

theorem tailTrace_1326009 : CollatzResearch.WordTrace tailWord_1326009 prefixEnd_1326009 302613319639025652173023 := by
  unfold tailWord_1326009
  simp only [CollatzResearch.WordTrace]
  refine ⟨48363521453103332152565081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32242347635402221435043387 48363521453103332152565081)
  ·
    refine ⟨36272641089827499114423811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48363521453103332152565081 36272641089827499114423811)
    ·
      refine ⟨54408961634741248671635717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36272641089827499114423811 54408961634741248671635717)
      ·
        refine ⟨10201680306513984125931697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54408961634741248671635717 10201680306513984125931697)
        ·
          refine ⟨7651260229885488094448773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10201680306513984125931697 7651260229885488094448773)
          ·
            refine ⟨1434611293103529017709145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7651260229885488094448773 1434611293103529017709145)
            ·
              refine ⟨1075958469827646763281859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1434611293103529017709145 1075958469827646763281859)
              ·
                refine ⟨1613937704741470144922789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1075958469827646763281859 1613937704741470144922789)
                ·
                  refine ⟨302613319639025652173023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1613937704741470144922789 302613319639025652173023)
                  ·
                    rfl

theorem cell21_1326009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 2, 1, 4].length) (baseStart_1326009 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1326009 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1326009 prefixEnd_1326009 := by exact prefixLift 1326009
  have htrace : WordTrace (prefixWord ++ tailWord_1326009) baseStart_1326009 baseEnd_1326009 := by
    simpa [prefixWord, tailWord_1326009, baseEnd_1326009] using wordTrace_append hprefix tailTrace_1326009
  have hstable : (prefixWord ++ tailWord_1326009).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326009).length < 2 ^ (prefixWord ++ tailWord_1326009).sum := by decide
  have hdescent : baseEnd_1326009 < baseStart_1326009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326113 : List Nat := [1, 2, 3, 2, 3, 2, 2, 1, 5]
def baseStart_1326113 : Nat := 118140960795 + 1326113 * 2 ^ 59
def prefixEnd_1326113 : Nat := 4983230072969 + 3 ^ 40 * 1326113 * 2
def baseEnd_1326113 : Nat := 302637053855944582439477

theorem tailTrace_1326113 : CollatzResearch.WordTrace tailWord_1326113 prefixEnd_1326113 302637053855944582439477 := by
  unfold tailWord_1326113
  simp only [CollatzResearch.WordTrace]
  refine ⟨48367314644726557914350993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32244876429817705276233995 48367314644726557914350993)
  ·
    refine ⟨36275485983544918435763245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48367314644726557914350993 36275485983544918435763245)
    ·
      refine ⟨13603307243829344413411217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36275485983544918435763245 13603307243829344413411217)
      ·
        refine ⟨10202480432872008310058413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13603307243829344413411217 10202480432872008310058413)
        ·
          refine ⟨3825930162327003116271905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10202480432872008310058413 3825930162327003116271905)
          ·
            refine ⟨2869447621745252337203929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3825930162327003116271905 2869447621745252337203929)
            ·
              refine ⟨2152085716308939252902947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2869447621745252337203929 2152085716308939252902947)
              ·
                refine ⟨3228128574463408879354421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2152085716308939252902947 3228128574463408879354421)
                ·
                  refine ⟨302637053855944582439477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3228128574463408879354421 302637053855944582439477)
                  ·
                    rfl

theorem cell21_1326113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 1, 5].length) (baseStart_1326113 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1326113 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1326113 prefixEnd_1326113 := by exact prefixLift 1326113
  have htrace : WordTrace (prefixWord ++ tailWord_1326113) baseStart_1326113 baseEnd_1326113 := by
    simpa [prefixWord, tailWord_1326113, baseEnd_1326113] using wordTrace_append hprefix tailTrace_1326113
  have hstable : (prefixWord ++ tailWord_1326113).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326113).length < 2 ^ (prefixWord ++ tailWord_1326113).sum := by decide
  have hdescent : baseEnd_1326113 < baseStart_1326113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326178 : List Nat := [3, 3, 2, 2, 1, 3, 2, 1, 4]
def baseStart_1326178 : Nat := 118140960795 + 1326178 * 2 ^ 59
def prefixEnd_1326178 : Nat := 4983230072969 + 3 ^ 40 * 1326178 * 2
def baseEnd_1326178 : Nat := 302651887741518913856011

theorem tailTrace_1326178 : CollatzResearch.WordTrace tailWord_1326178 prefixEnd_1326178 302651887741518913856011 := by
  unfold tailWord_1326178
  simp only [CollatzResearch.WordTrace]
  refine ⟨12092421347372768503866797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32246456926327382676978125 12092421347372768503866797)
  ·
    refine ⟨4534658005264788188950049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12092421347372768503866797 4534658005264788188950049)
    ·
      refine ⟨3400993503948591141712537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4534658005264788188950049 3400993503948591141712537)
      ·
        refine ⟨2550745127961443356284403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3400993503948591141712537 2550745127961443356284403)
        ·
          refine ⟨3826117691942165034426605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2550745127961443356284403 3826117691942165034426605)
          ·
            refine ⟨1434794134478311887909977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3826117691942165034426605 1434794134478311887909977)
            ·
              refine ⟨1076095600858733915932483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1434794134478311887909977 1076095600858733915932483)
              ·
                refine ⟨1614143401288100873898725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1076095600858733915932483 1614143401288100873898725)
                ·
                  refine ⟨302651887741518913856011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1614143401288100873898725 302651887741518913856011)
                  ·
                    rfl

theorem cell21_1326178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_1326178 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1326178 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1326178 prefixEnd_1326178 := by exact prefixLift 1326178
  have htrace : WordTrace (prefixWord ++ tailWord_1326178) baseStart_1326178 baseEnd_1326178 := by
    simpa [prefixWord, tailWord_1326178, baseEnd_1326178] using wordTrace_append hprefix tailTrace_1326178
  have hstable : (prefixWord ++ tailWord_1326178).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326178).length < 2 ^ (prefixWord ++ tailWord_1326178).sum := by decide
  have hdescent : baseEnd_1326178 < baseStart_1326178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326234 : List Nat := [3, 1, 1, 5, 1, 1, 3, 6]
def baseStart_1326234 : Nat := 118140960795 + 1326234 * 2 ^ 59
def prefixEnd_1326234 : Nat := 4983230072969 + 3 ^ 40 * 1326234 * 2
def baseEnd_1326234 : Nat := 100888222568158420307521

theorem tailTrace_1326234 : CollatzResearch.WordTrace tailWord_1326234 prefixEnd_1326234 100888222568158420307521 := by
  unfold tailWord_1326234
  simp only [CollatzResearch.WordTrace]
  refine ⟨12092931969322048894876439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32247818584858797053003837 12092931969322048894876439)
  ·
    refine ⟨18139397953983073342314659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12092931969322048894876439 18139397953983073342314659)
    ·
      refine ⟨27209096930974610013471989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18139397953983073342314659 27209096930974610013471989)
      ·
        refine ⟨2550852837278869688762999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27209096930974610013471989 2550852837278869688762999)
        ·
          refine ⟨3826279255918304533144499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2550852837278869688762999 3826279255918304533144499)
          ·
            refine ⟨5739418883877456799716749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3826279255918304533144499 5739418883877456799716749)
            ·
              refine ⟨2152282081454046299893781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5739418883877456799716749 2152282081454046299893781)
              ·
                refine ⟨100888222568158420307521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2152282081454046299893781 100888222568158420307521)
                ·
                  rfl

theorem cell21_1326234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 6].length) (baseStart_1326234 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1326234 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1326234 prefixEnd_1326234 := by exact prefixLift 1326234
  have htrace : WordTrace (prefixWord ++ tailWord_1326234) baseStart_1326234 baseEnd_1326234 := by
    simpa [prefixWord, tailWord_1326234, baseEnd_1326234] using wordTrace_append hprefix tailTrace_1326234
  have hstable : (prefixWord ++ tailWord_1326234).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326234).length < 2 ^ (prefixWord ++ tailWord_1326234).sum := by decide
  have hdescent : baseEnd_1326234 < baseStart_1326234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326265 : List Nat := [1, 2, 1, 4, 1, 3, 1, 5, 3]
def baseStart_1326265 : Nat := 118140960795 + 1326265 * 2 ^ 59
def prefixEnd_1326265 : Nat := 4983230072969 + 3 ^ 40 * 1326265 * 2
def baseEnd_1326265 : Nat := 302671742326826095905833

theorem tailTrace_1326265 : CollatzResearch.WordTrace tailWord_1326265 prefixEnd_1326265 302671742326826095905833 := by
  unfold tailWord_1326265
  simp only [CollatzResearch.WordTrace]
  refine ⟨48372858540175887873884249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32248572360117258582589499 48372858540175887873884249)
  ·
    refine ⟨36279643905131915905413187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48372858540175887873884249 36279643905131915905413187)
    ·
      refine ⟨54419465857697873858119781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36279643905131915905413187 54419465857697873858119781)
      ·
        refine ⟨10203649848318351348397459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54419465857697873858119781 10203649848318351348397459)
        ·
          refine ⟨15305474772477527022596189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10203649848318351348397459 15305474772477527022596189)
          ·
            refine ⟨5739553039679072633473571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15305474772477527022596189 5739553039679072633473571)
            ·
              refine ⟨8609329559518608950210357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5739553039679072633473571 8609329559518608950210357)
              ·
                refine ⟨807124646204869589082221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8609329559518608950210357 807124646204869589082221)
                ·
                  refine ⟨302671742326826095905833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 807124646204869589082221 302671742326826095905833)
                  ·
                    rfl

theorem cell21_1326265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 5, 3].length) (baseStart_1326265 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1326265 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1326265 prefixEnd_1326265 := by exact prefixLift 1326265
  have htrace : WordTrace (prefixWord ++ tailWord_1326265) baseStart_1326265 baseEnd_1326265 := by
    simpa [prefixWord, tailWord_1326265, baseEnd_1326265] using wordTrace_append hprefix tailTrace_1326265
  have hstable : (prefixWord ++ tailWord_1326265).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326265).length < 2 ^ (prefixWord ++ tailWord_1326265).sum := by decide
  have hdescent : baseEnd_1326265 < baseStart_1326265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326434 : List Nat := [3, 3, 2, 1, 1, 1, 4, 3, 3]
def baseStart_1326434 : Nat := 118140960795 + 1326434 * 2 ^ 59
def prefixEnd_1326434 : Nat := 4983230072969 + 3 ^ 40 * 1326434 * 2
def baseEnd_1326434 : Nat := 302710310429319357588821

theorem tailTrace_1326434 : CollatzResearch.WordTrace tailWord_1326434 prefixEnd_1326434 302710310429319357588821 := by
  unfold tailWord_1326434
  simp only [CollatzResearch.WordTrace]
  refine ⟨12094755619140907434196589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32252681651042419824524237 12094755619140907434196589)
  ·
    refine ⟨4535533357177840287823721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12094755619140907434196589 4535533357177840287823721)
    ·
      refine ⟨3401650017883380215867791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4535533357177840287823721 3401650017883380215867791)
      ·
        refine ⟨5102475026825070323801687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3401650017883380215867791 5102475026825070323801687)
        ·
          refine ⟨7653712540237605485702531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5102475026825070323801687 7653712540237605485702531)
          ·
            refine ⟨11480568810356408228553797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7653712540237605485702531 11480568810356408228553797)
            ·
              refine ⟨2152606651941826542853837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11480568810356408228553797 2152606651941826542853837)
              ·
                refine ⟨807227494478184953570189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2152606651941826542853837 807227494478184953570189)
                ·
                  refine ⟨302710310429319357588821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 807227494478184953570189 302710310429319357588821)
                  ·
                    rfl

theorem cell21_1326434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 3, 3].length) (baseStart_1326434 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1326434 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1326434 prefixEnd_1326434 := by exact prefixLift 1326434
  have htrace : WordTrace (prefixWord ++ tailWord_1326434) baseStart_1326434 baseEnd_1326434 := by
    simpa [prefixWord, tailWord_1326434, baseEnd_1326434] using wordTrace_append hprefix tailTrace_1326434
  have hstable : (prefixWord ++ tailWord_1326434).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326434).length < 2 ^ (prefixWord ++ tailWord_1326434).sum := by decide
  have hdescent : baseEnd_1326434 < baseStart_1326434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326445 : List Nat := [1, 5, 1, 1, 1, 4, 8]
def baseStart_1326445 : Nat := 118140960795 + 1326445 * 2 ^ 59
def prefixEnd_1326445 : Nat := 4983230072969 + 3 ^ 40 * 1326445 * 2
def baseEnd_1326445 : Nat := 33634757864353975878385

theorem tailTrace_1326445 : CollatzResearch.WordTrace tailWord_1326445 prefixEnd_1326445 33634757864353975878385 := by
  unfold tailWord_1326445
  simp only [CollatzResearch.WordTrace]
  refine ⟨48379423679523778615436789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32252949119682519076957859 48379423679523778615436789)
  ·
    refine ⟨4535570969955354245197199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48379423679523778615436789 4535570969955354245197199)
    ·
      refine ⟨6803356454933031367795799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4535570969955354245197199 6803356454933031367795799)
      ·
        refine ⟨10205034682399547051693699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6803356454933031367795799 10205034682399547051693699)
        ·
          refine ⟨15307552023599320577540549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10205034682399547051693699 15307552023599320577540549)
          ·
            refine ⟨2870166004424872608288853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15307552023599320577540549 2870166004424872608288853)
            ·
              refine ⟨33634757864353975878385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2870166004424872608288853 33634757864353975878385)
              ·
                rfl

theorem cell21_1326445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 8].length) (baseStart_1326445 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1326445 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1326445 prefixEnd_1326445 := by exact prefixLift 1326445
  have htrace : WordTrace (prefixWord ++ tailWord_1326445) baseStart_1326445 baseEnd_1326445 := by
    simpa [prefixWord, tailWord_1326445, baseEnd_1326445] using wordTrace_append hprefix tailTrace_1326445
  have hstable : (prefixWord ++ tailWord_1326445).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326445).length < 2 ^ (prefixWord ++ tailWord_1326445).sum := by decide
  have hdescent : baseEnd_1326445 < baseStart_1326445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326465 : List Nat := [1, 2, 4, 3, 2, 1, 3, 1, 4]
def baseStart_1326465 : Nat := 118140960795 + 1326465 * 2 ^ 59
def prefixEnd_1326465 : Nat := 4983230072969 + 3 ^ 40 * 1326465 * 2
def baseEnd_1326465 : Nat := 302717385051670192572091

theorem tailTrace_1326465 : CollatzResearch.WordTrace tailWord_1326465 prefixEnd_1326465 302717385051670192572091 := by
  unfold tailWord_1326465
  simp only [CollatzResearch.WordTrace]
  refine ⟨48380153139451322031164849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32253435426300881354109899 48380153139451322031164849)
  ·
    refine ⟨36285114854588491523373637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48380153139451322031164849 36285114854588491523373637)
    ·
      refine ⟨6803459035235342160632557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36285114854588491523373637 6803459035235342160632557)
      ·
        refine ⟨2551297138213253310237209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6803459035235342160632557 2551297138213253310237209)
        ·
          refine ⟨1913472853659939982677907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2551297138213253310237209 1913472853659939982677907)
          ·
            refine ⟨2870209280489909974016861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1913472853659939982677907 2870209280489909974016861)
            ·
              refine ⟨1076328480183716240256323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2870209280489909974016861 1076328480183716240256323)
              ·
                refine ⟨1614492720275574360384485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1076328480183716240256323 1614492720275574360384485)
                ·
                  refine ⟨302717385051670192572091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1614492720275574360384485 302717385051670192572091)
                  ·
                    rfl

theorem cell21_1326465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 3, 1, 4].length) (baseStart_1326465 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1326465 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1326465 prefixEnd_1326465 := by exact prefixLift 1326465
  have htrace : WordTrace (prefixWord ++ tailWord_1326465) baseStart_1326465 baseEnd_1326465 := by
    simpa [prefixWord, tailWord_1326465, baseEnd_1326465] using wordTrace_append hprefix tailTrace_1326465
  have hstable : (prefixWord ++ tailWord_1326465).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326465).length < 2 ^ (prefixWord ++ tailWord_1326465).sum := by decide
  have hdescent : baseEnd_1326465 < baseStart_1326465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326490 : List Nat := [3, 1, 1, 4, 1, 1, 1, 1, 8]
def baseStart_1326490 : Nat := 118140960795 + 1326490 * 2 ^ 59
def prefixEnd_1326490 : Nat := 4983230072969 + 3 ^ 40 * 1326490 * 2
def baseEnd_1326490 : Nat := 302723090392275704655373

theorem tailTrace_1326490 : CollatzResearch.WordTrace tailWord_1326490 prefixEnd_1326490 302723090392275704655373 := by
  unfold tailWord_1326490
  simp only [CollatzResearch.WordTrace]
  refine ⟨12095266241090187825206231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32254043309573834200549949 12095266241090187825206231)
  ·
    refine ⟨18142899361635281737809347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12095266241090187825206231 18142899361635281737809347)
    ·
      refine ⟨27214349042452922606714021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18142899361635281737809347 27214349042452922606714021)
      ·
        refine ⟨5102690445459922988758879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27214349042452922606714021 5102690445459922988758879)
        ·
          refine ⟨7654035668189884483138319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5102690445459922988758879 7654035668189884483138319)
          ·
            refine ⟨11481053502284826724707479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7654035668189884483138319 11481053502284826724707479)
            ·
              refine ⟨17221580253427240087061219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11481053502284826724707479 17221580253427240087061219)
              ·
                refine ⟨25832370380140860130591829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17221580253427240087061219 25832370380140860130591829)
                ·
                  refine ⟨302723090392275704655373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25832370380140860130591829 302723090392275704655373)
                  ·
                    rfl

theorem cell21_1326490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 8].length) (baseStart_1326490 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1326490 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1326490 prefixEnd_1326490 := by exact prefixLift 1326490
  have htrace : WordTrace (prefixWord ++ tailWord_1326490) baseStart_1326490 baseEnd_1326490 := by
    simpa [prefixWord, tailWord_1326490, baseEnd_1326490] using wordTrace_append hprefix tailTrace_1326490
  have hstable : (prefixWord ++ tailWord_1326490).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326490).length < 2 ^ (prefixWord ++ tailWord_1326490).sum := by decide
  have hdescent : baseEnd_1326490 < baseStart_1326490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326524 : List Nat := [2, 2, 2, 4, 2, 1, 1, 3, 4]
def baseStart_1326524 : Nat := 118140960795 + 1326524 * 2 ^ 59
def prefixEnd_1326524 : Nat := 4983230072969 + 3 ^ 40 * 1326524 * 2
def baseEnd_1326524 : Nat := 302730849655499201088637

theorem tailTrace_1326524 : CollatzResearch.WordTrace tailWord_1326524 prefixEnd_1326524 302730849655499201088637 := by
  unfold tailWord_1326524
  simp only [CollatzResearch.WordTrace]
  refine ⟨24191152523118787553781313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32254870030825050071708417 24191152523118787553781313)
  ·
    refine ⟨18143364392339090665335985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24191152523118787553781313 18143364392339090665335985)
    ·
      refine ⟨13607523294254317999001989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18143364392339090665335985 13607523294254317999001989)
      ·
        refine ⟨2551410617672684624812873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13607523294254317999001989 2551410617672684624812873)
        ·
          refine ⟨1913557963254513468609655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2551410617672684624812873 1913557963254513468609655)
          ·
            refine ⟨2870336944881770202914483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1913557963254513468609655 2870336944881770202914483)
            ·
              refine ⟨4305505417322655304371725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2870336944881770202914483 4305505417322655304371725)
              ·
                refine ⟨1614564531495995739139397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4305505417322655304371725 1614564531495995739139397)
                ·
                  refine ⟨302730849655499201088637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1614564531495995739139397 302730849655499201088637)
                  ·
                    rfl

theorem cell21_1326524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 3, 4].length) (baseStart_1326524 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1326524 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1326524 prefixEnd_1326524 := by exact prefixLift 1326524
  have htrace : WordTrace (prefixWord ++ tailWord_1326524) baseStart_1326524 baseEnd_1326524 := by
    simpa [prefixWord, tailWord_1326524, baseEnd_1326524] using wordTrace_append hprefix tailTrace_1326524
  have hstable : (prefixWord ++ tailWord_1326524).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326524).length < 2 ^ (prefixWord ++ tailWord_1326524).sum := by decide
  have hdescent : baseEnd_1326524 < baseStart_1326524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326535 : List Nat := [1, 1, 4, 1, 1, 3, 2, 1, 7]
def baseStart_1326535 : Nat := 118140960795 + 1326535 * 2 ^ 59
def prefixEnd_1326535 : Nat := 4983230072969 + 3 ^ 40 * 1326535 * 2
def baseEnd_1326535 : Nat := 302733360005365626405281

theorem tailTrace_1326535 : CollatzResearch.WordTrace tailWord_1326535 prefixEnd_1326535 302733360005365626405281 := by
  unfold tailWord_1326535
  simp only [CollatzResearch.WordTrace]
  refine ⟨48382706249197723986213059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32255137499465149324142039 48382706249197723986213059)
  ·
    refine ⟨72574059373796585979319589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48382706249197723986213059 72574059373796585979319589)
    ·
      refine ⟨13607636132586859871122423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72574059373796585979319589 13607636132586859871122423)
      ·
        refine ⟨20411454198880289806683635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13607636132586859871122423 20411454198880289806683635)
        ·
          refine ⟨30617181298320434710025453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20411454198880289806683635 30617181298320434710025453)
          ·
            refine ⟨11481442986870163016259545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30617181298320434710025453 11481442986870163016259545)
            ·
              refine ⟨8611082240152622262194659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11481442986870163016259545 8611082240152622262194659)
              ·
                refine ⟨12916623360228933393291989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8611082240152622262194659 12916623360228933393291989)
                ·
                  refine ⟨302733360005365626405281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12916623360228933393291989 302733360005365626405281)
                  ·
                    rfl

theorem cell21_1326535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 7].length) (baseStart_1326535 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1326535 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1326535 prefixEnd_1326535 := by exact prefixLift 1326535
  have htrace : WordTrace (prefixWord ++ tailWord_1326535) baseStart_1326535 baseEnd_1326535 := by
    simpa [prefixWord, tailWord_1326535, baseEnd_1326535] using wordTrace_append hprefix tailTrace_1326535
  have hstable : (prefixWord ++ tailWord_1326535).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326535).length < 2 ^ (prefixWord ++ tailWord_1326535).sum := by decide
  have hdescent : baseEnd_1326535 < baseStart_1326535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326738 : List Nat := [3, 2, 3, 1, 3, 1, 1, 4, 3]
def baseStart_1326738 : Nat := 118140960795 + 1326738 * 2 ^ 59
def prefixEnd_1326738 : Nat := 4983230072969 + 3 ^ 40 * 1326738 * 2
def baseEnd_1326738 : Nat := 302779687371082384521533

theorem tailTrace_1326738 : CollatzResearch.WordTrace tailWord_1326738 prefixEnd_1326738 302779687371082384521533 := by
  unfold tailWord_1326738
  simp only [CollatzResearch.WordTrace]
  refine ⟨12097527566865572413963217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32260073511641526437235245 12097527566865572413963217)
  ·
    refine ⟨9073145675149179310472413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12097527566865572413963217 9073145675149179310472413)
    ·
      refine ⟨3402429628180942241427155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9073145675149179310472413 3402429628180942241427155)
      ·
        refine ⟨5103644442271413362140733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3402429628180942241427155 5103644442271413362140733)
        ·
          refine ⟨1913866665851780010802775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5103644442271413362140733 1913866665851780010802775)
          ·
            refine ⟨2870799998777670016204163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1913866665851780010802775 2870799998777670016204163)
            ·
              refine ⟨4306199998166505024306245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2870799998777670016204163 4306199998166505024306245)
              ·
                refine ⟨807412499656219692057421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4306199998166505024306245 807412499656219692057421)
                ·
                  refine ⟨302779687371082384521533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 807412499656219692057421 302779687371082384521533)
                  ·
                    rfl

theorem cell21_1326738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 4, 3].length) (baseStart_1326738 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1326738 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1326738 prefixEnd_1326738 := by exact prefixLift 1326738
  have htrace : WordTrace (prefixWord ++ tailWord_1326738) baseStart_1326738 baseEnd_1326738 := by
    simpa [prefixWord, tailWord_1326738, baseEnd_1326738] using wordTrace_append hprefix tailTrace_1326738
  have hstable : (prefixWord ++ tailWord_1326738).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326738).length < 2 ^ (prefixWord ++ tailWord_1326738).sum := by decide
  have hdescent : baseEnd_1326738 < baseStart_1326738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326797 : List Nat := [1, 6, 2, 1, 1, 1, 1, 3, 5]
def baseStart_1326797 : Nat := 118140960795 + 1326797 * 2 ^ 59
def prefixEnd_1326797 : Nat := 4983230072969 + 3 ^ 40 * 1326797 * 2
def baseEnd_1326797 : Nat := 302793151974911393038079

theorem tailTrace_1326797 : CollatzResearch.WordTrace tailWord_1326797 prefixEnd_1326797 302793151974911393038079 := by
  unfold tailWord_1326797
  simp only [CollatzResearch.WordTrace]
  refine ⟨48392262174248542732250645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32261508116165695154833763 48392262174248542732250645)
  ·
    refine ⟨2268387289417900440574249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 48392262174248542732250645 2268387289417900440574249)
    ·
      refine ⟨1701290467063425330430687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2268387289417900440574249 1701290467063425330430687)
      ·
        refine ⟨2551935700595137995646031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1701290467063425330430687 2551935700595137995646031)
        ·
          refine ⟨3827903550892706993469047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2551935700595137995646031 3827903550892706993469047)
          ·
            refine ⟨5741855326339060490203571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3827903550892706993469047 5741855326339060490203571)
            ·
              refine ⟨8612782989508590735305357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5741855326339060490203571 8612782989508590735305357)
              ·
                refine ⟨3229793621065721525739509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8612782989508590735305357 3229793621065721525739509)
                ·
                  refine ⟨302793151974911393038079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3229793621065721525739509 302793151974911393038079)
                  ·
                    rfl

theorem cell21_1326797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_1326797 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1326797 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1326797 prefixEnd_1326797 := by exact prefixLift 1326797
  have htrace : WordTrace (prefixWord ++ tailWord_1326797) baseStart_1326797 baseEnd_1326797 := by
    simpa [prefixWord, tailWord_1326797, baseEnd_1326797] using wordTrace_append hprefix tailTrace_1326797
  have hstable : (prefixWord ++ tailWord_1326797).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326797).length < 2 ^ (prefixWord ++ tailWord_1326797).sum := by decide
  have hdescent : baseEnd_1326797 < baseStart_1326797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326808 : List Nat := [2, 1, 2, 2, 3, 1, 2, 8]
def baseStart_1326808 : Nat := 118140960795 + 1326808 * 2 ^ 59
def prefixEnd_1326808 : Nat := 4983230072969 + 3 ^ 40 * 1326808 * 2
def baseEnd_1326808 : Nat := 100931887441592606118241

theorem tailTrace_1326808 : CollatzResearch.WordTrace tailWord_1326808 prefixEnd_1326808 100931887441592606118241 := by
  unfold tailWord_1326808
  simp only [CollatzResearch.WordTrace]
  refine ⟨24196331688604345805450539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32261775584805794407267385 24196331688604345805450539)
  ·
    refine ⟨36294497532906518708175809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24196331688604345805450539 36294497532906518708175809)
    ·
      refine ⟨27220873149679889031131857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36294497532906518708175809 27220873149679889031131857)
      ·
        refine ⟨20415654862259916773348893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27220873149679889031131857 20415654862259916773348893)
        ·
          refine ⟨7655870573347468790005835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20415654862259916773348893 7655870573347468790005835)
          ·
            refine ⟨11483805860021203185008753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7655870573347468790005835 11483805860021203185008753)
            ·
              refine ⟨8612854395015902388756565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11483805860021203185008753 8612854395015902388756565)
              ·
                refine ⟨100931887441592606118241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8612854395015902388756565 100931887441592606118241)
                ·
                  rfl

theorem cell21_1326808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 8].length) (baseStart_1326808 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1326808 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1326808 prefixEnd_1326808 := by exact prefixLift 1326808
  have htrace : WordTrace (prefixWord ++ tailWord_1326808) baseStart_1326808 baseEnd_1326808 := by
    simpa [prefixWord, tailWord_1326808, baseEnd_1326808] using wordTrace_append hprefix tailTrace_1326808
  have hstable : (prefixWord ++ tailWord_1326808).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326808).length < 2 ^ (prefixWord ++ tailWord_1326808).sum := by decide
  have hdescent : baseEnd_1326808 < baseStart_1326808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326901 : List Nat := [1, 3, 3, 1, 5, 8]
def baseStart_1326901 : Nat := 118140960795 + 1326901 * 2 ^ 59
def prefixEnd_1326901 : Nat := 4983230072969 + 3 ^ 40 * 1326901 * 2
def baseEnd_1326901 : Nat := 11215440229327049011279

theorem tailTrace_1326901 : CollatzResearch.WordTrace tailWord_1326901 prefixEnd_1326901 11215440229327049011279 := by
  unfold tailWord_1326901
  simp only [CollatzResearch.WordTrace]
  refine ⟨48396055365871768494036557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32264036910581178996024371 48396055365871768494036557)
  ·
    refine ⟨18148520762201913185263709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48396055365871768494036557 18148520762201913185263709)
    ·
      refine ⟨6805695285825717444473891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18148520762201913185263709 6805695285825717444473891)
      ·
        refine ⟨10208542928738576166710837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6805695285825717444473891 10208542928738576166710837)
        ·
          refine ⟨957050899569241515629141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10208542928738576166710837 957050899569241515629141)
          ·
            refine ⟨11215440229327049011279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 957050899569241515629141 11215440229327049011279)
            ·
              rfl

theorem cell21_1326901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 8].length) (baseStart_1326901 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1326901 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1326901 prefixEnd_1326901 := by exact prefixLift 1326901
  have htrace : WordTrace (prefixWord ++ tailWord_1326901) baseStart_1326901 baseEnd_1326901 := by
    simpa [prefixWord, tailWord_1326901, baseEnd_1326901] using wordTrace_append hprefix tailTrace_1326901
  have hstable : (prefixWord ++ tailWord_1326901).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326901).length < 2 ^ (prefixWord ++ tailWord_1326901).sum := by decide
  have hdescent : baseEnd_1326901 < baseStart_1326901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326932 : List Nat := [2, 4, 1, 1, 3, 2, 1, 2, 5]
def baseStart_1326932 : Nat := 118140960795 + 1326932 * 2 ^ 59
def prefixEnd_1326932 : Nat := 4983230072969 + 3 ^ 40 * 1326932 * 2
def baseEnd_1326932 : Nat := 302823960814181158287803

theorem tailTrace_1326932 : CollatzResearch.WordTrace tailWord_1326932 prefixEnd_1326932 302823960814181158287803 := by
  unfold tailWord_1326932
  simp only [CollatzResearch.WordTrace]
  refine ⟨24198593014379730394207525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32264790685839640525610033 24198593014379730394207525)
  ·
    refine ⟨4537236190196199448913911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24198593014379730394207525 4537236190196199448913911)
    ·
      refine ⟨6805854285294299173370867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4537236190196199448913911 6805854285294299173370867)
      ·
        refine ⟨10208781427941448760056301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6805854285294299173370867 10208781427941448760056301)
        ·
          refine ⟨3828293035478043285021113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10208781427941448760056301 3828293035478043285021113)
          ·
            refine ⟨2871219776608532463765835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3828293035478043285021113 2871219776608532463765835)
            ·
              refine ⟨4306829664912798695648753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2871219776608532463765835 4306829664912798695648753)
              ·
                refine ⟨3230122248684599021736565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4306829664912798695648753 3230122248684599021736565)
                ·
                  refine ⟨302823960814181158287803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3230122248684599021736565 302823960814181158287803)
                  ·
                    rfl

theorem cell21_1326932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_1326932 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1326932 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1326932 prefixEnd_1326932 := by exact prefixLift 1326932
  have htrace : WordTrace (prefixWord ++ tailWord_1326932) baseStart_1326932 baseEnd_1326932 := by
    simpa [prefixWord, tailWord_1326932, baseEnd_1326932] using wordTrace_append hprefix tailTrace_1326932
  have hstable : (prefixWord ++ tailWord_1326932).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326932).length < 2 ^ (prefixWord ++ tailWord_1326932).sum := by decide
  have hdescent : baseEnd_1326932 < baseStart_1326932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1326994 : List Nat := [3, 2, 3, 2, 1, 1, 4, 5]
def baseStart_1326994 : Nat := 118140960795 + 1326994 * 2 ^ 59
def prefixEnd_1326994 : Nat := 4983230072969 + 3 ^ 40 * 1326994 * 2
def baseEnd_1326994 : Nat := 100946036686294276084781

theorem tailTrace_1326994 : CollatzResearch.WordTrace tailWord_1326994 prefixEnd_1326994 100946036686294276084781 := by
  unfold tailWord_1326994
  simp only [CollatzResearch.WordTrace]
  refine ⟨12099861838633711344293009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32266298236356563584781357 12099861838633711344293009)
  ·
    refine ⟨9074896378975283508219757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12099861838633711344293009 9074896378975283508219757)
    ·
      refine ⟨3403086142115731315582409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9074896378975283508219757 3403086142115731315582409)
      ·
        refine ⟨2552314606586798486686807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3403086142115731315582409 2552314606586798486686807)
        ·
          refine ⟨3828471909880197730030211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2552314606586798486686807 3828471909880197730030211)
          ·
            refine ⟨5742707864820296595045317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3828471909880197730030211 5742707864820296595045317)
            ·
              refine ⟨1076757724653805611570997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5742707864820296595045317 1076757724653805611570997)
              ·
                refine ⟨100946036686294276084781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1076757724653805611570997 100946036686294276084781)
                ·
                  rfl

theorem cell21_1326994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 4, 5].length) (baseStart_1326994 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1326994 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1326994 prefixEnd_1326994 := by exact prefixLift 1326994
  have htrace : WordTrace (prefixWord ++ tailWord_1326994) baseStart_1326994 baseEnd_1326994 := by
    simpa [prefixWord, tailWord_1326994, baseEnd_1326994] using wordTrace_append hprefix tailTrace_1326994
  have hstable : (prefixWord ++ tailWord_1326994).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1326994).length < 2 ^ (prefixWord ++ tailWord_1326994).sum := by decide
  have hdescent : baseEnd_1326994 < baseStart_1326994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1326994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327236 : List Nat := [2, 3, 2, 1, 2, 1, 2, 5, 3]
def baseStart_1327236 : Nat := 118140960795 + 1327236 * 2 ^ 59
def prefixEnd_1327236 : Nat := 4983230072969 + 3 ^ 40 * 1327236 * 2
def baseEnd_1327236 : Nat := 302893337755944185220515

theorem tailTrace_1327236 : CollatzResearch.WordTrace tailWord_1327236 prefixEnd_1327236 302893337755944185220515 := by
  unfold tailWord_1327236
  simp only [CollatzResearch.WordTrace]
  refine ⟨24204136909829060353740781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32272182546438747138321041 24204136909829060353740781)
  ·
    refine ⟨9076551341185897632652793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24204136909829060353740781 9076551341185897632652793)
    ·
      refine ⟨6807413505889423224489595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9076551341185897632652793 6807413505889423224489595)
      ·
        refine ⟨10211120258834134836734393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6807413505889423224489595 10211120258834134836734393)
        ·
          refine ⟨7658340194125601127550795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10211120258834134836734393 7658340194125601127550795)
          ·
            refine ⟨11487510291188401691326193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7658340194125601127550795 11487510291188401691326193)
            ·
              refine ⟨8615632718391301268494645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11487510291188401691326193 8615632718391301268494645)
              ·
                refine ⟨807715567349184493921373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8615632718391301268494645 807715567349184493921373)
                ·
                  refine ⟨302893337755944185220515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 807715567349184493921373 302893337755944185220515)
                  ·
                    rfl

theorem cell21_1327236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 5, 3].length) (baseStart_1327236 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1327236 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1327236 prefixEnd_1327236 := by exact prefixLift 1327236
  have htrace : WordTrace (prefixWord ++ tailWord_1327236) baseStart_1327236 baseEnd_1327236 := by
    simpa [prefixWord, tailWord_1327236, baseEnd_1327236] using wordTrace_append hprefix tailTrace_1327236
  have hstable : (prefixWord ++ tailWord_1327236).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327236).length < 2 ^ (prefixWord ++ tailWord_1327236).sum := by decide
  have hdescent : baseEnd_1327236 < baseStart_1327236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327264 : List Nat := [2, 1, 1, 4, 2, 2, 3, 6]
def baseStart_1327264 : Nat := 118140960795 + 1327264 * 2 ^ 59
def prefixEnd_1327264 : Nat := 4983230072969 + 3 ^ 40 * 1327264 * 2
def baseEnd_1327264 : Nat := 100966575912474119584597

theorem tailTrace_1327264 : CollatzResearch.WordTrace tailWord_1327264 prefixEnd_1327264 100966575912474119584597 := by
  unfold tailWord_1327264
  simp only [CollatzResearch.WordTrace]
  refine ⟨24204647531778340744750423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32272863375704454326333897 24204647531778340744750423)
  ·
    refine ⟨36306971297667511117125635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24204647531778340744750423 36306971297667511117125635)
    ·
      refine ⟨54460456946501266675688453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36306971297667511117125635 54460456946501266675688453)
      ·
        refine ⟨10211335677468987501691585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54460456946501266675688453 10211335677468987501691585)
        ·
          refine ⟨7658501758101740626268689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10211335677468987501691585 7658501758101740626268689)
          ·
            refine ⟨5743876318576305469701517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7658501758101740626268689 5743876318576305469701517)
            ·
              refine ⟨2153953619466114551138069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5743876318576305469701517 2153953619466114551138069)
              ·
                refine ⟨100966575912474119584597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2153953619466114551138069 100966575912474119584597)
                ·
                  rfl

theorem cell21_1327264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 6].length) (baseStart_1327264 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1327264 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1327264 prefixEnd_1327264 := by exact prefixLift 1327264
  have htrace : WordTrace (prefixWord ++ tailWord_1327264) baseStart_1327264 baseEnd_1327264 := by
    simpa [prefixWord, tailWord_1327264, baseEnd_1327264] using wordTrace_append hprefix tailTrace_1327264
  have hstable : (prefixWord ++ tailWord_1327264).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327264).length < 2 ^ (prefixWord ++ tailWord_1327264).sum := by decide
  have hdescent : baseEnd_1327264 < baseStart_1327264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327298 : List Nat := [3, 5, 1, 1, 1, 2, 8]
def baseStart_1327298 : Nat := 118140960795 + 1327298 * 2 ^ 59
def prefixEnd_1327298 : Nat := 4983230072969 + 3 ^ 40 * 1327298 * 2
def baseEnd_1327298 : Nat := 33656387444516206131895

theorem tailTrace_1327298 : CollatzResearch.WordTrace tailWord_1327298 prefixEnd_1327298 33656387444516206131895 := by
  unfold tailWord_1327298
  simp only [CollatzResearch.WordTrace]
  refine ⟨12102633786358376324059637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32273690096955670197492365 12102633786358376324059637)
  ·
    refine ⟨1134621917471097780380591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12102633786358376324059637 1134621917471097780380591)
    ·
      refine ⟨1701932876206646670570887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1134621917471097780380591 1701932876206646670570887)
      ·
        refine ⟨2552899314309970005856331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1701932876206646670570887 2552899314309970005856331)
        ·
          refine ⟨3829348971464955008784497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2552899314309970005856331 3829348971464955008784497)
          ·
            refine ⟨2872011728598716256588373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3829348971464955008784497 2872011728598716256588373)
            ·
              refine ⟨33656387444516206131895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2872011728598716256588373 33656387444516206131895)
              ·
                rfl

theorem cell21_1327298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 8].length) (baseStart_1327298 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1327298 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1327298 prefixEnd_1327298 := by exact prefixLift 1327298
  have htrace : WordTrace (prefixWord ++ tailWord_1327298) baseStart_1327298 baseEnd_1327298 := by
    simpa [prefixWord, tailWord_1327298, baseEnd_1327298] using wordTrace_append hprefix tailTrace_1327298
  have hstable : (prefixWord ++ tailWord_1327298).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327298).length < 2 ^ (prefixWord ++ tailWord_1327298).sum := by decide
  have hdescent : baseEnd_1327298 < baseStart_1327298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327422 : List Nat := [4, 2, 1, 2, 1, 4, 2, 2, 3]
def baseStart_1327422 : Nat := 118140960795 + 1327422 * 2 ^ 59
def prefixEnd_1327422 : Nat := 4983230072969 + 3 ^ 40 * 1327422 * 2
def baseEnd_1327422 : Nat := 302935785490049195120135

theorem tailTrace_1327422 : CollatzResearch.WordTrace tailWord_1327422 prefixEnd_1327422 302935785490049195120135 := by
  unfold tailWord_1327422
  simp only [CollatzResearch.WordTrace]
  refine ⟨6051882224623034309219065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32276705197989516315835013 6051882224623034309219065)
  ·
    refine ⟨4538911668467275731914299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6051882224623034309219065 4538911668467275731914299)
    ·
      refine ⟨6808367502700913597871449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4538911668467275731914299 6808367502700913597871449)
      ·
        refine ⟨5106275627025685198403587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6808367502700913597871449 5106275627025685198403587)
        ·
          refine ⟨7659413440538527797605381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5106275627025685198403587 7659413440538527797605381)
          ·
            refine ⟨1436140020100973962051009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7659413440538527797605381 1436140020100973962051009)
            ·
              refine ⟨1077105015075730471538257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1436140020100973962051009 1077105015075730471538257)
              ·
                refine ⟨807828761306797853653693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1077105015075730471538257 807828761306797853653693)
                ·
                  refine ⟨302935785490049195120135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 807828761306797853653693 302935785490049195120135)
                  ·
                    rfl

theorem cell21_1327422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 2, 2, 3].length) (baseStart_1327422 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1327422 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1327422 prefixEnd_1327422 := by exact prefixLift 1327422
  have htrace : WordTrace (prefixWord ++ tailWord_1327422) baseStart_1327422 baseEnd_1327422 := by
    simpa [prefixWord, tailWord_1327422, baseEnd_1327422] using wordTrace_append hprefix tailTrace_1327422
  have hstable : (prefixWord ++ tailWord_1327422).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327422).length < 2 ^ (prefixWord ++ tailWord_1327422).sum := by decide
  have hdescent : baseEnd_1327422 < baseStart_1327422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327464 : List Nat := [2, 1, 4, 2, 2, 1, 1, 5, 3]
def baseStart_1327464 : Nat := 118140960795 + 1327464 * 2 ^ 59
def prefixEnd_1327464 : Nat := 4983230072969 + 3 ^ 40 * 1327464 * 2
def baseEnd_1327464 : Nat := 302945370462266455420049

theorem tailTrace_1327464 : CollatzResearch.WordTrace tailWord_1327464 prefixEnd_1327464 302945370462266455420049 := by
  unfold tailWord_1327464
  simp only [CollatzResearch.WordTrace]
  refine ⟨24208294831416057823390723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32277726441888077097854297 24208294831416057823390723)
  ·
    refine ⟨36312442247124086735086085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24208294831416057823390723 36312442247124086735086085)
    ·
      refine ⟨6808582921335766262828641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36312442247124086735086085 6808582921335766262828641)
      ·
        refine ⟨5106437191001824697121481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6808582921335766262828641 5106437191001824697121481)
        ·
          refine ⟨3829827893251368522841111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5106437191001824697121481 3829827893251368522841111)
          ·
            refine ⟨5744741839877052784261667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3829827893251368522841111 5744741839877052784261667)
            ·
              refine ⟨8617112759815579176392501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5744741839877052784261667 8617112759815579176392501)
              ·
                refine ⟨807854321232710547786797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8617112759815579176392501 807854321232710547786797)
                ·
                  refine ⟨302945370462266455420049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 807854321232710547786797 302945370462266455420049)
                  ·
                    rfl

theorem cell21_1327464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 5, 3].length) (baseStart_1327464 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1327464 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1327464 prefixEnd_1327464 := by exact prefixLift 1327464
  have htrace : WordTrace (prefixWord ++ tailWord_1327464) baseStart_1327464 baseEnd_1327464 := by
    simpa [prefixWord, tailWord_1327464, baseEnd_1327464] using wordTrace_append hprefix tailTrace_1327464
  have hstable : (prefixWord ++ tailWord_1327464).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327464).length < 2 ^ (prefixWord ++ tailWord_1327464).sum := by decide
  have hdescent : baseEnd_1327464 < baseStart_1327464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327537 : List Nat := [1, 2, 2, 4, 1, 2, 2, 1, 6]
def baseStart_1327537 : Nat := 118140960795 + 1327537 * 2 ^ 59
def prefixEnd_1327537 : Nat := 4983230072969 + 3 ^ 40 * 1327537 * 2
def baseEnd_1327537 : Nat := 302962030056834550703233

theorem tailTrace_1327537 : CollatzResearch.WordTrace tailWord_1327537 prefixEnd_1327537 302962030056834550703233 := by
  unfold tailWord_1327537
  simp only [CollatzResearch.WordTrace]
  refine ⟨48419252191567649114188865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32279501461045099409459243 48419252191567649114188865)
  ·
    refine ⟨36314439143675736835641649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48419252191567649114188865 36314439143675736835641649)
    ·
      refine ⟨27235829357756802626731237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36314439143675736835641649 27235829357756802626731237)
      ·
        refine ⟨5106718004579400492512107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27235829357756802626731237 5106718004579400492512107)
        ·
          refine ⟨7660077006869100738768161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5106718004579400492512107 7660077006869100738768161)
          ·
            refine ⟨5745057755151825554076121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7660077006869100738768161 5745057755151825554076121)
            ·
              refine ⟨4308793316363869165557091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5745057755151825554076121 4308793316363869165557091)
              ·
                refine ⟨6463189974545803748335637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4308793316363869165557091 6463189974545803748335637)
                ·
                  refine ⟨302962030056834550703233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6463189974545803748335637 302962030056834550703233)
                  ·
                    rfl

theorem cell21_1327537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 1, 6].length) (baseStart_1327537 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1327537 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1327537 prefixEnd_1327537 := by exact prefixLift 1327537
  have htrace : WordTrace (prefixWord ++ tailWord_1327537) baseStart_1327537 baseEnd_1327537 := by
    simpa [prefixWord, tailWord_1327537, baseEnd_1327537] using wordTrace_append hprefix tailTrace_1327537
  have hstable : (prefixWord ++ tailWord_1327537).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327537).length < 2 ^ (prefixWord ++ tailWord_1327537).sum := by decide
  have hdescent : baseEnd_1327537 < baseStart_1327537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327602 : List Nat := [3, 2, 1, 4, 3, 1, 1, 6]
def baseStart_1327602 : Nat := 118140960795 + 1327602 * 2 ^ 59
def prefixEnd_1327602 : Nat := 4983230072969 + 3 ^ 40 * 1327602 * 2
def baseEnd_1327602 : Nat := 100992287980802960706589

theorem tailTrace_1327602 : CollatzResearch.WordTrace tailWord_1327602 prefixEnd_1327602 100992287980802960706589 := by
  unfold tailWord_1327602
  simp only [CollatzResearch.WordTrace]
  refine ⟨12105405734083041303826265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32281081957554776810203373 12105405734083041303826265)
  ·
    refine ⟨9079054300562280977869699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12105405734083041303826265 9079054300562280977869699)
    ·
      refine ⟨13618581450843421466804549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9079054300562280977869699 13618581450843421466804549)
      ·
        refine ⟨2553484022033141525025853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13618581450843421466804549 2553484022033141525025853)
        ·
          refine ⟨957556508262428071884695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2553484022033141525025853 957556508262428071884695)
          ·
            refine ⟨1436334762393642107827043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 957556508262428071884695 1436334762393642107827043)
            ·
              refine ⟨2154502143590463161740565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1436334762393642107827043 2154502143590463161740565)
              ·
                refine ⟨100992287980802960706589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2154502143590463161740565 100992287980802960706589)
                ·
                  rfl

theorem cell21_1327602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 6].length) (baseStart_1327602 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1327602 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1327602 prefixEnd_1327602 := by exact prefixLift 1327602
  have htrace : WordTrace (prefixWord ++ tailWord_1327602) baseStart_1327602 baseEnd_1327602 := by
    simpa [prefixWord, tailWord_1327602, baseEnd_1327602] using wordTrace_append hprefix tailTrace_1327602
  have hstable : (prefixWord ++ tailWord_1327602).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327602).length < 2 ^ (prefixWord ++ tailWord_1327602).sum := by decide
  have hdescent : baseEnd_1327602 < baseStart_1327602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327613 : List Nat := [1, 4, 1, 1, 1, 3, 1, 5, 4]
def baseStart_1327613 : Nat := 118140960795 + 1327613 * 2 ^ 59
def prefixEnd_1327613 : Nat := 4983230072969 + 3 ^ 40 * 1327613 * 2
def baseEnd_1327613 : Nat := 302979374292275307436411

theorem tailTrace_1327613 : CollatzResearch.WordTrace tailWord_1327613 prefixEnd_1327613 302979374292275307436411 := by
  unfold tailWord_1327613
  simp only [CollatzResearch.WordTrace]
  refine ⟨48422024139292314093955493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32281349426194876062636995 48422024139292314093955493)
  ·
    refine ⟨9079129526117308892616655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48422024139292314093955493 9079129526117308892616655)
    ·
      refine ⟨13618694289175963338924983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9079129526117308892616655 13618694289175963338924983)
      ·
        refine ⟨20428041433763945008387475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13618694289175963338924983 20428041433763945008387475)
        ·
          refine ⟨30642062150645917512581213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20428041433763945008387475 30642062150645917512581213)
          ·
            refine ⟨11490773306492219067217955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30642062150645917512581213 11490773306492219067217955)
            ·
              refine ⟨17236159959738328600826933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11490773306492219067217955 17236159959738328600826933)
              ·
                refine ⟨1615889996225468306327525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17236159959738328600826933 1615889996225468306327525)
                ·
                  refine ⟨302979374292275307436411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1615889996225468306327525 302979374292275307436411)
                  ·
                    rfl

theorem cell21_1327613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 5, 4].length) (baseStart_1327613 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1327613 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1327613 prefixEnd_1327613 := by exact prefixLift 1327613
  have htrace : WordTrace (prefixWord ++ tailWord_1327613) baseStart_1327613 baseEnd_1327613 := by
    simpa [prefixWord, tailWord_1327613, baseEnd_1327613] using wordTrace_append hprefix tailTrace_1327613
  have hstable : (prefixWord ++ tailWord_1327613).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327613).length < 2 ^ (prefixWord ++ tailWord_1327613).sum := by decide
  have hdescent : baseEnd_1327613 < baseStart_1327613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327684 : List Nat := [2, 3, 5, 1, 2, 1, 1, 3, 3]
def baseStart_1327684 : Nat := 118140960795 + 1327684 * 2 ^ 59
def prefixEnd_1327684 : Nat := 4983230072969 + 3 ^ 40 * 1327684 * 2
def baseEnd_1327684 : Nat := 302995577459594961752933

theorem tailTrace_1327684 : CollatzResearch.WordTrace tailWord_1327684 prefixEnd_1327684 302995577459594961752933 := by
  unfold tailWord_1327684
  simp only [CollatzResearch.WordTrace]
  refine ⟨24212306861017546609895053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32283075814690062146526737 24212306861017546609895053)
  ·
    refine ⟨9079615072881579978710645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24212306861017546609895053 9079615072881579978710645)
    ·
      refine ⟨851213913082648123004123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9079615072881579978710645 851213913082648123004123)
      ·
        refine ⟨1276820869623972184506185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 851213913082648123004123 1276820869623972184506185)
        ·
          refine ⟨957615652217979138379639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1276820869623972184506185 957615652217979138379639)
          ·
            refine ⟨1436423478326968707569459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 957615652217979138379639 1436423478326968707569459)
            ·
              refine ⟨2154635217490453061354189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1436423478326968707569459 2154635217490453061354189)
              ·
                refine ⟨807988206558919898007821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2154635217490453061354189 807988206558919898007821)
                ·
                  refine ⟨302995577459594961752933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 807988206558919898007821 302995577459594961752933)
                  ·
                    rfl

theorem cell21_1327684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 3, 3].length) (baseStart_1327684 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1327684 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1327684 prefixEnd_1327684 := by exact prefixLift 1327684
  have htrace : WordTrace (prefixWord ++ tailWord_1327684) baseStart_1327684 baseEnd_1327684 := by
    simpa [prefixWord, tailWord_1327684, baseEnd_1327684] using wordTrace_append hprefix tailTrace_1327684
  have hstable : (prefixWord ++ tailWord_1327684).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327684).length < 2 ^ (prefixWord ++ tailWord_1327684).sum := by decide
  have hdescent : baseEnd_1327684 < baseStart_1327684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327751 : List Nat := [1, 1, 4, 2, 1, 2, 2, 5, 3]
def baseStart_1327751 : Nat := 118140960795 + 1327751 * 2 ^ 59
def prefixEnd_1327751 : Nat := 4983230072969 + 3 ^ 40 * 1327751 * 2
def baseEnd_1327751 : Nat := 303010867772417734136129

theorem tailTrace_1327751 : CollatzResearch.WordTrace tailWord_1327751 prefixEnd_1327751 303010867772417734136129 := by
  unfold tailWord_1327751
  simp only [CollatzResearch.WordTrace]
  refine ⟨48427057412792363662479107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32284704941861575774986071 48427057412792363662479107)
  ·
    refine ⟨72640586119188545493718661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48427057412792363662479107 72640586119188545493718661)
    ·
      refine ⟨13620109897347852280072249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72640586119188545493718661 13620109897347852280072249)
      ·
        refine ⟨10215082423010889210054187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13620109897347852280072249 10215082423010889210054187)
        ·
          refine ⟨15322623634516333815081281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10215082423010889210054187 15322623634516333815081281)
          ·
            refine ⟨11491967725887250361310961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15322623634516333815081281 11491967725887250361310961)
            ·
              refine ⟨8618975794415437770983221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11491967725887250361310961 8618975794415437770983221)
              ·
                refine ⟨808028980726447291029677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8618975794415437770983221 808028980726447291029677)
                ·
                  refine ⟨303010867772417734136129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 808028980726447291029677 303010867772417734136129)
                  ·
                    rfl

theorem cell21_1327751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 5, 3].length) (baseStart_1327751 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1327751 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1327751 prefixEnd_1327751 := by exact prefixLift 1327751
  have htrace : WordTrace (prefixWord ++ tailWord_1327751) baseStart_1327751 baseEnd_1327751 := by
    simpa [prefixWord, tailWord_1327751, baseEnd_1327751] using wordTrace_append hprefix tailTrace_1327751
  have hstable : (prefixWord ++ tailWord_1327751).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327751).length < 2 ^ (prefixWord ++ tailWord_1327751).sum := by decide
  have hdescent : baseEnd_1327751 < baseStart_1327751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327855 : List Nat := [1, 1, 2, 1, 5, 3, 1, 7]
def baseStart_1327855 : Nat := 118140960795 + 1327855 * 2 ^ 59
def prefixEnd_1327855 : Nat := 4983230072969 + 3 ^ 40 * 1327855 * 2
def baseEnd_1327855 : Nat := 101011533996445554800861

theorem tailTrace_1327855 : CollatzResearch.WordTrace tailWord_1327855 prefixEnd_1327855 101011533996445554800861 := by
  unfold tailWord_1327855
  simp only [CollatzResearch.WordTrace]
  refine ⟨48430850604415589424265019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32287233736277059616176679 48430850604415589424265019)
  ·
    refine ⟨72646275906623384136397529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48430850604415589424265019 72646275906623384136397529)
    ·
      refine ⟨54484706929967538102298147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72646275906623384136397529 54484706929967538102298147)
      ·
        refine ⟨81727060394951307153447221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54484706929967538102298147 81727060394951307153447221)
        ·
          refine ⟨7661911912026685045635677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 81727060394951307153447221 7661911912026685045635677)
          ·
            refine ⟨2873216967010006892113379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7661911912026685045635677 2873216967010006892113379)
            ·
              refine ⟨4309825450515010338170069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2873216967010006892113379 4309825450515010338170069)
              ·
                refine ⟨101011533996445554800861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4309825450515010338170069 101011533996445554800861)
                ·
                  rfl

theorem cell21_1327855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 7].length) (baseStart_1327855 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1327855 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1327855 prefixEnd_1327855 := by exact prefixLift 1327855
  have htrace : WordTrace (prefixWord ++ tailWord_1327855) baseStart_1327855 baseEnd_1327855 := by
    simpa [prefixWord, tailWord_1327855, baseEnd_1327855] using wordTrace_append hprefix tailTrace_1327855
  have hstable : (prefixWord ++ tailWord_1327855).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327855).length < 2 ^ (prefixWord ++ tailWord_1327855).sum := by decide
  have hdescent : baseEnd_1327855 < baseStart_1327855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327937 : List Nat := [1, 2, 5, 3, 1, 1, 1, 4, 3]
def baseStart_1327937 : Nat := 118140960795 + 1327937 * 2 ^ 59
def prefixEnd_1327937 : Nat := 4983230072969 + 3 ^ 40 * 1327937 * 2
def baseEnd_1327937 : Nat := 303053315506522744035749

theorem tailTrace_1327937 : CollatzResearch.WordTrace tailWord_1327937 prefixEnd_1327937 303053315506522744035749 := by
  unfold tailWord_1327937
  simp only [CollatzResearch.WordTrace]
  refine ⟨48433841390118517428750065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32289227593412344952500043 48433841390118517428750065)
  ·
    refine ⟨36325381042588888071562549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48433841390118517428750065 36325381042588888071562549)
    ·
      refine ⟨3405504472742708256708989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36325381042588888071562549 3405504472742708256708989)
      ·
        refine ⟨1277064177278515596265871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3405504472742708256708989 1277064177278515596265871)
        ·
          refine ⟨1915596265917773394398807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1277064177278515596265871 1915596265917773394398807)
          ·
            refine ⟨2873394398876660091598211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1915596265917773394398807 2873394398876660091598211)
            ·
              refine ⟨4310091598314990137397317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2873394398876660091598211 4310091598314990137397317)
              ·
                refine ⟨808142174684060650761997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4310091598314990137397317 808142174684060650761997)
                ·
                  refine ⟨303053315506522744035749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 808142174684060650761997 303053315506522744035749)
                  ·
                    rfl

theorem cell21_1327937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 4, 3].length) (baseStart_1327937 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1327937 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1327937 prefixEnd_1327937 := by exact prefixLift 1327937
  have htrace : WordTrace (prefixWord ++ tailWord_1327937) baseStart_1327937 baseEnd_1327937 := by
    simpa [prefixWord, tailWord_1327937, baseEnd_1327937] using wordTrace_append hprefix tailTrace_1327937
  have hstable : (prefixWord ++ tailWord_1327937).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327937).length < 2 ^ (prefixWord ++ tailWord_1327937).sum := by decide
  have hdescent : baseEnd_1327937 < baseStart_1327937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327948 : List Nat := [2, 2, 1, 3, 3, 3, 1, 6]
def baseStart_1327948 : Nat := 118140960795 + 1327948 * 2 ^ 59
def prefixEnd_1327948 : Nat := 4983230072969 + 3 ^ 40 * 1327948 * 2
def baseEnd_1327948 : Nat := 101018608618796389784131

theorem tailTrace_1327948 : CollatzResearch.WordTrace tailWord_1327948 prefixEnd_1327948 101018608618796389784131 := by
  unfold tailWord_1327948
  simp only [CollatzResearch.WordTrace]
  refine ⟨24217121296539333153700249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32289495062052444204933665 24217121296539333153700249)
  ·
    refine ⟨18162840972404499865275187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24217121296539333153700249 18162840972404499865275187)
    ·
      refine ⟨27244261458606749797912781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18162840972404499865275187 27244261458606749797912781)
      ·
        refine ⟨10216598046977531174217293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27244261458606749797912781 10216598046977531174217293)
        ·
          refine ⟨3831224267616574190331485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10216598046977531174217293 3831224267616574190331485)
          ·
            refine ⟨1436709100356215321374307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3831224267616574190331485 1436709100356215321374307)
            ·
              refine ⟨2155063650534322982061461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1436709100356215321374307 2155063650534322982061461)
              ·
                refine ⟨101018608618796389784131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2155063650534322982061461 101018608618796389784131)
                ·
                  rfl

theorem cell21_1327948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 6].length) (baseStart_1327948 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1327948 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1327948 prefixEnd_1327948 := by exact prefixLift 1327948
  have htrace : WordTrace (prefixWord ++ tailWord_1327948) baseStart_1327948 baseEnd_1327948 := by
    simpa [prefixWord, tailWord_1327948, baseEnd_1327948] using wordTrace_append hprefix tailTrace_1327948
  have hstable : (prefixWord ++ tailWord_1327948).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327948).length < 2 ^ (prefixWord ++ tailWord_1327948).sum := by decide
  have hdescent : baseEnd_1327948 < baseStart_1327948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327962 : List Nat := [3, 1, 1, 2, 1, 5, 1, 2, 5]
def baseStart_1327962 : Nat := 118140960795 + 1327962 * 2 ^ 59
def prefixEnd_1327962 : Nat := 4983230072969 + 3 ^ 40 * 1327962 * 2
def baseEnd_1327962 : Nat := 303059020847128256119031

theorem tailTrace_1327962 : CollatzResearch.WordTrace tailWord_1327962 prefixEnd_1327962 303059020847128256119031 := by
  unfold tailWord_1327962
  simp only [CollatzResearch.WordTrace]
  refine ⟨12108688303756986674602535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32289835476685297798940093 12108688303756986674602535)
  ·
    refine ⟨18163032455635480011903803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12108688303756986674602535 18163032455635480011903803)
    ·
      refine ⟨27244548683453220017855705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18163032455635480011903803 27244548683453220017855705)
      ·
        refine ⟨20433411512589915013391779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27244548683453220017855705 20433411512589915013391779)
        ·
          refine ⟨30650117268884872520087669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20433411512589915013391779 30650117268884872520087669)
          ·
            refine ⟨2873448493957956798758219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30650117268884872520087669 2873448493957956798758219)
            ·
              refine ⟨4310172740936935198137329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2873448493957956798758219 4310172740936935198137329)
              ·
                refine ⟨3232629555702701398602997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4310172740936935198137329 3232629555702701398602997)
                ·
                  refine ⟨303059020847128256119031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3232629555702701398602997 303059020847128256119031)
                  ·
                    rfl

theorem cell21_1327962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 2, 5].length) (baseStart_1327962 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1327962 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1327962 prefixEnd_1327962 := by exact prefixLift 1327962
  have htrace : WordTrace (prefixWord ++ tailWord_1327962) baseStart_1327962 baseEnd_1327962 := by
    simpa [prefixWord, tailWord_1327962, baseEnd_1327962] using wordTrace_append hprefix tailTrace_1327962
  have hstable : (prefixWord ++ tailWord_1327962).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327962).length < 2 ^ (prefixWord ++ tailWord_1327962).sum := by decide
  have hdescent : baseEnd_1327962 < baseStart_1327962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1327993 : List Nat := [1, 2, 1, 3, 2, 3, 3, 2, 4]
def baseStart_1327993 : Nat := 118140960795 + 1327993 * 2 ^ 59
def prefixEnd_1327993 : Nat := 4983230072969 + 3 ^ 40 * 1327993 * 2
def baseEnd_1327993 : Nat := 303066095469479091102301

theorem tailTrace_1327993 : CollatzResearch.WordTrace tailWord_1327993 prefixEnd_1327993 303066095469479091102301 := by
  unfold tailWord_1327993
  simp only [CollatzResearch.WordTrace]
  refine ⟨48435883877915638992788633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32290589251943759328525755 48435883877915638992788633)
  ·
    refine ⟨36326912908436729244591475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48435883877915638992788633 36326912908436729244591475)
    ·
      refine ⟨54490369362655093866887213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36326912908436729244591475 54490369362655093866887213)
      ·
        refine ⟨20433888510995660200082705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54490369362655093866887213 20433888510995660200082705)
        ·
          refine ⟨15325416383246745150062029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20433888510995660200082705 15325416383246745150062029)
          ·
            refine ⟨5747031143717529431273261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15325416383246745150062029 5747031143717529431273261)
            ·
              refine ⟨2155136678894073536727473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5747031143717529431273261 2155136678894073536727473)
              ·
                refine ⟨1616352509170555152545605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2155136678894073536727473 1616352509170555152545605)
                ·
                  refine ⟨303066095469479091102301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1616352509170555152545605 303066095469479091102301)
                  ·
                    rfl

theorem cell21_1327993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 2, 4].length) (baseStart_1327993 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1327993 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1327993 prefixEnd_1327993 := by exact prefixLift 1327993
  have htrace : WordTrace (prefixWord ++ tailWord_1327993) baseStart_1327993 baseEnd_1327993 := by
    simpa [prefixWord, tailWord_1327993, baseEnd_1327993] using wordTrace_append hprefix tailTrace_1327993
  have hstable : (prefixWord ++ tailWord_1327993).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1327993).length < 2 ^ (prefixWord ++ tailWord_1327993).sum := by decide
  have hdescent : baseEnd_1327993 < baseStart_1327993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1327993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328162 : List Nat := [3, 3, 1, 1, 1, 5, 1, 2, 4]
def baseStart_1328162 : Nat := 118140960795 + 1328162 * 2 ^ 59
def prefixEnd_1328162 : Nat := 4983230072969 + 3 ^ 40 * 1328162 * 2
def baseEnd_1328162 : Nat := 303104663571972352785289

theorem tailTrace_1328162 : CollatzResearch.WordTrace tailWord_1328162 prefixEnd_1328162 303104663571972352785289 := by
  unfold tailWord_1328162
  simp only [CollatzResearch.WordTrace]
  refine ⟨12110511953575845213922685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32294698542868920570460493 12110511953575845213922685)
  ·
    refine ⟨4541441982590941955221007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12110511953575845213922685 4541441982590941955221007)
    ·
      refine ⟨6812162973886412932831511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4541441982590941955221007 6812162973886412932831511)
      ·
        refine ⟨10218244460829619399247267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6812162973886412932831511 10218244460829619399247267)
        ·
          refine ⟨15327366691244429098870901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10218244460829619399247267 15327366691244429098870901)
          ·
            refine ⟨1436940627304165228019147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15327366691244429098870901 1436940627304165228019147)
            ·
              refine ⟨2155410940956247842028721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1436940627304165228019147 2155410940956247842028721)
              ·
                refine ⟨1616558205717185881521541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2155410940956247842028721 1616558205717185881521541)
                ·
                  refine ⟨303104663571972352785289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1616558205717185881521541 303104663571972352785289)
                  ·
                    rfl

theorem cell21_1328162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_1328162 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1328162 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1328162 prefixEnd_1328162 := by exact prefixLift 1328162
  have htrace : WordTrace (prefixWord ++ tailWord_1328162) baseStart_1328162 baseEnd_1328162 := by
    simpa [prefixWord, tailWord_1328162, baseEnd_1328162] using wordTrace_append hprefix tailTrace_1328162
  have hstable : (prefixWord ++ tailWord_1328162).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328162).length < 2 ^ (prefixWord ++ tailWord_1328162).sum := by decide
  have hdescent : baseEnd_1328162 < baseStart_1328162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328187 : List Nat := [1, 1, 1, 1, 1, 2, 1, 3, 10]
def baseStart_1328187 : Nat := 118140960795 + 1328187 * 2 ^ 59
def prefixEnd_1328187 : Nat := 4983230072969 + 3 ^ 40 * 1328187 * 2
def baseEnd_1328187 : Nat := 303110368912577864868571

theorem tailTrace_1328187 : CollatzResearch.WordTrace tailWord_1328187 prefixEnd_1328187 303110368912577864868571 := by
  unfold tailWord_1328187
  simp only [CollatzResearch.WordTrace]
  refine ⟨48442959639212810125350815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32295306426141873416900543 48442959639212810125350815)
  ·
    refine ⟨72664439458819215188026223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48442959639212810125350815 72664439458819215188026223)
    ·
      refine ⟨108996659188228822782039335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72664439458819215188026223 108996659188228822782039335)
      ·
        refine ⟨163494988782343234173059003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108996659188228822782039335 163494988782343234173059003)
        ·
          refine ⟨245242483173514851259588505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163494988782343234173059003 245242483173514851259588505)
          ·
            refine ⟨183931862380136138444691379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 245242483173514851259588505 183931862380136138444691379)
            ·
              refine ⟨275897793570204207667037069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183931862380136138444691379 275897793570204207667037069)
              ·
                refine ⟨103461672588826577875138901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 275897793570204207667037069 103461672588826577875138901)
                ·
                  refine ⟨303110368912577864868571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 103461672588826577875138901 303110368912577864868571)
                  ·
                    rfl

theorem cell21_1328187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 10].length) (baseStart_1328187 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1328187 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1328187 prefixEnd_1328187 := by exact prefixLift 1328187
  have htrace : WordTrace (prefixWord ++ tailWord_1328187) baseStart_1328187 baseEnd_1328187 := by
    simpa [prefixWord, tailWord_1328187, baseEnd_1328187] using wordTrace_append hprefix tailTrace_1328187
  have hstable : (prefixWord ++ tailWord_1328187).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328187).length < 2 ^ (prefixWord ++ tailWord_1328187).sum := by decide
  have hdescent : baseEnd_1328187 < baseStart_1328187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328193 : List Nat := [1, 2, 5, 1, 3, 2, 2, 5]
def baseStart_1328193 : Nat := 118140960795 + 1328193 * 2 ^ 59
def prefixEnd_1328193 : Nat := 4983230072969 + 3 ^ 40 * 1328193 * 2
def baseEnd_1328193 : Nat := 101037246064774395922853

theorem tailTrace_1328193 : CollatzResearch.WordTrace tailWord_1328193 prefixEnd_1328193 101037246064774395922853 := by
  unfold tailWord_1328193
  simp only [CollatzResearch.WordTrace]
  refine ⟨48443178477191073150069233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32295452318127382100046155 48443178477191073150069233)
  ·
    refine ⟨36332383857893304862551925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48443178477191073150069233 36332383857893304862551925)
    ·
      refine ⟨3406160986677497330864243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36332383857893304862551925 3406160986677497330864243)
      ·
        refine ⟨5109241480016245996296365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3406160986677497330864243 5109241480016245996296365)
        ·
          refine ⟨1915965555006092248611137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5109241480016245996296365 1915965555006092248611137)
          ·
            refine ⟨1436974166254569186458353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1915965555006092248611137 1436974166254569186458353)
            ·
              refine ⟨1077730624690926889843765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1436974166254569186458353 1077730624690926889843765)
              ·
                refine ⟨101037246064774395922853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1077730624690926889843765 101037246064774395922853)
                ·
                  rfl

theorem cell21_1328193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 2, 5].length) (baseStart_1328193 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1328193 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1328193 prefixEnd_1328193 := by exact prefixLift 1328193
  have htrace : WordTrace (prefixWord ++ tailWord_1328193) baseStart_1328193 baseEnd_1328193 := by
    simpa [prefixWord, tailWord_1328193, baseEnd_1328193] using wordTrace_append hprefix tailTrace_1328193
  have hstable : (prefixWord ++ tailWord_1328193).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328193).length < 2 ^ (prefixWord ++ tailWord_1328193).sum := by decide
  have hdescent : baseEnd_1328193 < baseStart_1328193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328238 : List Nat := [4, 1, 2, 2, 1, 2, 4, 1, 4]
def baseStart_1328238 : Nat := 118140960795 + 1328238 * 2 ^ 59
def prefixEnd_1328238 : Nat := 4983230072969 + 3 ^ 40 * 1328238 * 2
def baseEnd_1328238 : Nat := 303122007807413109518467

theorem tailTrace_1328238 : CollatzResearch.WordTrace tailWord_1328238 prefixEnd_1328238 303122007807413109518467 := by
  unfold tailWord_1328238
  simp only [CollatzResearch.WordTrace]
  refine ⟨6055602470253505729432171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32296546508018697223638245 6055602470253505729432171)
  ·
    refine ⟨9083403705380258594148257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6055602470253505729432171 9083403705380258594148257)
    ·
      refine ⟨6812552779035193945611193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9083403705380258594148257 6812552779035193945611193)
      ·
        refine ⟨5109414584276395459208395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6812552779035193945611193 5109414584276395459208395)
        ·
          refine ⟨7664121876414593188812593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5109414584276395459208395 7664121876414593188812593)
          ·
            refine ⟨5748091407310944891609445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7664121876414593188812593 5748091407310944891609445)
            ·
              refine ⟨1077767138870802167176771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5748091407310944891609445 1077767138870802167176771)
              ·
                refine ⟨1616650708306203250765157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1077767138870802167176771 1616650708306203250765157)
                ·
                  refine ⟨303122007807413109518467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1616650708306203250765157 303122007807413109518467)
                  ·
                    rfl

theorem cell21_1328238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 4, 1, 4].length) (baseStart_1328238 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1328238 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1328238 prefixEnd_1328238 := by exact prefixLift 1328238
  have htrace : WordTrace (prefixWord ++ tailWord_1328238) baseStart_1328238 baseEnd_1328238 := by
    simpa [prefixWord, tailWord_1328238, baseEnd_1328238] using wordTrace_append hprefix tailTrace_1328238
  have hstable : (prefixWord ++ tailWord_1328238).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328238).length < 2 ^ (prefixWord ++ tailWord_1328238).sum := by decide
  have hdescent : baseEnd_1328238 < baseStart_1328238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328311 : List Nat := [1, 1, 3, 1, 4, 1, 5, 5]
def baseStart_1328311 : Nat := 118140960795 + 1328311 * 2 ^ 59
def prefixEnd_1328311 : Nat := 4983230072969 + 3 ^ 40 * 1328311 * 2
def baseEnd_1328311 : Nat := 101046222467327068267217

theorem tailTrace_1328311 : CollatzResearch.WordTrace tailWord_1328311 prefixEnd_1328311 101046222467327068267217 := by
  unfold tailWord_1328311
  simp only [CollatzResearch.WordTrace]
  refine ⟨48447482290763579302864787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32298321527175719535243191 48447482290763579302864787)
  ·
    refine ⟨72671223436145368954297181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48447482290763579302864787 72671223436145368954297181)
    ·
      refine ⟨27251708788554513357861443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72671223436145368954297181 27251708788554513357861443)
      ·
        refine ⟨40877563182831770036792165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27251708788554513357861443 40877563182831770036792165)
        ·
          refine ⟨7664543096780956881898531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40877563182831770036792165 7664543096780956881898531)
          ·
            refine ⟨11496814645171435322847797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7664543096780956881898531 11496814645171435322847797)
            ·
              refine ⟨1077826372984822061516981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11496814645171435322847797 1077826372984822061516981)
              ·
                refine ⟨101046222467327068267217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1077826372984822061516981 101046222467327068267217)
                ·
                  rfl

theorem cell21_1328311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 5, 5].length) (baseStart_1328311 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1328311 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1328311 prefixEnd_1328311 := by exact prefixLift 1328311
  have htrace : WordTrace (prefixWord ++ tailWord_1328311) baseStart_1328311 baseEnd_1328311 := by
    simpa [prefixWord, tailWord_1328311, baseEnd_1328311] using wordTrace_append hprefix tailTrace_1328311
  have hstable : (prefixWord ++ tailWord_1328311).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328311).length < 2 ^ (prefixWord ++ tailWord_1328311).sum := by decide
  have hdescent : baseEnd_1328311 < baseStart_1328311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328339 : List Nat := [1, 1, 1, 2, 1, 1, 1, 7, 6]
def baseStart_1328339 : Nat := 118140960795 + 1328339 * 2 ^ 59
def prefixEnd_1328339 : Nat := 4983230072969 + 3 ^ 40 * 1328339 * 2
def baseEnd_1328339 : Nat := 303145057383459378334927

theorem tailTrace_1328339 : CollatzResearch.WordTrace tailWord_1328339 prefixEnd_1328339 303145057383459378334927 := by
  unfold tailWord_1328339
  simp only [CollatzResearch.WordTrace]
  refine ⟨48448503534662140084884071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32299002356441426723256047 48448503534662140084884071)
  ·
    refine ⟨72672755301993210127326107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48448503534662140084884071 72672755301993210127326107)
    ·
      refine ⟨109009132952989815190989161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72672755301993210127326107 109009132952989815190989161)
      ·
        refine ⟨81756849714742361393241871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109009132952989815190989161 81756849714742361393241871)
        ·
          refine ⟨122635274572113542089862807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81756849714742361393241871 122635274572113542089862807)
          ·
            refine ⟨183952911858170313134794211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122635274572113542089862807 183952911858170313134794211)
            ·
              refine ⟨275929367787255469702191317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183952911858170313134794211 275929367787255469702191317)
              ·
                refine ⟨6467094557513800071145109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 275929367787255469702191317 6467094557513800071145109)
                ·
                  refine ⟨303145057383459378334927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6467094557513800071145109 303145057383459378334927)
                  ·
                    rfl

theorem cell21_1328339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7, 6].length) (baseStart_1328339 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1328339 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1328339 prefixEnd_1328339 := by exact prefixLift 1328339
  have htrace : WordTrace (prefixWord ++ tailWord_1328339) baseStart_1328339 baseEnd_1328339 := by
    simpa [prefixWord, tailWord_1328339, baseEnd_1328339] using wordTrace_append hprefix tailTrace_1328339
  have hstable : (prefixWord ++ tailWord_1328339).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328339).length < 2 ^ (prefixWord ++ tailWord_1328339).sum := by decide
  have hdescent : baseEnd_1328339 < baseStart_1328339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328356 : List Nat := [2, 3, 1, 1, 1, 2, 2, 5, 4]
def baseStart_1328356 : Nat := 118140960795 + 1328356 * 2 ^ 59
def prefixEnd_1328356 : Nat := 4983230072969 + 3 ^ 40 * 1328356 * 2
def baseEnd_1328356 : Nat := 303148937015071126551559

theorem tailTrace_1328356 : CollatzResearch.WordTrace tailWord_1328356 prefixEnd_1328356 303148937015071126551559 := by
  unfold tailWord_1328356
  simp only [CollatzResearch.WordTrace]
  refine ⟨24224561787800275994126461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32299415717067034658835281 24224561787800275994126461)
  ·
    refine ⟨9084210670425103497797423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24224561787800275994126461 9084210670425103497797423)
    ·
      refine ⟨13626316005637655246696135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9084210670425103497797423 13626316005637655246696135)
      ·
        refine ⟨20439474008456482870044203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13626316005637655246696135 20439474008456482870044203)
        ·
          refine ⟨30659211012684724305066305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20439474008456482870044203 30659211012684724305066305)
          ·
            refine ⟨22994408259513543228799729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30659211012684724305066305 22994408259513543228799729)
            ·
              refine ⟨17245806194635157421599797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22994408259513543228799729 17245806194635157421599797)
              ·
                refine ⟨1616794330747046008274981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17245806194635157421599797 1616794330747046008274981)
                ·
                  refine ⟨303148937015071126551559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1616794330747046008274981 303148937015071126551559)
                  ·
                    rfl

theorem cell21_1328356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 5, 4].length) (baseStart_1328356 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1328356 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1328356 prefixEnd_1328356 := by exact prefixLift 1328356
  have htrace : WordTrace (prefixWord ++ tailWord_1328356) baseStart_1328356 baseEnd_1328356 := by
    simpa [prefixWord, tailWord_1328356, baseEnd_1328356] using wordTrace_append hprefix tailTrace_1328356
  have hstable : (prefixWord ++ tailWord_1328356).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328356).length < 2 ^ (prefixWord ++ tailWord_1328356).sum := by decide
  have hdescent : baseEnd_1328356 < baseStart_1328356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328449 : List Nat := [1, 2, 5, 2, 1, 1, 1, 4, 4]
def baseStart_1328449 : Nat := 118140960795 + 1328449 * 2 ^ 59
def prefixEnd_1328449 : Nat := 4983230072969 + 3 ^ 40 * 1328449 * 2
def baseEnd_1328449 : Nat := 303170160882123631501369

theorem tailTrace_1328449 : CollatzResearch.WordTrace tailWord_1328449 prefixEnd_1328449 303170160882123631501369 := by
  unfold tailWord_1328449
  simp only [CollatzResearch.WordTrace]
  refine ⟨48452515564263628871388401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32301677042842419247592267 48452515564263628871388401)
  ·
    refine ⟨36339386673197721653541301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48452515564263628871388401 36339386673197721653541301)
    ·
      refine ⟨3406817500612286405019497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36339386673197721653541301 3406817500612286405019497)
      ·
        refine ⟨2555113125459214803764623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3406817500612286405019497 2555113125459214803764623)
        ·
          refine ⟨3832669688188822205646935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2555113125459214803764623 3832669688188822205646935)
          ·
            refine ⟨5749004532283233308470403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3832669688188822205646935 5749004532283233308470403)
            ·
              refine ⟨8623506798424849962705605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5749004532283233308470403 8623506798424849962705605)
              ·
                refine ⟨1616907524704659368007301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8623506798424849962705605 1616907524704659368007301)
                ·
                  refine ⟨303170160882123631501369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1616907524704659368007301 303170160882123631501369)
                  ·
                    rfl

theorem cell21_1328449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 4, 4].length) (baseStart_1328449 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1328449 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1328449 prefixEnd_1328449 := by exact prefixLift 1328449
  have htrace : WordTrace (prefixWord ++ tailWord_1328449) baseStart_1328449 baseEnd_1328449 := by
    simpa [prefixWord, tailWord_1328449, baseEnd_1328449] using wordTrace_append hprefix tailTrace_1328449
  have hstable : (prefixWord ++ tailWord_1328449).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328449).length < 2 ^ (prefixWord ++ tailWord_1328449).sum := by decide
  have hdescent : baseEnd_1328449 < baseStart_1328449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328452 : List Nat := [2, 3, 4, 1, 1, 2, 1, 4, 3]
def baseStart_1328452 : Nat := 118140960795 + 1328452 * 2 ^ 59
def prefixEnd_1328452 : Nat := 4983230072969 + 3 ^ 40 * 1328452 * 2
def baseEnd_1328452 : Nat := 303170845522996292951363

theorem tailTrace_1328452 : CollatzResearch.WordTrace tailWord_1328452 prefixEnd_1328452 303170845522996292951363 := by
  unfold tailWord_1328452
  simp only [CollatzResearch.WordTrace]
  refine ⟨24226312491626380191873805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32301749988835173589165073 24226312491626380191873805)
  ·
    refine ⟨9084867184359892571952677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24226312491626380191873805 9084867184359892571952677)
    ·
      refine ⟨1703412597067479857241127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9084867184359892571952677 1703412597067479857241127)
      ·
        refine ⟨2555118895601219785861691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1703412597067479857241127 2555118895601219785861691)
        ·
          refine ⟨3832678343401829678792537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2555118895601219785861691 3832678343401829678792537)
          ·
            refine ⟨2874508757551372259094403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3832678343401829678792537 2874508757551372259094403)
            ·
              refine ⟨4311763136327058388641605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2874508757551372259094403 4311763136327058388641605)
              ·
                refine ⟨808455588061323447870301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4311763136327058388641605 808455588061323447870301)
                ·
                  refine ⟨303170845522996292951363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 808455588061323447870301 303170845522996292951363)
                  ·
                    rfl

theorem cell21_1328452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 4, 3].length) (baseStart_1328452 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1328452 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1328452 prefixEnd_1328452 := by exact prefixLift 1328452
  have htrace : WordTrace (prefixWord ++ tailWord_1328452) baseStart_1328452 baseEnd_1328452 := by
    simpa [prefixWord, tailWord_1328452, baseEnd_1328452] using wordTrace_append hprefix tailTrace_1328452
  have hstable : (prefixWord ++ tailWord_1328452).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328452).length < 2 ^ (prefixWord ++ tailWord_1328452).sum := by decide
  have hdescent : baseEnd_1328452 < baseStart_1328452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328567 : List Nat := [1, 1, 3, 1, 3, 2, 1, 3, 6]
def baseStart_1328567 : Nat := 118140960795 + 1328567 * 2 ^ 59
def prefixEnd_1328567 : Nat := 4983230072969 + 3 ^ 40 * 1328567 * 2
def baseEnd_1328567 : Nat := 303197090089781648534461

theorem tailTrace_1328567 : CollatzResearch.WordTrace tailWord_1328567 prefixEnd_1328567 303197090089781648534461 := by
  unfold tailWord_1328567
  simp only [CollatzResearch.WordTrace]
  refine ⟨48456819377836135024183955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32304546251890756682789303 48456819377836135024183955)
  ·
    refine ⟨72685229066754202536275933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48456819377836135024183955 72685229066754202536275933)
    ·
      refine ⟨27256960900032825951103475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72685229066754202536275933 27256960900032825951103475)
      ·
        refine ⟨40885441350049238926655213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27256960900032825951103475 40885441350049238926655213)
        ·
          refine ⟨15332040506268464597495705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40885441350049238926655213 15332040506268464597495705)
          ·
            refine ⟨11499030379701348448121779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15332040506268464597495705 11499030379701348448121779)
            ·
              refine ⟨17248545569552022672182669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11499030379701348448121779 17248545569552022672182669)
              ·
                refine ⟨6468204588582008502068501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17248545569552022672182669 6468204588582008502068501)
                ·
                  refine ⟨303197090089781648534461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6468204588582008502068501 303197090089781648534461)
                  ·
                    rfl

theorem cell21_1328567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3, 6].length) (baseStart_1328567 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1328567 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1328567 prefixEnd_1328567 := by exact prefixLift 1328567
  have htrace : WordTrace (prefixWord ++ tailWord_1328567) baseStart_1328567 baseEnd_1328567 := by
    simpa [prefixWord, tailWord_1328567, baseEnd_1328567] using wordTrace_append hprefix tailTrace_1328567
  have hstable : (prefixWord ++ tailWord_1328567).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328567).length < 2 ^ (prefixWord ++ tailWord_1328567).sum := by decide
  have hdescent : baseEnd_1328567 < baseStart_1328567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328584 : List Nat := [2, 1, 3, 1, 3, 1, 3, 3, 4]
def baseStart_1328584 : Nat := 118140960795 + 1328584 * 2 ^ 59
def prefixEnd_1328584 : Nat := 4983230072969 + 3 ^ 40 * 1328584 * 2
def baseEnd_1328584 : Nat := 303200969721393396751093

theorem tailTrace_1328584 : CollatzResearch.WordTrace tailWord_1328584 prefixEnd_1328584 303200969721393396751093 := by
  unfold tailWord_1328584
  simp only [CollatzResearch.WordTrace]
  refine ⟨24228719709387273463776403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32304959612516364618368537 24228719709387273463776403)
  ·
    refine ⟨36343079564080910195664605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24228719709387273463776403 36343079564080910195664605)
    ·
      refine ⟨13628654836530341323374227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36343079564080910195664605 13628654836530341323374227)
      ·
        refine ⟨20442982254795511985061341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13628654836530341323374227 20442982254795511985061341)
        ·
          refine ⟨7666118345548316994398003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20442982254795511985061341 7666118345548316994398003)
          ·
            refine ⟨11499177518322475491597005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7666118345548316994398003 11499177518322475491597005)
            ·
              refine ⟨4312191569370928309348877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11499177518322475491597005 4312191569370928309348877)
              ·
                refine ⟨1617071838514098116005829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4312191569370928309348877 1617071838514098116005829)
                ·
                  refine ⟨303200969721393396751093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1617071838514098116005829 303200969721393396751093)
                  ·
                    rfl

theorem cell21_1328584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 3, 4].length) (baseStart_1328584 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1328584 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1328584 prefixEnd_1328584 := by exact prefixLift 1328584
  have htrace : WordTrace (prefixWord ++ tailWord_1328584) baseStart_1328584 baseEnd_1328584 := by
    simpa [prefixWord, tailWord_1328584, baseEnd_1328584] using wordTrace_append hprefix tailTrace_1328584
  have hstable : (prefixWord ++ tailWord_1328584).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328584).length < 2 ^ (prefixWord ++ tailWord_1328584).sum := by decide
  have hdescent : baseEnd_1328584 < baseStart_1328584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328621 : List Nat := [1, 5, 1, 3, 2, 2, 2, 2, 3]
def baseStart_1328621 : Nat := 118140960795 + 1328621 * 2 ^ 59
def prefixEnd_1328621 : Nat := 4983230072969 + 3 ^ 40 * 1328621 * 2
def baseEnd_1328621 : Nat := 303209413625489554634351

theorem tailTrace_1328621 : CollatzResearch.WordTrace tailWord_1328621 prefixEnd_1328621 303209413625489554634351 := by
  unfold tailWord_1328621
  simp only [CollatzResearch.WordTrace]
  refine ⟨48458788919640502246649717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32305859279760334831099811 48458788919640502246649717)
  ·
    refine ⟨4543011461216297085623411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48458788919640502246649717 4543011461216297085623411)
    ·
      refine ⟨6814517191824445628435117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4543011461216297085623411 6814517191824445628435117)
      ·
        refine ⟨2555443946934167110663169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6814517191824445628435117 2555443946934167110663169)
        ·
          refine ⟨1916582960200625332997377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2555443946934167110663169 1916582960200625332997377)
          ·
            refine ⟨1437437220150468999748033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1916582960200625332997377 1437437220150468999748033)
            ·
              refine ⟨1078077915112851749811025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1437437220150468999748033 1078077915112851749811025)
              ·
                refine ⟨808558436334638812358269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1078077915112851749811025 808558436334638812358269)
                ·
                  refine ⟨303209413625489554634351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 808558436334638812358269 303209413625489554634351)
                  ·
                    rfl

theorem cell21_1328621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 2, 2, 3].length) (baseStart_1328621 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1328621 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1328621 prefixEnd_1328621 := by exact prefixLift 1328621
  have htrace : WordTrace (prefixWord ++ tailWord_1328621) baseStart_1328621 baseEnd_1328621 := by
    simpa [prefixWord, tailWord_1328621, baseEnd_1328621] using wordTrace_append hprefix tailTrace_1328621
  have hstable : (prefixWord ++ tailWord_1328621).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328621).length < 2 ^ (prefixWord ++ tailWord_1328621).sum := by decide
  have hdescent : baseEnd_1328621 < baseStart_1328621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328705 : List Nat := [1, 2, 5, 1, 1, 1, 1, 4, 5]
def baseStart_1328705 : Nat := 118140960795 + 1328705 * 2 ^ 59
def prefixEnd_1328705 : Nat := 4983230072969 + 3 ^ 40 * 1328705 * 2
def baseEnd_1328705 : Nat := 303228583569924075234179

theorem tailTrace_1328705 : CollatzResearch.WordTrace tailWord_1328705 prefixEnd_1328705 303228583569924075234179 := by
  unfold tailWord_1328705
  simp only [CollatzResearch.WordTrace]
  refine ⟨48461852651336184592707569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32307901767557456395138379 48461852651336184592707569)
  ·
    refine ⟨36346389488502138444530677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48461852651336184592707569 36346389488502138444530677)
    ·
      refine ⟨3407474014547075479174751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36346389488502138444530677 3407474014547075479174751)
      ·
        refine ⟨5111211021820613218762127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3407474014547075479174751 5111211021820613218762127)
        ·
          refine ⟨7666816532730919828143191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5111211021820613218762127 7666816532730919828143191)
          ·
            refine ⟨11500224799096379742214787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7666816532730919828143191 11500224799096379742214787)
            ·
              refine ⟨17250337198644569613322181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11500224799096379742214787 17250337198644569613322181)
              ·
                refine ⟨3234438224745856802497909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17250337198644569613322181 3234438224745856802497909)
                ·
                  refine ⟨303228583569924075234179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3234438224745856802497909 303228583569924075234179)
                  ·
                    rfl

theorem cell21_1328705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 4, 5].length) (baseStart_1328705 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1328705 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1328705 prefixEnd_1328705 := by exact prefixLift 1328705
  have htrace : WordTrace (prefixWord ++ tailWord_1328705) baseStart_1328705 baseEnd_1328705 := by
    simpa [prefixWord, tailWord_1328705, baseEnd_1328705] using wordTrace_append hprefix tailTrace_1328705
  have hstable : (prefixWord ++ tailWord_1328705).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328705).length < 2 ^ (prefixWord ++ tailWord_1328705).sum := by decide
  have hdescent : baseEnd_1328705 < baseStart_1328705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328739 : List Nat := [1, 1, 1, 5, 1, 4, 3, 2, 3]
def baseStart_1328739 : Nat := 118140960795 + 1328739 * 2 ^ 59
def prefixEnd_1328739 : Nat := 4983230072969 + 3 ^ 40 * 1328739 * 2
def baseEnd_1328739 : Nat := 303236342833147571667443

theorem tailTrace_1328739 : CollatzResearch.WordTrace tailWord_1328739 prefixEnd_1328739 303236342833147571667443 := by
  unfold tailWord_1328739
  simp only [CollatzResearch.WordTrace]
  refine ⟨48463092733213008399445271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32308728488808672266296847 48463092733213008399445271)
  ·
    refine ⟨72694639099819512599167907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48463092733213008399445271 72694639099819512599167907)
    ·
      refine ⟨109041958649729268898751861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72694639099819512599167907 109041958649729268898751861)
      ·
        refine ⟨10222683623412118959257987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 109041958649729268898751861 10222683623412118959257987)
        ·
          refine ⟨15334025435118178438886981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10222683623412118959257987 15334025435118178438886981)
          ·
            refine ⟨2875129769084658457291309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15334025435118178438886981 2875129769084658457291309)
            ·
              refine ⟨1078173663406746921484241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2875129769084658457291309 1078173663406746921484241)
              ·
                refine ⟨808630247555060191113181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1078173663406746921484241 808630247555060191113181)
                ·
                  refine ⟨303236342833147571667443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 808630247555060191113181 303236342833147571667443)
                  ·
                    rfl

theorem cell21_1328739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 3, 2, 3].length) (baseStart_1328739 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1328739 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1328739 prefixEnd_1328739 := by exact prefixLift 1328739
  have htrace : WordTrace (prefixWord ++ tailWord_1328739) baseStart_1328739 baseEnd_1328739 := by
    simpa [prefixWord, tailWord_1328739, baseEnd_1328739] using wordTrace_append hprefix tailTrace_1328739
  have hstable : (prefixWord ++ tailWord_1328739).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328739).length < 2 ^ (prefixWord ++ tailWord_1328739).sum := by decide
  have hdescent : baseEnd_1328739 < baseStart_1328739 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328764 : List Nat := [2, 2, 2, 1, 1, 2, 1, 3, 7]
def baseStart_1328764 : Nat := 118140960795 + 1328764 * 2 ^ 59
def prefixEnd_1328764 : Nat := 4983230072969 + 3 ^ 40 * 1328764 * 2
def baseEnd_1328764 : Nat := 303242048173753083750725

theorem tailTrace_1328764 : CollatzResearch.WordTrace tailWord_1328764 prefixEnd_1328764 303242048173753083750725 := by
  unfold tailWord_1328764
  simp only [CollatzResearch.WordTrace]
  refine ⟨24232002279061218834552673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32309336372081625112736897 24232002279061218834552673)
  ·
    refine ⟨18174001709295914125914505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24232002279061218834552673 18174001709295914125914505)
    ·
      refine ⟨13630501281971935594435879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18174001709295914125914505 13630501281971935594435879)
      ·
        refine ⟨20445751922957903391653819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13630501281971935594435879 20445751922957903391653819)
        ·
          refine ⟨30668627884436855087480729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20445751922957903391653819 30668627884436855087480729)
          ·
            refine ⟨23001470913327641315610547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30668627884436855087480729 23001470913327641315610547)
            ·
              refine ⟨34502206369991461973415821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23001470913327641315610547 34502206369991461973415821)
              ·
                refine ⟨12938327388746798240030933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34502206369991461973415821 12938327388746798240030933)
                ·
                  refine ⟨303242048173753083750725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12938327388746798240030933 303242048173753083750725)
                  ·
                    rfl

theorem cell21_1328764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 7].length) (baseStart_1328764 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1328764 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1328764 prefixEnd_1328764 := by exact prefixLift 1328764
  have htrace : WordTrace (prefixWord ++ tailWord_1328764) baseStart_1328764 baseEnd_1328764 := by
    simpa [prefixWord, tailWord_1328764, baseEnd_1328764] using wordTrace_append hprefix tailTrace_1328764
  have hstable : (prefixWord ++ tailWord_1328764).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328764).length < 2 ^ (prefixWord ++ tailWord_1328764).sum := by decide
  have hdescent : baseEnd_1328764 < baseStart_1328764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328840 : List Nat := [2, 1, 3, 1, 2, 2, 1, 2, 7]
def baseStart_1328840 : Nat := 118140960795 + 1328840 * 2 ^ 59
def prefixEnd_1328840 : Nat := 4983230072969 + 3 ^ 40 * 1328840 * 2
def baseEnd_1328840 : Nat := 303259392409193840483903

theorem tailTrace_1328840 : CollatzResearch.WordTrace tailWord_1328840 prefixEnd_1328840 303259392409193840483903 := by
  unfold tailWord_1328840
  simp only [CollatzResearch.WordTrace]
  refine ⟨24233388252923551324435987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32311184337231401765914649 24233388252923551324435987)
  ·
    refine ⟨36350082379385326986653981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24233388252923551324435987 36350082379385326986653981)
    ·
      refine ⟨13631280892269497619995243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36350082379385326986653981 13631280892269497619995243)
      ·
        refine ⟨20446921338404246429992865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13631280892269497619995243 20446921338404246429992865)
        ·
          refine ⟨15335191003803184822494649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20446921338404246429992865 15335191003803184822494649)
          ·
            refine ⟨11501393252852388616870987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15335191003803184822494649 11501393252852388616870987)
            ·
              refine ⟨17252089879278582925306481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11501393252852388616870987 17252089879278582925306481)
              ·
                refine ⟨12939067409458937193979861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17252089879278582925306481 12939067409458937193979861)
                ·
                  refine ⟨303259392409193840483903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12939067409458937193979861 303259392409193840483903)
                  ·
                    rfl

theorem cell21_1328840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 7].length) (baseStart_1328840 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1328840 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1328840 prefixEnd_1328840 := by exact prefixLift 1328840
  have htrace : WordTrace (prefixWord ++ tailWord_1328840) baseStart_1328840 baseEnd_1328840 := by
    simpa [prefixWord, tailWord_1328840, baseEnd_1328840] using wordTrace_append hprefix tailTrace_1328840
  have hstable : (prefixWord ++ tailWord_1328840).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328840).length < 2 ^ (prefixWord ++ tailWord_1328840).sum := by decide
  have hdescent : baseEnd_1328840 < baseStart_1328840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328857 : List Nat := [1, 2, 1, 2, 3, 4, 2, 1, 5]
def baseStart_1328857 : Nat := 118140960795 + 1328857 * 2 ^ 59
def prefixEnd_1328857 : Nat := 4983230072969 + 3 ^ 40 * 1328857 * 2
def baseEnd_1328857 : Nat := 303263272040805588700535

theorem tailTrace_1328857 : CollatzResearch.WordTrace tailWord_1328857 prefixEnd_1328857 303263272040805588700535 := by
  unfold tailWord_1328857
  simp only [CollatzResearch.WordTrace]
  refine ⟨48467396546785514552240825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32311597697857009701493883 48467396546785514552240825)
  ·
    refine ⟨36350547410089135914180619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48467396546785514552240825 36350547410089135914180619)
    ·
      refine ⟨54525821115133703871270929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36350547410089135914180619 54525821115133703871270929)
      ·
        refine ⟨40894365836350277903453197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54525821115133703871270929 40894365836350277903453197)
        ·
          refine ⟨15335387188631354213794949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40894365836350277903453197 15335387188631354213794949)
          ·
            refine ⟨2875385097868378915086553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15335387188631354213794949 2875385097868378915086553)
            ·
              refine ⟨2156538823401284186314915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2875385097868378915086553 2156538823401284186314915)
              ·
                refine ⟨3234808235101926279472373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2156538823401284186314915 3234808235101926279472373)
                ·
                  refine ⟨303263272040805588700535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3234808235101926279472373 303263272040805588700535)
                  ·
                    rfl

theorem cell21_1328857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 1, 5].length) (baseStart_1328857 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1328857 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1328857 prefixEnd_1328857 := by exact prefixLift 1328857
  have htrace : WordTrace (prefixWord ++ tailWord_1328857) baseStart_1328857 baseEnd_1328857 := by
    simpa [prefixWord, tailWord_1328857, baseEnd_1328857] using wordTrace_append hprefix tailTrace_1328857
  have hstable : (prefixWord ++ tailWord_1328857).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328857).length < 2 ^ (prefixWord ++ tailWord_1328857).sum := by decide
  have hdescent : baseEnd_1328857 < baseStart_1328857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328961 : List Nat := [1, 2, 5, 13]
def baseStart_1328961 : Nat := 118140960795 + 1328961 * 2 ^ 59
def prefixEnd_1328961 : Nat := 4983230072969 + 3 ^ 40 * 1328961 * 2
def baseEnd_1328961 : Nat := 1248094675957714069823

theorem tailTrace_1328961 : CollatzResearch.WordTrace tailWord_1328961 prefixEnd_1328961 1248094675957714069823 := by
  unfold tailWord_1328961
  simp only [CollatzResearch.WordTrace]
  refine ⟨48471189738408740314026737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32314126492272493542684491 48471189738408740314026737)
  ·
    refine ⟨36353392303806555235520053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48471189738408740314026737 36353392303806555235520053)
    ·
      refine ⟨3408130528481864553330005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36353392303806555235520053 3408130528481864553330005)
      ·
        refine ⟨1248094675957714069823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 3408130528481864553330005 1248094675957714069823)
        ·
          rfl

theorem cell21_1328961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 13].length) (baseStart_1328961 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1328961 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1328961 prefixEnd_1328961 := by exact prefixLift 1328961
  have htrace : WordTrace (prefixWord ++ tailWord_1328961) baseStart_1328961 baseEnd_1328961 := by
    simpa [prefixWord, tailWord_1328961, baseEnd_1328961] using wordTrace_append hprefix tailTrace_1328961
  have hstable : (prefixWord ++ tailWord_1328961).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328961).length < 2 ^ (prefixWord ++ tailWord_1328961).sum := by decide
  have hdescent : baseEnd_1328961 < baseStart_1328961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328978 : List Nat := [3, 2, 2, 1, 1, 3, 3, 6]
def baseStart_1328978 : Nat := 118140960795 + 1328978 * 2 ^ 59
def prefixEnd_1328978 : Nat := 4983230072969 + 3 ^ 40 * 1328978 * 2
def baseEnd_1328978 : Nat := 101096961963112089061207

theorem tailTrace_1328978 : CollatzResearch.WordTrace tailWord_1328978 prefixEnd_1328978 101096961963112089061207 := by
  unfold tailWord_1328978
  simp only [CollatzResearch.WordTrace]
  refine ⟨12117952444836788054348897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32314539852898101478263725 12117952444836788054348897)
  ·
    refine ⟨9088464333627591040761673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12117952444836788054348897 9088464333627591040761673)
    ·
      refine ⟨6816348250220693280571255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9088464333627591040761673 6816348250220693280571255)
      ·
        refine ⟨10224522375331039920856883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6816348250220693280571255 10224522375331039920856883)
        ·
          refine ⟨15336783562996559881285325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10224522375331039920856883 15336783562996559881285325)
          ·
            refine ⟨5751293836123709955481997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15336783562996559881285325 5751293836123709955481997)
            ·
              refine ⟨2156735188546391233305749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5751293836123709955481997 2156735188546391233305749)
              ·
                refine ⟨101096961963112089061207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2156735188546391233305749 101096961963112089061207)
                ·
                  rfl

theorem cell21_1328978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 6].length) (baseStart_1328978 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1328978 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1328978 prefixEnd_1328978 := by exact prefixLift 1328978
  have htrace : WordTrace (prefixWord ++ tailWord_1328978) baseStart_1328978 baseEnd_1328978 := by
    simpa [prefixWord, tailWord_1328978, baseEnd_1328978] using wordTrace_append hprefix tailTrace_1328978
  have hstable : (prefixWord ++ tailWord_1328978).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328978).length < 2 ^ (prefixWord ++ tailWord_1328978).sum := by decide
  have hdescent : baseEnd_1328978 < baseStart_1328978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328992 : List Nat := [2, 1, 1, 3, 3, 2, 1, 1, 7]
def baseStart_1328992 : Nat := 118140960795 + 1328992 * 2 ^ 59
def prefixEnd_1328992 : Nat := 4983230072969 + 3 ^ 40 * 1328992 * 2
def baseEnd_1328992 : Nat := 303294080880075353950259

theorem tailTrace_1328992 : CollatzResearch.WordTrace tailWord_1328992 prefixEnd_1328992 303294080880075353950259 := by
  unfold tailWord_1328992
  simp only [CollatzResearch.WordTrace]
  refine ⟨24236160200648216304202615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32314880267530955072270153 24236160200648216304202615)
  ·
    refine ⟨36354240300972324456303923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24236160200648216304202615 36354240300972324456303923)
    ·
      refine ⟨54531360451458486684455885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36354240300972324456303923 54531360451458486684455885)
      ·
        refine ⟨20449260169296932506670957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54531360451458486684455885 20449260169296932506670957)
        ·
          refine ⟨7668472563486349690001609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20449260169296932506670957 7668472563486349690001609)
          ·
            refine ⟨5751354422614762267501207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7668472563486349690001609 5751354422614762267501207)
            ·
              refine ⟨8627031633922143401251811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5751354422614762267501207 8627031633922143401251811)
              ·
                refine ⟨12940547450883215101877717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8627031633922143401251811 12940547450883215101877717)
                ·
                  refine ⟨303294080880075353950259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12940547450883215101877717 303294080880075353950259)
                  ·
                    rfl

theorem cell21_1328992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 7].length) (baseStart_1328992 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1328992 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1328992 prefixEnd_1328992 := by exact prefixLift 1328992
  have htrace : WordTrace (prefixWord ++ tailWord_1328992) baseStart_1328992 baseEnd_1328992 := by
    simpa [prefixWord, tailWord_1328992, baseEnd_1328992] using wordTrace_append hprefix tailTrace_1328992
  have hstable : (prefixWord ++ tailWord_1328992).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328992).length < 2 ^ (prefixWord ++ tailWord_1328992).sum := by decide
  have hdescent : baseEnd_1328992 < baseStart_1328992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1328995 : List Nat := [1, 1, 1, 5, 4, 1, 3, 5]
def baseStart_1328995 : Nat := 118140960795 + 1328995 * 2 ^ 59
def prefixEnd_1328995 : Nat := 4983230072969 + 3 ^ 40 * 1328995 * 2
def baseEnd_1328995 : Nat := 101098255173649338466751

theorem tailTrace_1328995 : CollatzResearch.WordTrace tailWord_1328995 prefixEnd_1328995 101098255173649338466751 := by
  unfold tailWord_1328995
  simp only [CollatzResearch.WordTrace]
  refine ⟨48472429820285564120764439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32314953213523709413842959 48472429820285564120764439)
  ·
    refine ⟨72708644730428346181146659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48472429820285564120764439 72708644730428346181146659)
    ·
      refine ⟨109062967095642519271719989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72708644730428346181146659 109062967095642519271719989)
      ·
        refine ⟨10224653165216486181723749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 109062967095642519271719989 10224653165216486181723749)
        ·
          refine ⟨1917122468478091159073203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10224653165216486181723749 1917122468478091159073203)
          ·
            refine ⟨2875683702717136738609805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1917122468478091159073203 2875683702717136738609805)
            ·
              refine ⟨1078381388518926276978677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2875683702717136738609805 1078381388518926276978677)
              ·
                refine ⟨101098255173649338466751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1078381388518926276978677 101098255173649338466751)
                ·
                  rfl

theorem cell21_1328995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 3, 5].length) (baseStart_1328995 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1328995 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1328995 prefixEnd_1328995 := by exact prefixLift 1328995
  have htrace : WordTrace (prefixWord ++ tailWord_1328995) baseStart_1328995 baseEnd_1328995 := by
    simpa [prefixWord, tailWord_1328995, baseEnd_1328995] using wordTrace_append hprefix tailTrace_1328995
  have hstable : (prefixWord ++ tailWord_1328995).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1328995).length < 2 ^ (prefixWord ++ tailWord_1328995).sum := by decide
  have hdescent : baseEnd_1328995 < baseStart_1328995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1328995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329046 : List Nat := [5, 3, 1, 1, 2, 2, 2, 5]
def baseStart_1329046 : Nat := 118140960795 + 1329046 * 2 ^ 59
def prefixEnd_1329046 : Nat := 4983230072969 + 3 ^ 40 * 1329046 * 2
def baseEnd_1329046 : Nat := 101102134805261086683383

theorem tailTrace_1329046 : CollatzResearch.WordTrace tailWord_1329046 prefixEnd_1329046 101102134805261086683383 := by
  unfold tailWord_1329046
  simp only [CollatzResearch.WordTrace]
  refine ⟨3029643121443799989429437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32316193295400533220580661 3029643121443799989429437)
  ·
    refine ⟨1136116170541424996036039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3029643121443799989429437 1136116170541424996036039)
    ·
      refine ⟨1704174255812137494054059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1136116170541424996036039 1704174255812137494054059)
      ·
        refine ⟨2556261383718206241081089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1704174255812137494054059 2556261383718206241081089)
        ·
          refine ⟨1917196037788654680810817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2556261383718206241081089 1917196037788654680810817)
          ·
            refine ⟨1437897028341491010608113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1917196037788654680810817 1437897028341491010608113)
            ·
              refine ⟨1078422771256118257956085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1437897028341491010608113 1078422771256118257956085)
              ·
                refine ⟨101102134805261086683383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1078422771256118257956085 101102134805261086683383)
                ·
                  rfl

theorem cell21_1329046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 2, 5].length) (baseStart_1329046 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1329046 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1329046 prefixEnd_1329046 := by exact prefixLift 1329046
  have htrace : WordTrace (prefixWord ++ tailWord_1329046) baseStart_1329046 baseEnd_1329046 := by
    simpa [prefixWord, tailWord_1329046, baseEnd_1329046] using wordTrace_append hprefix tailTrace_1329046
  have hstable : (prefixWord ++ tailWord_1329046).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329046).length < 2 ^ (prefixWord ++ tailWord_1329046).sum := by decide
  have hdescent : baseEnd_1329046 < baseStart_1329046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329085 : List Nat := [1, 4, 1, 2, 3, 1, 3, 1, 5]
def baseStart_1329085 : Nat := 118140960795 + 1329085 * 2 ^ 59
def prefixEnd_1329085 : Nat := 4983230072969 + 3 ^ 40 * 1329085 * 2
def baseEnd_1329085 : Nat := 303315304747127858900069

theorem tailTrace_1329085 : CollatzResearch.WordTrace tailWord_1329085 prefixEnd_1329085 303315304747127858900069 := by
  unfold tailWord_1329085
  simp only [CollatzResearch.WordTrace]
  refine ⟨48475712389959509491540709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32317141593306339661027139 48475712389959509491540709)
  ·
    refine ⟨9089196073117408029663883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48475712389959509491540709 9089196073117408029663883)
    ·
      refine ⟨13633794109676112044495825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9089196073117408029663883 13633794109676112044495825)
      ·
        refine ⟨10225345582257084033371869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13633794109676112044495825 10225345582257084033371869)
        ·
          refine ⟨3834504593346406512514451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10225345582257084033371869 3834504593346406512514451)
          ·
            refine ⟨5751756890019609768771677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3834504593346406512514451 5751756890019609768771677)
            ·
              refine ⟨2156908833757353663289379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5751756890019609768771677 2156908833757353663289379)
              ·
                refine ⟨3235363250636030494934069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2156908833757353663289379 3235363250636030494934069)
                ·
                  refine ⟨303315304747127858900069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3235363250636030494934069 303315304747127858900069)
                  ·
                    rfl

theorem cell21_1329085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 1, 5].length) (baseStart_1329085 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1329085 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1329085 prefixEnd_1329085 := by exact prefixLift 1329085
  have htrace : WordTrace (prefixWord ++ tailWord_1329085) baseStart_1329085 baseEnd_1329085 := by
    simpa [prefixWord, tailWord_1329085, baseEnd_1329085] using wordTrace_append hprefix tailTrace_1329085
  have hstable : (prefixWord ++ tailWord_1329085).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329085).length < 2 ^ (prefixWord ++ tailWord_1329085).sum := by decide
  have hdescent : baseEnd_1329085 < baseStart_1329085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329099 : List Nat := [1, 1, 1, 1, 3, 4, 3, 3, 4]
def baseStart_1329099 : Nat := 118140960795 + 1329099 * 2 ^ 59
def prefixEnd_1329099 : Nat := 4983230072969 + 3 ^ 40 * 1329099 * 2
def baseEnd_1329099 : Nat := 303318499737866945666707

theorem tailTrace_1329099 : CollatzResearch.WordTrace tailWord_1329099 prefixEnd_1329099 303318499737866945666707 := by
  unfold tailWord_1329099
  simp only [CollatzResearch.WordTrace]
  refine ⟨48476223011908789882550351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32317482007939193255033567 48476223011908789882550351)
  ·
    refine ⟨72714334517863184823825527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48476223011908789882550351 72714334517863184823825527)
    ·
      refine ⟨109071501776794777235738291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72714334517863184823825527 109071501776794777235738291)
      ·
        refine ⟨163607252665192165853607437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109071501776794777235738291 163607252665192165853607437)
        ·
          refine ⟨61352719749447062195102789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 163607252665192165853607437 61352719749447062195102789)
          ·
            refine ⟨11503634953021324161581773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61352719749447062195102789 11503634953021324161581773)
            ·
              refine ⟨4313863107382996560593165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11503634953021324161581773 4313863107382996560593165)
              ·
                refine ⟨1617698665268623710222437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4313863107382996560593165 1617698665268623710222437)
                ·
                  refine ⟨303318499737866945666707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1617698665268623710222437 303318499737866945666707)
                  ·
                    rfl

theorem cell21_1329099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 3, 4].length) (baseStart_1329099 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1329099 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1329099 prefixEnd_1329099 := by exact prefixLift 1329099
  have htrace : WordTrace (prefixWord ++ tailWord_1329099) baseStart_1329099 baseEnd_1329099 := by
    simpa [prefixWord, tailWord_1329099, baseEnd_1329099] using wordTrace_append hprefix tailTrace_1329099
  have hstable : (prefixWord ++ tailWord_1329099).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329099).length < 2 ^ (prefixWord ++ tailWord_1329099).sum := by decide
  have hdescent : baseEnd_1329099 < baseStart_1329099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329178 : List Nat := [3, 1, 1, 3, 1, 4, 2, 3, 3]
def baseStart_1329178 : Nat := 118140960795 + 1329178 * 2 ^ 59
def prefixEnd_1329178 : Nat := 4983230072969 + 3 ^ 40 * 1329178 * 2
def baseEnd_1329178 : Nat := 303336528614180363849879

theorem tailTrace_1329178 : CollatzResearch.WordTrace tailWord_1329178 prefixEnd_1329178 303336528614180363849879 := by
  unfold tailWord_1329178
  simp only [CollatzResearch.WordTrace]
  refine ⟨12119776094655646593669047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32319402919081724249784125 12119776094655646593669047)
  ·
    refine ⟨18179664141983469890503571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12119776094655646593669047 18179664141983469890503571)
    ·
      refine ⟨27269496212975204835755357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18179664141983469890503571 27269496212975204835755357)
      ·
        refine ⟨10226061079865701813408259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27269496212975204835755357 10226061079865701813408259)
        ·
          refine ⟨15339091619798552720112389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10226061079865701813408259 15339091619798552720112389)
          ·
            refine ⟨2876079678712228635021073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15339091619798552720112389 2876079678712228635021073)
            ·
              refine ⟨2157059759034171476265805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2876079678712228635021073 2157059759034171476265805)
              ·
                refine ⟨808897409637814303599677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2157059759034171476265805 808897409637814303599677)
                ·
                  refine ⟨303336528614180363849879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 808897409637814303599677 303336528614180363849879)
                  ·
                    rfl

theorem cell21_1329178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 3, 3].length) (baseStart_1329178 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1329178 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1329178 prefixEnd_1329178 := by exact prefixLift 1329178
  have htrace : WordTrace (prefixWord ++ tailWord_1329178) baseStart_1329178 baseEnd_1329178 := by
    simpa [prefixWord, tailWord_1329178, baseEnd_1329178] using wordTrace_append hprefix tailTrace_1329178
  have hstable : (prefixWord ++ tailWord_1329178).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329178).length < 2 ^ (prefixWord ++ tailWord_1329178).sum := by decide
  have hdescent : baseEnd_1329178 < baseStart_1329178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329189 : List Nat := [1, 3, 1, 2, 2, 4, 8]
def baseStart_1329189 : Nat := 118140960795 + 1329189 * 2 ^ 59
def prefixEnd_1329189 : Nat := 4983230072969 + 3 ^ 40 * 1329189 * 2
def baseEnd_1329189 : Nat := 33704337662671865462947

theorem tailTrace_1329189 : CollatzResearch.WordTrace tailWord_1329189 prefixEnd_1329189 33704337662671865462947 := by
  unfold tailWord_1329189
  simp only [CollatzResearch.WordTrace]
  refine ⟨48479505581582735253326621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32319670387721823502217747 48479505581582735253326621)
  ·
    refine ⟨18179814593093525719997483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48479505581582735253326621 18179814593093525719997483)
    ·
      refine ⟨27269721889640288579996225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18179814593093525719997483 27269721889640288579996225)
      ·
        refine ⟨20452291417230216434997169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27269721889640288579996225 20452291417230216434997169)
        ·
          refine ⟨15339218562922662326247877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20452291417230216434997169 15339218562922662326247877)
          ·
            refine ⟨2876103480547999186171477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15339218562922662326247877 2876103480547999186171477)
            ·
              refine ⟨33704337662671865462947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2876103480547999186171477 33704337662671865462947)
              ·
                rfl

theorem cell21_1329189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 8].length) (baseStart_1329189 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1329189 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1329189 prefixEnd_1329189 := by exact prefixLift 1329189
  have htrace : WordTrace (prefixWord ++ tailWord_1329189) baseStart_1329189 baseEnd_1329189 := by
    simpa [prefixWord, tailWord_1329189, baseEnd_1329189] using wordTrace_append hprefix tailTrace_1329189
  have hstable : (prefixWord ++ tailWord_1329189).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329189).length < 2 ^ (prefixWord ++ tailWord_1329189).sum := by decide
  have hdescent : baseEnd_1329189 < baseStart_1329189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329206 : List Nat := [5, 1, 2, 1, 1, 1, 2, 8]
def baseStart_1329206 : Nat := 118140960795 + 1329206 * 2 ^ 59
def prefixEnd_1329206 : Nat := 4983230072969 + 3 ^ 40 * 1329206 * 2
def baseEnd_1329206 : Nat := 101114306198552845794385

theorem tailTrace_1329206 : CollatzResearch.WordTrace tailWord_1329206 prefixEnd_1329206 101114306198552845794385 := by
  unfold tailWord_1329206
  simp only [CollatzResearch.WordTrace]
  refine ⟨3030007851407571697293467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32320083748347431437796981 3030007851407571697293467)
  ·
    refine ⟨4545011777111357545940201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3030007851407571697293467 4545011777111357545940201)
    ·
      refine ⟨3408758832833518159455151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4545011777111357545940201 3408758832833518159455151)
      ·
        refine ⟨5113138249250277239182727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3408758832833518159455151 5113138249250277239182727)
        ·
          refine ⟨7669707373875415858774091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5113138249250277239182727 7669707373875415858774091)
          ·
            refine ⟨11504561060813123788161137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7669707373875415858774091 11504561060813123788161137)
            ·
              refine ⟨8628420795609842841120853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11504561060813123788161137 8628420795609842841120853)
              ·
                refine ⟨101114306198552845794385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8628420795609842841120853 101114306198552845794385)
                ·
                  rfl

theorem cell21_1329206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 8].length) (baseStart_1329206 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1329206 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1329206 prefixEnd_1329206 := by exact prefixLift 1329206
  have htrace : WordTrace (prefixWord ++ tailWord_1329206) baseStart_1329206 baseEnd_1329206 := by
    simpa [prefixWord, tailWord_1329206, baseEnd_1329206] using wordTrace_append hprefix tailTrace_1329206
  have hstable : (prefixWord ++ tailWord_1329206).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329206).length < 2 ^ (prefixWord ++ tailWord_1329206).sum := by decide
  have hdescent : baseEnd_1329206 < baseStart_1329206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329209 : List Nat := [1, 2, 1, 5, 3, 1, 3, 1, 4]
def baseStart_1329209 : Nat := 118140960795 + 1329209 * 2 ^ 59
def prefixEnd_1329209 : Nat := 4983230072969 + 3 ^ 40 * 1329209 * 2
def baseEnd_1329209 : Nat := 303343603236531198833149

theorem tailTrace_1329209 : CollatzResearch.WordTrace tailWord_1329209 prefixEnd_1329209 303343603236531198833149 := by
  unfold tailWord_1329209
  simp only [CollatzResearch.WordTrace]
  refine ⟨48480235041510278669054681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32320156694340185779369787 48480235041510278669054681)
  ·
    refine ⟨36360176281132709001791011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48480235041510278669054681 36360176281132709001791011)
    ·
      refine ⟨54540264421699063502686517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36360176281132709001791011 54540264421699063502686517)
      ·
        refine ⟨5113149789534287203376861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54540264421699063502686517 5113149789534287203376861)
        ·
          refine ⟨1917431171075357701266323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5113149789534287203376861 1917431171075357701266323)
          ·
            refine ⟨2876146756613036551899485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1917431171075357701266323 2876146756613036551899485)
            ·
              refine ⟨1078555033729888706962307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2876146756613036551899485 1078555033729888706962307)
              ·
                refine ⟨1617832550594833060443461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1078555033729888706962307 1617832550594833060443461)
                ·
                  refine ⟨303343603236531198833149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1617832550594833060443461 303343603236531198833149)
                  ·
                    rfl

theorem cell21_1329209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 3, 1, 4].length) (baseStart_1329209 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1329209 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1329209 prefixEnd_1329209 := by exact prefixLift 1329209
  have htrace : WordTrace (prefixWord ++ tailWord_1329209) baseStart_1329209 baseEnd_1329209 := by
    simpa [prefixWord, tailWord_1329209, baseEnd_1329209] using wordTrace_append hprefix tailTrace_1329209
  have hstable : (prefixWord ++ tailWord_1329209).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329209).length < 2 ^ (prefixWord ++ tailWord_1329209).sum := by decide
  have hdescent : baseEnd_1329209 < baseStart_1329209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329265 : List Nat := [1, 2, 2, 2, 1, 1, 6, 6]
def baseStart_1329265 : Nat := 118140960795 + 1329265 * 2 ^ 59
def prefixEnd_1329265 : Nat := 4983230072969 + 3 ^ 40 * 1329265 * 2
def baseEnd_1329265 : Nat := 101118794399829181966567

theorem tailTrace_1329265 : CollatzResearch.WordTrace tailWord_1329265 prefixEnd_1329265 101118794399829181966567 := by
  unfold tailWord_1329265
  simp only [CollatzResearch.WordTrace]
  refine ⟨48482277529307400233093249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32321518352871600155395499 48482277529307400233093249)
  ·
    refine ⟨36361708146980550174819937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48482277529307400233093249 36361708146980550174819937)
    ·
      refine ⟨27271281110235412631114953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36361708146980550174819937 27271281110235412631114953)
      ·
        refine ⟨20453460832676559473336215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27271281110235412631114953 20453460832676559473336215)
        ·
          refine ⟨30680191249014839210004323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20453460832676559473336215 30680191249014839210004323)
          ·
            refine ⟨46020286873522258815006485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30680191249014839210004323 46020286873522258815006485)
            ·
              refine ⟨2157200947196355881953429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 46020286873522258815006485 2157200947196355881953429)
              ·
                refine ⟨101118794399829181966567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2157200947196355881953429 101118794399829181966567)
                ·
                  rfl

theorem cell21_1329265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 6].length) (baseStart_1329265 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1329265 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1329265 prefixEnd_1329265 := by exact prefixLift 1329265
  have htrace : WordTrace (prefixWord ++ tailWord_1329265) baseStart_1329265 baseEnd_1329265 := by
    simpa [prefixWord, tailWord_1329265, baseEnd_1329265] using wordTrace_append hprefix tailTrace_1329265
  have hstable : (prefixWord ++ tailWord_1329265).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329265).length < 2 ^ (prefixWord ++ tailWord_1329265).sum := by decide
  have hdescent : baseEnd_1329265 < baseStart_1329265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329355 : List Nat := [1, 1, 1, 1, 3, 2, 3, 2, 7]
def baseStart_1329355 : Nat := 118140960795 + 1329355 * 2 ^ 59
def prefixEnd_1329355 : Nat := 4983230072969 + 3 ^ 40 * 1329355 * 2
def baseEnd_1329355 : Nat := 303376922425667389399517

theorem tailTrace_1329355 : CollatzResearch.WordTrace tailWord_1329355 prefixEnd_1329355 303376922425667389399517 := by
  unfold tailWord_1329355
  simp only [CollatzResearch.WordTrace]
  refine ⟨48485560098981345603869519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32323706732654230402579679 48485560098981345603869519)
  ·
    refine ⟨72728340148472018405804279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48485560098981345603869519 72728340148472018405804279)
    ·
      refine ⟨109092510222708027608706419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72728340148472018405804279 109092510222708027608706419)
      ·
        refine ⟨163638765334062041413059629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109092510222708027608706419 163638765334062041413059629)
        ·
          refine ⟨61364537000273265529897361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 163638765334062041413059629 61364537000273265529897361)
          ·
            refine ⟨46023402750204949147423021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61364537000273265529897361 46023402750204949147423021)
            ·
              refine ⟨17258776031326855930283633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46023402750204949147423021 17258776031326855930283633)
              ·
                refine ⟨12944082023495141947712725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17258776031326855930283633 12944082023495141947712725)
                ·
                  refine ⟨303376922425667389399517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12944082023495141947712725 303376922425667389399517)
                  ·
                    rfl

theorem cell21_1329355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 7].length) (baseStart_1329355 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1329355 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1329355 prefixEnd_1329355 := by exact prefixLift 1329355
  have htrace : WordTrace (prefixWord ++ tailWord_1329355) baseStart_1329355 baseEnd_1329355 := by
    simpa [prefixWord, tailWord_1329355, baseEnd_1329355] using wordTrace_append hprefix tailTrace_1329355
  have hstable : (prefixWord ++ tailWord_1329355).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329355).length < 2 ^ (prefixWord ++ tailWord_1329355).sum := by decide
  have hdescent : baseEnd_1329355 < baseStart_1329355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329417 : List Nat := [1, 2, 1, 1, 3, 6, 7]
def baseStart_1329417 : Nat := 118140960795 + 1329417 * 2 ^ 59
def prefixEnd_1329417 : Nat := 4983230072969 + 3 ^ 40 * 1329417 * 2
def baseEnd_1329417 : Nat := 33710119074485451040673

theorem tailTrace_1329417 : CollatzResearch.WordTrace tailWord_1329417 prefixEnd_1329417 33710119074485451040673 := by
  unfold tailWord_1329417
  simp only [CollatzResearch.WordTrace]
  refine ⟨48487821424756730192626505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32325214283171153461751003 48487821424756730192626505)
  ·
    refine ⟨36365866068567547644469879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48487821424756730192626505 36365866068567547644469879)
    ·
      refine ⟨54548799102851321466704819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36365866068567547644469879 54548799102851321466704819)
      ·
        refine ⟨81823198654276982200057229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54548799102851321466704819 81823198654276982200057229)
        ·
          refine ⟨30683699495353868325021461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81823198654276982200057229 30683699495353868325021461)
          ·
            refine ⟨1438298413844712577735381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 30683699495353868325021461 1438298413844712577735381)
            ·
              refine ⟨33710119074485451040673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1438298413844712577735381 33710119074485451040673)
              ·
                rfl

theorem cell21_1329417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 7].length) (baseStart_1329417 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1329417 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1329417 prefixEnd_1329417 := by exact prefixLift 1329417
  have htrace : WordTrace (prefixWord ++ tailWord_1329417) baseStart_1329417 baseEnd_1329417 := by
    simpa [prefixWord, tailWord_1329417, baseEnd_1329417] using wordTrace_append hprefix tailTrace_1329417
  have hstable : (prefixWord ++ tailWord_1329417).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329417).length < 2 ^ (prefixWord ++ tailWord_1329417).sum := by decide
  have hdescent : baseEnd_1329417 < baseStart_1329417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329434 : List Nat := [3, 1, 1, 3, 4, 1, 2, 6]
def baseStart_1329434 : Nat := 118140960795 + 1329434 * 2 ^ 59
def prefixEnd_1329434 : Nat := 4983230072969 + 3 ^ 40 * 1329434 * 2
def baseEnd_1329434 : Nat := 101131650433993602527563

theorem tailTrace_1329434 : CollatzResearch.WordTrace tailWord_1329434 prefixEnd_1329434 101131650433993602527563 := by
  unfold tailWord_1329434
  simp only [CollatzResearch.WordTrace]
  refine ⟨12122110366423785523998839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32325627643796761397330237 12122110366423785523998839)
  ·
    refine ⟨18183165549635678285998259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12122110366423785523998839 18183165549635678285998259)
    ·
      refine ⟨27274748324453517428997389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18183165549635678285998259 27274748324453517428997389)
      ·
        refine ⟨10228030621670069035874021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27274748324453517428997389 10228030621670069035874021)
        ·
          refine ⟨1917755741563137944226379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10228030621670069035874021 1917755741563137944226379)
          ·
            refine ⟨2876633612344706916339569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1917755741563137944226379 2876633612344706916339569)
            ·
              refine ⟨2157475209258530187254677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2876633612344706916339569 2157475209258530187254677)
              ·
                refine ⟨101131650433993602527563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2157475209258530187254677 101131650433993602527563)
                ·
                  rfl

theorem cell21_1329434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 6].length) (baseStart_1329434 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1329434 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1329434 prefixEnd_1329434 := by exact prefixLift 1329434
  have htrace : WordTrace (prefixWord ++ tailWord_1329434) baseStart_1329434 baseEnd_1329434 := by
    simpa [prefixWord, tailWord_1329434, baseEnd_1329434] using wordTrace_append hprefix tailTrace_1329434
  have hstable : (prefixWord ++ tailWord_1329434).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329434).length < 2 ^ (prefixWord ++ tailWord_1329434).sum := by decide
  have hdescent : baseEnd_1329434 < baseStart_1329434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329479 : List Nat := [1, 1, 4, 1, 2, 2, 4, 2, 4]
def baseStart_1329479 : Nat := 118140960795 + 1329479 * 2 ^ 59
def prefixEnd_1329479 : Nat := 4983230072969 + 3 ^ 40 * 1329479 * 2
def baseEnd_1329479 : Nat := 303405220915070729332597

theorem tailTrace_1329479 : CollatzResearch.WordTrace tailWord_1329479 prefixEnd_1329479 303405220915070729332597 := by
  unfold tailWord_1329479
  simp only [CollatzResearch.WordTrace]
  refine ⟨48490082750532114781383491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32326721833688076520922327 48490082750532114781383491)
  ·
    refine ⟨72735124125798172172075237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48490082750532114781383491 72735124125798172172075237)
    ·
      refine ⟨13637835773587157282264107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72735124125798172172075237 13637835773587157282264107)
      ·
        refine ⟨20456753660380735923396161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13637835773587157282264107 20456753660380735923396161)
        ·
          refine ⟨15342565245285551942547121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20456753660380735923396161 15342565245285551942547121)
          ·
            refine ⟨11506923933964163956910341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15342565245285551942547121 11506923933964163956910341)
            ·
              refine ⟨2157548237618280741920689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11506923933964163956910341 2157548237618280741920689)
              ·
                refine ⟨1618161178213710556440517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2157548237618280741920689 1618161178213710556440517)
                ·
                  refine ⟨303405220915070729332597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1618161178213710556440517 303405220915070729332597)
                  ·
                    rfl

theorem cell21_1329479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 2, 4].length) (baseStart_1329479 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1329479 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1329479 prefixEnd_1329479 := by exact prefixLift 1329479
  have htrace : WordTrace (prefixWord ++ tailWord_1329479) baseStart_1329479 baseEnd_1329479 := by
    simpa [prefixWord, tailWord_1329479, baseEnd_1329479] using wordTrace_append hprefix tailTrace_1329479
  have hstable : (prefixWord ++ tailWord_1329479).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329479).length < 2 ^ (prefixWord ++ tailWord_1329479).sum := by decide
  have hdescent : baseEnd_1329479 < baseStart_1329479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329502 : List Nat := [4, 4, 2, 1, 1, 1, 3, 5]
def baseStart_1329502 : Nat := 118140960795 + 1329502 * 2 ^ 59
def prefixEnd_1329502 : Nat := 4983230072969 + 3 ^ 40 * 1329502 * 2
def baseEnd_1329502 : Nat := 101136823276142600149739

theorem tailTrace_1329502 : CollatzResearch.WordTrace tailWord_1329502 prefixEnd_1329502 101136823276142600149739 := by
  unfold tailWord_1329502
  simp only [CollatzResearch.WordTrace]
  refine ⟨6061365203681098713683845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32327281086299193139647173 6061365203681098713683845)
  ·
    refine ⟨1136505975690206008815721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6061365203681098713683845 1136505975690206008815721)
    ·
      refine ⟨852379481767654506611791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1136505975690206008815721 852379481767654506611791)
      ·
        refine ⟨1278569222651481759917687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 852379481767654506611791 1278569222651481759917687)
        ·
          refine ⟨1917853833977222639876531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1278569222651481759917687 1917853833977222639876531)
          ·
            refine ⟨2876780750965833959814797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1917853833977222639876531 2876780750965833959814797)
            ·
              refine ⟨1078792781612187734930549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2876780750965833959814797 1078792781612187734930549)
              ·
                refine ⟨101136823276142600149739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1078792781612187734930549 101136823276142600149739)
                ·
                  rfl

theorem cell21_1329502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 3, 5].length) (baseStart_1329502 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1329502 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1329502 prefixEnd_1329502 := by exact prefixLift 1329502
  have htrace : WordTrace (prefixWord ++ tailWord_1329502) baseStart_1329502 baseEnd_1329502 := by
    simpa [prefixWord, tailWord_1329502, baseEnd_1329502] using wordTrace_append hprefix tailTrace_1329502
  have hstable : (prefixWord ++ tailWord_1329502).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329502).length < 2 ^ (prefixWord ++ tailWord_1329502).sum := by decide
  have hdescent : baseEnd_1329502 < baseStart_1329502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329645 : List Nat := [1, 5, 1, 3, 1, 10]
def baseStart_1329645 : Nat := 118140960795 + 1329645 * 2 ^ 59
def prefixEnd_1329645 : Nat := 4983230072969 + 3 ^ 40 * 1329645 * 2
def baseEnd_1329645 : Nat := 11238633495433012206133

theorem tailTrace_1329645 : CollatzResearch.WordTrace tailWord_1329645 prefixEnd_1329645 11238633495433012206133 := by
  unfold tailWord_1329645
  simp only [CollatzResearch.WordTrace]
  refine ⟨48496137267930725131926389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32330758178620483421284259 48496137267930725131926389)
  ·
    refine ⟨4546512868868505481118099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48496137267930725131926389 4546512868868505481118099)
    ·
      refine ⟨6819769303302758221677149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4546512868868505481118099 6819769303302758221677149)
      ·
        refine ⟨2557413488738534333128931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6819769303302758221677149 2557413488738534333128931)
        ·
          refine ⟨3836120233107801499693397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2557413488738534333128931 3836120233107801499693397)
          ·
            refine ⟨11238633495433012206133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3836120233107801499693397 11238633495433012206133)
            ·
              rfl

theorem cell21_1329645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 10].length) (baseStart_1329645 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1329645 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1329645 prefixEnd_1329645 := by exact prefixLift 1329645
  have htrace : WordTrace (prefixWord ++ tailWord_1329645) baseStart_1329645 baseEnd_1329645 := by
    simpa [prefixWord, tailWord_1329645, baseEnd_1329645] using wordTrace_append hprefix tailTrace_1329645
  have hstable : (prefixWord ++ tailWord_1329645).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329645).length < 2 ^ (prefixWord ++ tailWord_1329645).sum := by decide
  have hdescent : baseEnd_1329645 < baseStart_1329645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329676 : List Nat := [2, 2, 1, 2, 4, 2, 1, 2, 5]
def baseStart_1329676 : Nat := 118140960795 + 1329676 * 2 ^ 59
def prefixEnd_1329676 : Nat := 4983230072969 + 3 ^ 40 * 1329676 * 2
def baseEnd_1329676 : Nat := 303450178999042164548861

theorem tailTrace_1329676 : CollatzResearch.WordTrace tailWord_1329676 prefixEnd_1329676 303450178999042164548861 := by
  unfold tailWord_1329676
  simp only [CollatzResearch.WordTrace]
  refine ⟨24248633965409208713152441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32331511953878944950869921 24248633965409208713152441)
  ·
    refine ⟨18186475474056906534864331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24248633965409208713152441 18186475474056906534864331)
    ·
      refine ⟨27279713211085359802296497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18186475474056906534864331 27279713211085359802296497)
      ·
        refine ⟨20459784908314019851722373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27279713211085359802296497 20459784908314019851722373)
        ·
          refine ⟨3836209670308878722197945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20459784908314019851722373 3836209670308878722197945)
          ·
            refine ⟨2877157252731659041648459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3836209670308878722197945 2877157252731659041648459)
            ·
              refine ⟨4315735879097488562472689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2877157252731659041648459 4315735879097488562472689)
              ·
                refine ⟨3236801909323116421854517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4315735879097488562472689 3236801909323116421854517)
                ·
                  refine ⟨303450178999042164548861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3236801909323116421854517 303450178999042164548861)
                  ·
                    rfl

theorem cell21_1329676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 2, 5].length) (baseStart_1329676 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1329676 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1329676 prefixEnd_1329676 := by exact prefixLift 1329676
  have htrace : WordTrace (prefixWord ++ tailWord_1329676) baseStart_1329676 baseEnd_1329676 := by
    simpa [prefixWord, tailWord_1329676, baseEnd_1329676] using wordTrace_append hprefix tailTrace_1329676
  have hstable : (prefixWord ++ tailWord_1329676).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329676).length < 2 ^ (prefixWord ++ tailWord_1329676).sum := by decide
  have hdescent : baseEnd_1329676 < baseStart_1329676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329693 : List Nat := [1, 4, 2, 2, 1, 2, 1, 5, 3]
def baseStart_1329693 : Nat := 118140960795 + 1329693 * 2 ^ 59
def prefixEnd_1329693 : Nat := 4983230072969 + 3 ^ 40 * 1329693 * 2
def baseEnd_1329693 : Nat := 303454058630653912765493

theorem tailTrace_1329693 : CollatzResearch.WordTrace tailWord_1329693 prefixEnd_1329693 303454058630653912765493 := by
  unfold tailWord_1329693
  simp only [CollatzResearch.WordTrace]
  refine ⟨48497887971756829329673733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32331925314504552886449155 48497887971756829329673733)
  ·
    refine ⟨9093353994704405499313825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48497887971756829329673733 9093353994704405499313825)
    ·
      refine ⟨6820015496028304124485369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9093353994704405499313825 6820015496028304124485369)
      ·
        refine ⟨5115011622021228093364027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6820015496028304124485369 5115011622021228093364027)
        ·
          refine ⟨7672517433031842140046041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5115011622021228093364027 7672517433031842140046041)
          ·
            refine ⟨5754388074773881605034531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7672517433031842140046041 5754388074773881605034531)
            ·
              refine ⟨8631582112160822407551797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5754388074773881605034531 8631582112160822407551797)
              ·
                refine ⟨809210823015077100707981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8631582112160822407551797 809210823015077100707981)
                ·
                  refine ⟨303454058630653912765493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 809210823015077100707981 303454058630653912765493)
                  ·
                    rfl

theorem cell21_1329693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 5, 3].length) (baseStart_1329693 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1329693 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1329693 prefixEnd_1329693 := by exact prefixLift 1329693
  have htrace : WordTrace (prefixWord ++ tailWord_1329693) baseStart_1329693 baseEnd_1329693 := by
    simpa [prefixWord, tailWord_1329693, baseEnd_1329693] using wordTrace_append hprefix tailTrace_1329693
  have hstable : (prefixWord ++ tailWord_1329693).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329693).length < 2 ^ (prefixWord ++ tailWord_1329693).sum := by decide
  have hdescent : baseEnd_1329693 < baseStart_1329693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329724 : List Nat := [2, 2, 2, 2, 3, 2, 3, 1, 4]
def baseStart_1329724 : Nat := 118140960795 + 1329724 * 2 ^ 59
def prefixEnd_1329724 : Nat := 4983230072969 + 3 ^ 40 * 1329724 * 2
def baseEnd_1329724 : Nat := 303461133253004747748763

theorem tailTrace_1329724 : CollatzResearch.WordTrace tailWord_1329724 prefixEnd_1329724 303461133253004747748763 := by
  unfold tailWord_1329724
  simp only [CollatzResearch.WordTrace]
  refine ⟨24249509317322260812026113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32332679089763014416034817 24249509317322260812026113)
  ·
    refine ⟨18187131987991695609019585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24249509317322260812026113 18187131987991695609019585)
    ·
      refine ⟨13640348990993771706764689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18187131987991695609019585 13640348990993771706764689)
      ·
        refine ⟨10230261743245328780073517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13640348990993771706764689 10230261743245328780073517)
        ·
          refine ⟨3836348153716998292527569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10230261743245328780073517 3836348153716998292527569)
          ·
            refine ⟨2877261115287748719395677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3836348153716998292527569 2877261115287748719395677)
            ·
              refine ⟨1078972918232905769773379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2877261115287748719395677 1078972918232905769773379)
              ·
                refine ⟨1618459377349358654660069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1078972918232905769773379 1618459377349358654660069)
                ·
                  refine ⟨303461133253004747748763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1618459377349358654660069 303461133253004747748763)
                  ·
                    rfl

theorem cell21_1329724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 3, 1, 4].length) (baseStart_1329724 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1329724 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1329724 prefixEnd_1329724 := by exact prefixLift 1329724
  have htrace : WordTrace (prefixWord ++ tailWord_1329724) baseStart_1329724 baseEnd_1329724 := by
    simpa [prefixWord, tailWord_1329724, baseEnd_1329724] using wordTrace_append hprefix tailTrace_1329724
  have hstable : (prefixWord ++ tailWord_1329724).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329724).length < 2 ^ (prefixWord ++ tailWord_1329724).sum := by decide
  have hdescent : baseEnd_1329724 < baseStart_1329724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329738 : List Nat := [3, 1, 2, 1, 1, 6, 2, 5]
def baseStart_1329738 : Nat := 118140960795 + 1329738 * 2 ^ 59
def prefixEnd_1329738 : Nat := 4983230072969 + 3 ^ 40 * 1329738 * 2
def baseEnd_1329738 : Nat := 101154776081247944838467

theorem tailTrace_1329738 : CollatzResearch.WordTrace tailWord_1329738 prefixEnd_1329738 101154776081247944838467 := by
  unfold tailWord_1329738
  simp only [CollatzResearch.WordTrace]
  refine ⟨12124882314148450503765467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32333019504395868010041245 12124882314148450503765467)
  ·
    refine ⟨18187323471222675755648201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12124882314148450503765467 18187323471222675755648201)
    ·
      refine ⟨13640492603417006816736151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18187323471222675755648201 13640492603417006816736151)
      ·
        refine ⟨20460738905125510225104227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13640492603417006816736151 20460738905125510225104227)
        ·
          refine ⟨30691108357688265337656341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20460738905125510225104227 30691108357688265337656341)
          ·
            refine ⟨1438645704266637437702641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 30691108357688265337656341 1438645704266637437702641)
            ·
              refine ⟨1078984278199978078276981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1438645704266637437702641 1078984278199978078276981)
              ·
                refine ⟨101154776081247944838467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1078984278199978078276981 101154776081247944838467)
                ·
                  rfl

theorem cell21_1329738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 2, 5].length) (baseStart_1329738 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1329738 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1329738 prefixEnd_1329738 := by exact prefixLift 1329738
  have htrace : WordTrace (prefixWord ++ tailWord_1329738) baseStart_1329738 baseEnd_1329738 := by
    simpa [prefixWord, tailWord_1329738, baseEnd_1329738] using wordTrace_append hprefix tailTrace_1329738
  have hstable : (prefixWord ++ tailWord_1329738).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329738).length < 2 ^ (prefixWord ++ tailWord_1329738).sum := by decide
  have hdescent : baseEnd_1329738 < baseStart_1329738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329783 : List Nat := [1, 1, 3, 1, 1, 3, 6, 1, 4]
def baseStart_1329783 : Nat := 118140960795 + 1329783 * 2 ^ 59
def prefixEnd_1329783 : Nat := 4983230072969 + 3 ^ 40 * 1329783 * 2
def baseEnd_1329783 : Nat := 303474597856833756265309

theorem tailTrace_1329783 : CollatzResearch.WordTrace tailWord_1329783 prefixEnd_1329783 303474597856833756265309 := by
  unfold tailWord_1329783
  simp only [CollatzResearch.WordTrace]
  refine ⟨48501170541430774700450003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32334113694287183133633335 48501170541430774700450003)
  ·
    refine ⟨72751755812146162050675005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48501170541430774700450003 72751755812146162050675005)
    ·
      refine ⟨27281908429554810769003127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72751755812146162050675005 27281908429554810769003127)
      ·
        refine ⟨40922862644332216153504691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27281908429554810769003127 40922862644332216153504691)
        ·
          refine ⟨61384293966498324230257037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40922862644332216153504691 61384293966498324230257037)
          ·
            refine ⟨23019110237436871586346389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61384293966498324230257037 23019110237436871586346389)
            ·
              refine ⟨1079020792379853355609987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 23019110237436871586346389 1079020792379853355609987)
              ·
                refine ⟨1618531188569780033414981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1079020792379853355609987 1618531188569780033414981)
                ·
                  refine ⟨303474597856833756265309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1618531188569780033414981 303474597856833756265309)
                  ·
                    rfl

theorem cell21_1329783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 6, 1, 4].length) (baseStart_1329783 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1329783 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1329783 prefixEnd_1329783 := by exact prefixLift 1329783
  have htrace : WordTrace (prefixWord ++ tailWord_1329783) baseStart_1329783 baseEnd_1329783 := by
    simpa [prefixWord, tailWord_1329783, baseEnd_1329783] using wordTrace_append hprefix tailTrace_1329783
  have hstable : (prefixWord ++ tailWord_1329783).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329783).length < 2 ^ (prefixWord ++ tailWord_1329783).sum := by decide
  have hdescent : baseEnd_1329783 < baseStart_1329783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329831 : List Nat := [1, 1, 6, 3, 1, 2, 1, 6]
def baseStart_1329831 : Nat := 118140960795 + 1329831 * 2 ^ 59
def prefixEnd_1329831 : Nat := 4983230072969 + 3 ^ 40 * 1329831 * 2
def baseEnd_1329831 : Nat := 101161850703598779821737

theorem tailTrace_1329831 : CollatzResearch.WordTrace tailWord_1329831 prefixEnd_1329831 101161850703598779821737 := by
  unfold tailWord_1329831
  simp only [CollatzResearch.WordTrace]
  refine ⟨48502921245256878898197347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32335280830171252598798231 48502921245256878898197347)
  ·
    refine ⟨72754381867885318347296021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48502921245256878898197347 72754381867885318347296021)
    ·
      refine ⟨3410361650057124297529501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 72754381867885318347296021 3410361650057124297529501)
      ·
        refine ⟨1278885618771421611573563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3410361650057124297529501 1278885618771421611573563)
        ·
          refine ⟨1918328428157132417360345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1278885618771421611573563 1918328428157132417360345)
          ·
            refine ⟨1438746321117849313020259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1918328428157132417360345 1438746321117849313020259)
            ·
              refine ⟨2158119481676773969530389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1438746321117849313020259 2158119481676773969530389)
              ·
                refine ⟨101161850703598779821737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2158119481676773969530389 101161850703598779821737)
                ·
                  rfl

theorem cell21_1329831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 6].length) (baseStart_1329831 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1329831 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1329831 prefixEnd_1329831 := by exact prefixLift 1329831
  have htrace : WordTrace (prefixWord ++ tailWord_1329831) baseStart_1329831 baseEnd_1329831 := by
    simpa [prefixWord, tailWord_1329831, baseEnd_1329831] using wordTrace_append hprefix tailTrace_1329831
  have hstable : (prefixWord ++ tailWord_1329831).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329831).length < 2 ^ (prefixWord ++ tailWord_1329831).sum := by decide
  have hdescent : baseEnd_1329831 < baseStart_1329831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329887 : List Nat := [1, 1, 2, 3, 2, 3, 1, 3, 5]
def baseStart_1329887 : Nat := 118140960795 + 1329887 * 2 ^ 59
def prefixEnd_1329887 : Nat := 4983230072969 + 3 ^ 40 * 1329887 * 2
def baseEnd_1329887 : Nat := 303498332073752686531763

theorem tailTrace_1329887 : CollatzResearch.WordTrace tailWord_1329887 prefixEnd_1329887 303498332073752686531763 := by
  unfold tailWord_1329887
  simp only [CollatzResearch.WordTrace]
  refine ⟨48504963733054000462235915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32336642488702666974823943 48504963733054000462235915)
  ·
    refine ⟨72757445599581000693353873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48504963733054000462235915 72757445599581000693353873)
    ·
      refine ⟨54568084199685750520015405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72757445599581000693353873 54568084199685750520015405)
      ·
        refine ⟨20463031574882156445005777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54568084199685750520015405 20463031574882156445005777)
        ·
          refine ⟨15347273681161617333754333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20463031574882156445005777 15347273681161617333754333)
          ·
            refine ⟨5755227630435606500157875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15347273681161617333754333 5755227630435606500157875)
            ·
              refine ⟨8632841445653409750236813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5755227630435606500157875 8632841445653409750236813)
              ·
                refine ⟨3237315542120028656338805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8632841445653409750236813 3237315542120028656338805)
                ·
                  refine ⟨303498332073752686531763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3237315542120028656338805 303498332073752686531763)
                  ·
                    rfl

theorem cell21_1329887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 3, 5].length) (baseStart_1329887 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1329887 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1329887 prefixEnd_1329887 := by exact prefixLift 1329887
  have htrace : WordTrace (prefixWord ++ tailWord_1329887) baseStart_1329887 baseEnd_1329887 := by
    simpa [prefixWord, tailWord_1329887, baseEnd_1329887] using wordTrace_append hprefix tailTrace_1329887
  have hstable : (prefixWord ++ tailWord_1329887).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329887).length < 2 ^ (prefixWord ++ tailWord_1329887).sum := by decide
  have hdescent : baseEnd_1329887 < baseStart_1329887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329938 : List Nat := [3, 2, 4, 1, 2, 2, 1, 1, 5]
def baseStart_1329938 : Nat := 118140960795 + 1329938 * 2 ^ 59
def prefixEnd_1329938 : Nat := 4983230072969 + 3 ^ 40 * 1329938 * 2
def baseEnd_1329938 : Nat := 303509970968587931181659

theorem tailTrace_1329938 : CollatzResearch.WordTrace tailWord_1329938 prefixEnd_1329938 303509970968587931181659 := by
  unfold tailWord_1329938
  simp only [CollatzResearch.WordTrace]
  refine ⟨12126705963967309043085617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32337882570579490781561645 12126705963967309043085617)
  ·
    refine ⟨9095029472975481782314213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12126705963967309043085617 9095029472975481782314213)
    ·
      refine ⟨1705318026182902834183915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9095029472975481782314213 1705318026182902834183915)
      ·
        refine ⟨2557977039274354251275873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1705318026182902834183915 2557977039274354251275873)
        ·
          refine ⟨1918482779455765688456905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2557977039274354251275873 1918482779455765688456905)
          ·
            refine ⟨1438862084591824266342679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1918482779455765688456905 1438862084591824266342679)
            ·
              refine ⟨2158293126887736399514019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1438862084591824266342679 2158293126887736399514019)
              ·
                refine ⟨3237439690331604599271029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2158293126887736399514019 3237439690331604599271029)
                ·
                  refine ⟨303509970968587931181659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3237439690331604599271029 303509970968587931181659)
                  ·
                    rfl

theorem cell21_1329938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 1, 5].length) (baseStart_1329938 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1329938 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1329938 prefixEnd_1329938 := by exact prefixLift 1329938
  have htrace : WordTrace (prefixWord ++ tailWord_1329938) baseStart_1329938 baseEnd_1329938 := by
    simpa [prefixWord, tailWord_1329938, baseEnd_1329938] using wordTrace_append hprefix tailTrace_1329938
  have hstable : (prefixWord ++ tailWord_1329938).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329938).length < 2 ^ (prefixWord ++ tailWord_1329938).sum := by decide
  have hdescent : baseEnd_1329938 < baseStart_1329938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329952 : List Nat := [2, 1, 1, 5, 1, 4, 2, 1, 4]
def baseStart_1329952 : Nat := 118140960795 + 1329952 * 2 ^ 59
def prefixEnd_1329952 : Nat := 4983230072969 + 3 ^ 40 * 1329952 * 2
def baseEnd_1329952 : Nat := 303513165959327017948297

theorem tailTrace_1329952 : CollatzResearch.WordTrace tailWord_1329952 prefixEnd_1329952 303513165959327017948297 := by
  unfold tailWord_1329952
  simp only [CollatzResearch.WordTrace]
  refine ⟨24253667238909258281676055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32338222985212344375568073 24253667238909258281676055)
  ·
    refine ⟨36380500858363887422514083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24253667238909258281676055 36380500858363887422514083)
    ·
      refine ⟨54570751287545831133771125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36380500858363887422514083 54570751287545831133771125)
      ·
        refine ⟨5116007933207421668791043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54570751287545831133771125 5116007933207421668791043)
        ·
          refine ⟨7674011899811132503186565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5116007933207421668791043 7674011899811132503186565)
          ·
            refine ⟨1438877231214587344347481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7674011899811132503186565 1438877231214587344347481)
            ·
              refine ⟨1079157923410940508260611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1438877231214587344347481 1079157923410940508260611)
              ·
                refine ⟨1618736885116410762390917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1079157923410940508260611 1618736885116410762390917)
                ·
                  refine ⟨303513165959327017948297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1618736885116410762390917 303513165959327017948297)
                  ·
                    rfl

theorem cell21_1329952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 2, 1, 4].length) (baseStart_1329952 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1329952 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1329952 prefixEnd_1329952 := by exact prefixLift 1329952
  have htrace : WordTrace (prefixWord ++ tailWord_1329952) baseStart_1329952 baseEnd_1329952 := by
    simpa [prefixWord, tailWord_1329952, baseEnd_1329952] using wordTrace_append hprefix tailTrace_1329952
  have hstable : (prefixWord ++ tailWord_1329952).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329952).length < 2 ^ (prefixWord ++ tailWord_1329952).sum := by decide
  have hdescent : baseEnd_1329952 < baseStart_1329952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1329980 : List Nat := [2, 2, 2, 2, 1, 1, 1, 7, 3]
def baseStart_1329980 : Nat := 118140960795 + 1329980 * 2 ^ 59
def prefixEnd_1329980 : Nat := 4983230072969 + 3 ^ 40 * 1329980 * 2
def baseEnd_1329980 : Nat := 303519555940805191481573

theorem tailTrace_1329980 : CollatzResearch.WordTrace tailWord_1329980 prefixEnd_1329980 303519555940805191481573 := by
  unfold tailWord_1329980
  simp only [CollatzResearch.WordTrace]
  refine ⟨24254177860858538672685697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32338903814478051563580929 24254177860858538672685697)
  ·
    refine ⟨18190633395643904004514273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24254177860858538672685697 18190633395643904004514273)
    ·
      refine ⟨13642975046732928003385705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18190633395643904004514273 13642975046732928003385705)
      ·
        refine ⟨10232231285049696002539279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13642975046732928003385705 10232231285049696002539279)
        ·
          refine ⟨15348346927574544003808919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10232231285049696002539279 15348346927574544003808919)
          ·
            refine ⟨23022520391361816005713379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15348346927574544003808919 23022520391361816005713379)
            ·
              refine ⟨34533780587042724008570069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23022520391361816005713379 34533780587042724008570069)
              ·
                refine ⟨809385482508813843950861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 34533780587042724008570069 809385482508813843950861)
                ·
                  refine ⟨303519555940805191481573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 809385482508813843950861 303519555940805191481573)
                  ·
                    rfl

theorem cell21_1329980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 7, 3].length) (baseStart_1329980 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1329980 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1329980 prefixEnd_1329980 := by exact prefixLift 1329980
  have htrace : WordTrace (prefixWord ++ tailWord_1329980) baseStart_1329980 baseEnd_1329980 := by
    simpa [prefixWord, tailWord_1329980, baseEnd_1329980] using wordTrace_append hprefix tailTrace_1329980
  have hstable : (prefixWord ++ tailWord_1329980).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1329980).length < 2 ^ (prefixWord ++ tailWord_1329980).sum := by decide
  have hdescent : baseEnd_1329980 < baseStart_1329980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1329980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330056 : List Nat := [2, 1, 3, 3, 2, 2, 2, 1, 5]
def baseStart_1330056 : Nat := 118140960795 + 1330056 * 2 ^ 59
def prefixEnd_1330056 : Nat := 4983230072969 + 3 ^ 40 * 1330056 * 2
def baseEnd_1330056 : Nat := 303536900176245948214751

theorem tailTrace_1330056 : CollatzResearch.WordTrace tailWord_1330056 prefixEnd_1330056 303536900176245948214751 := by
  unfold tailWord_1330056
  simp only [CollatzResearch.WordTrace]
  refine ⟨24255563834720871162569011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32340751779627828216758681 24255563834720871162569011)
  ·
    refine ⟨36383345752081306743853517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24255563834720871162569011 36383345752081306743853517)
    ·
      refine ⟨13643754657030490028945069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36383345752081306743853517 13643754657030490028945069)
      ·
        refine ⟨5116407996386433760854401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13643754657030490028945069 5116407996386433760854401)
        ·
          refine ⟨3837305997289825320640801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5116407996386433760854401 3837305997289825320640801)
          ·
            refine ⟨2877979497967368990480601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3837305997289825320640801 2877979497967368990480601)
            ·
              refine ⟨2158484623475526742860451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2877979497967368990480601 2158484623475526742860451)
              ·
                refine ⟨3237726935213290114290677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2158484623475526742860451 3237726935213290114290677)
                ·
                  refine ⟨303536900176245948214751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3237726935213290114290677 303536900176245948214751)
                  ·
                    rfl

theorem cell21_1330056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 1, 5].length) (baseStart_1330056 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1330056 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1330056 prefixEnd_1330056 := by exact prefixLift 1330056
  have htrace : WordTrace (prefixWord ++ tailWord_1330056) baseStart_1330056 baseEnd_1330056 := by
    simpa [prefixWord, tailWord_1330056, baseEnd_1330056] using wordTrace_append hprefix tailTrace_1330056
  have hstable : (prefixWord ++ tailWord_1330056).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330056).length < 2 ^ (prefixWord ++ tailWord_1330056).sum := by decide
  have hdescent : baseEnd_1330056 < baseStart_1330056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330084 : List Nat := [2, 3, 1, 2, 1, 2, 3, 7]
def baseStart_1330084 : Nat := 118140960795 + 1330084 * 2 ^ 59
def prefixEnd_1330084 : Nat := 4983230072969 + 3 ^ 40 * 1330084 * 2
def baseEnd_1330084 : Nat := 101181096719241373916009

theorem tailTrace_1330084 : CollatzResearch.WordTrace tailWord_1330084 prefixEnd_1330084 101181096719241373916009 := by
  unfold tailWord_1330084
  simp only [CollatzResearch.WordTrace]
  refine ⟨24256074456670151553578653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32341432608893535404771537 24256074456670151553578653)
  ·
    refine ⟨9096027921251306832591995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24256074456670151553578653 9096027921251306832591995)
    ·
      refine ⟨13644041881876960248887993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9096027921251306832591995 13644041881876960248887993)
      ·
        refine ⟨10233031411407720186665995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13644041881876960248887993 10233031411407720186665995)
        ·
          refine ⟨15349547117111580279998993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10233031411407720186665995 15349547117111580279998993)
          ·
            refine ⟨11512160337833685209999245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15349547117111580279998993 11512160337833685209999245)
            ·
              refine ⟨4317060126687631953749717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11512160337833685209999245 4317060126687631953749717)
              ·
                refine ⟨101181096719241373916009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4317060126687631953749717 101181096719241373916009)
                ·
                  rfl

theorem cell21_1330084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 7].length) (baseStart_1330084 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1330084 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1330084 prefixEnd_1330084 := by exact prefixLift 1330084
  have htrace : WordTrace (prefixWord ++ tailWord_1330084) baseStart_1330084 baseEnd_1330084 := by
    simpa [prefixWord, tailWord_1330084, baseEnd_1330084] using wordTrace_append hprefix tailTrace_1330084
  have hstable : (prefixWord ++ tailWord_1330084).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330084).length < 2 ^ (prefixWord ++ tailWord_1330084).sum := by decide
  have hdescent : baseEnd_1330084 < baseStart_1330084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330166 : List Nat := [5, 1, 1, 1, 3, 1, 4, 2, 3]
def baseStart_1330166 : Nat := 118140960795 + 1330166 * 2 ^ 59
def prefixEnd_1330166 : Nat := 4983230072969 + 3 ^ 40 * 1330166 * 2
def baseEnd_1330166 : Nat := 303562003674910201381193

theorem tailTrace_1330166 : CollatzResearch.WordTrace tailWord_1330166 prefixEnd_1330166 303562003674910201381193 := by
  unfold tailWord_1330166
  simp only [CollatzResearch.WordTrace]
  refine ⟨3032196231190201944477647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32343426466028820741094901 3032196231190201944477647)
  ·
    refine ⟨4548294346785302916716471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3032196231190201944477647 4548294346785302916716471)
    ·
      refine ⟨6822441520177954375074707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4548294346785302916716471 6822441520177954375074707)
      ·
        refine ⟨10233662280266931562612061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6822441520177954375074707 10233662280266931562612061)
        ·
          refine ⟨3837623355100099335979523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10233662280266931562612061 3837623355100099335979523)
          ·
            refine ⟨5756435032650149003969285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3837623355100099335979523 5756435032650149003969285)
            ·
              refine ⟨1079331568621902938244241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5756435032650149003969285 1079331568621902938244241)
              ·
                refine ⟨809498676466427203683181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1079331568621902938244241 809498676466427203683181)
                ·
                  refine ⟨303562003674910201381193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 809498676466427203683181 303562003674910201381193)
                  ·
                    rfl

theorem cell21_1330166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 4, 2, 3].length) (baseStart_1330166 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1330166 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1330166 prefixEnd_1330166 := by exact prefixLift 1330166
  have htrace : WordTrace (prefixWord ++ tailWord_1330166) baseStart_1330166 baseEnd_1330166 := by
    simpa [prefixWord, tailWord_1330166, baseEnd_1330166] using wordTrace_append hprefix tailTrace_1330166
  have hstable : (prefixWord ++ tailWord_1330166).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330166).length < 2 ^ (prefixWord ++ tailWord_1330166).sum := by decide
  have hdescent : baseEnd_1330166 < baseStart_1330166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330177 : List Nat := [1, 2, 4, 1, 2, 4, 1, 6]
def baseStart_1330177 : Nat := 118140960795 + 1330177 * 2 ^ 59
def prefixEnd_1330177 : Nat := 4983230072969 + 3 ^ 40 * 1330177 * 2
def baseEnd_1330177 : Nat := 101188171341592208899279

theorem tailTrace_1330177 : CollatzResearch.WordTrace tailWord_1330177 prefixEnd_1330177 101188171341592208899279 := by
  unfold tailWord_1330177
  simp only [CollatzResearch.WordTrace]
  refine ⟨48515540902003379990292785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32343693934668919993528523 48515540902003379990292785)
  ·
    refine ⟨36386655676502534992719589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48515540902003379990292785 36386655676502534992719589)
    ·
      refine ⟨6822497939344225311134923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36386655676502534992719589 6822497939344225311134923)
      ·
        refine ⟨10233746909016337966702385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6822497939344225311134923 10233746909016337966702385)
        ·
          refine ⟨7675310181762253475026789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10233746909016337966702385 7675310181762253475026789)
          ·
            refine ⟨1439120659080422526567523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7675310181762253475026789 1439120659080422526567523)
            ·
              refine ⟨2158680988620633789851285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1439120659080422526567523 2158680988620633789851285)
              ·
                refine ⟨101188171341592208899279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2158680988620633789851285 101188171341592208899279)
                ·
                  rfl

theorem cell21_1330177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 6].length) (baseStart_1330177 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1330177 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1330177 prefixEnd_1330177 := by exact prefixLift 1330177
  have htrace : WordTrace (prefixWord ++ tailWord_1330177) baseStart_1330177 baseEnd_1330177 := by
    simpa [prefixWord, tailWord_1330177, baseEnd_1330177] using wordTrace_append hprefix tailTrace_1330177
  have hstable : (prefixWord ++ tailWord_1330177).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330177).length < 2 ^ (prefixWord ++ tailWord_1330177).sum := by decide
  have hdescent : baseEnd_1330177 < baseStart_1330177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330219 : List Nat := [1, 1, 1, 1, 2, 1, 14]
def baseStart_1330219 : Nat := 118140960795 + 1330219 * 2 ^ 59
def prefixEnd_1330219 : Nat := 4983230072969 + 3 ^ 40 * 1330219 * 2
def baseEnd_1330219 : Nat := 33730455444110431888639

theorem tailTrace_1330219 : CollatzResearch.WordTrace tailWord_1330219 prefixEnd_1330219 33730455444110431888639 := by
  unfold tailWord_1330219
  simp only [CollatzResearch.WordTrace]
  refine ⟨48517072767851221163321711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32344715178567480775547807 48517072767851221163321711)
  ·
    refine ⟨72775609151776831744982567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48517072767851221163321711 72775609151776831744982567)
    ·
      refine ⟨109163413727665247617473851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72775609151776831744982567 109163413727665247617473851)
      ·
        refine ⟨163745120591497871426210777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109163413727665247617473851 163745120591497871426210777)
        ·
          refine ⟨122808840443623403569658083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163745120591497871426210777 122808840443623403569658083)
          ·
            refine ⟨184213260665435105354487125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122808840443623403569658083 184213260665435105354487125)
            ·
              refine ⟨33730455444110431888639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 184213260665435105354487125 33730455444110431888639)
              ·
                rfl

theorem cell21_1330219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 14].length) (baseStart_1330219 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1330219 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1330219 prefixEnd_1330219 := by exact prefixLift 1330219
  have htrace : WordTrace (prefixWord ++ tailWord_1330219) baseStart_1330219 baseEnd_1330219 := by
    simpa [prefixWord, tailWord_1330219, baseEnd_1330219] using wordTrace_append hprefix tailTrace_1330219
  have hstable : (prefixWord ++ tailWord_1330219).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330219).length < 2 ^ (prefixWord ++ tailWord_1330219).sum := by decide
  have hdescent : baseEnd_1330219 < baseStart_1330219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330222 : List Nat := [4, 1, 3, 1, 1, 1, 3, 1, 6]
def baseStart_1330222 : Nat := 118140960795 + 1330222 * 2 ^ 59
def prefixEnd_1330222 : Nat := 4983230072969 + 3 ^ 40 * 1330222 * 2
def baseEnd_1330222 : Nat := 303574783637866548447745

theorem tailTrace_1330222 : CollatzResearch.WordTrace tailWord_1330222 prefixEnd_1330222 303574783637866548447745 := by
  unfold tailWord_1330222
  simp only [CollatzResearch.WordTrace]
  refine ⟨6064647773355044084460115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32344788124560235117120613 6064647773355044084460115)
  ·
    refine ⟨9096971660032566126690173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6064647773355044084460115 9096971660032566126690173)
    ·
      refine ⟨3411364372512212297508815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9096971660032566126690173 3411364372512212297508815)
      ·
        refine ⟨5117046558768318446263223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3411364372512212297508815 5117046558768318446263223)
        ·
          refine ⟨7675569838152477669394835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5117046558768318446263223 7675569838152477669394835)
          ·
            refine ⟨11513354757228716504092253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7675569838152477669394835 11513354757228716504092253)
            ·
              refine ⟨4317508033960768689034595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11513354757228716504092253 4317508033960768689034595)
              ·
                refine ⟨6476262050941153033551893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4317508033960768689034595 6476262050941153033551893)
                ·
                  refine ⟨303574783637866548447745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6476262050941153033551893 303574783637866548447745)
                  ·
                    rfl

theorem cell21_1330222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 1, 6].length) (baseStart_1330222 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1330222 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1330222 prefixEnd_1330222 := by exact prefixLift 1330222
  have htrace : WordTrace (prefixWord ++ tailWord_1330222) baseStart_1330222 baseEnd_1330222 := by
    simpa [prefixWord, tailWord_1330222, baseEnd_1330222] using wordTrace_append hprefix tailTrace_1330222
  have hstable : (prefixWord ++ tailWord_1330222).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330222).length < 2 ^ (prefixWord ++ tailWord_1330222).sum := by decide
  have hdescent : baseEnd_1330222 < baseStart_1330222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330253 : List Nat := [1, 6, 1, 1, 1, 3, 1, 7]
def baseStart_1330253 : Nat := 118140960795 + 1330253 * 2 ^ 59
def prefixEnd_1330253 : Nat := 4983230072969 + 3 ^ 40 * 1330253 * 2
def baseEnd_1330253 : Nat := 101193952753405794477005

theorem tailTrace_1330253 : CollatzResearch.WordTrace tailWord_1330253 prefixEnd_1330253 101193952753405794477005 := by
  unfold tailWord_1330253
  simp only [CollatzResearch.WordTrace]
  refine ⟨48518312849728044970059413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32345541899818696646706275 48518312849728044970059413)
  ·
    refine ⟨2274295914831002107971535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 48518312849728044970059413 2274295914831002107971535)
    ·
      refine ⟨3411443872246503161957303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2274295914831002107971535 3411443872246503161957303)
      ·
        refine ⟨5117165808369754742935955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3411443872246503161957303 5117165808369754742935955)
        ·
          refine ⟨7675748712554632114403933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5117165808369754742935955 7675748712554632114403933)
          ·
            refine ⟨2878405767207987042901475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7675748712554632114403933 2878405767207987042901475)
            ·
              refine ⟨4317608650811980564352213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2878405767207987042901475 4317608650811980564352213)
              ·
                refine ⟨101193952753405794477005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4317608650811980564352213 101193952753405794477005)
                ·
                  rfl

theorem cell21_1330253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 7].length) (baseStart_1330253 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1330253 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1330253 prefixEnd_1330253 := by exact prefixLift 1330253
  have htrace : WordTrace (prefixWord ++ tailWord_1330253) baseStart_1330253 baseEnd_1330253 := by
    simpa [prefixWord, tailWord_1330253, baseEnd_1330253] using wordTrace_append hprefix tailTrace_1330253
  have hstable : (prefixWord ++ tailWord_1330253).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330253).length < 2 ^ (prefixWord ++ tailWord_1330253).sum := by decide
  have hdescent : baseEnd_1330253 < baseStart_1330253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330270 : List Nat := [4, 4, 1, 1, 1, 1, 9]
def baseStart_1330270 : Nat := 118140960795 + 1330270 * 2 ^ 59
def prefixEnd_1330270 : Nat := 4983230072969 + 3 ^ 40 * 1330270 * 2
def baseEnd_1330270 : Nat := 33731748654647681294183

theorem tailTrace_1330270 : CollatzResearch.WordTrace tailWord_1330270 prefixEnd_1330270 33731748654647681294183 := by
  unfold tailWord_1330270
  simp only [CollatzResearch.WordTrace]
  refine ⟨6064866611333307109178533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32345955260444304582285509 6064866611333307109178533)
  ·
    refine ⟨1137162489624995082970975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6064866611333307109178533 1137162489624995082970975)
    ·
      refine ⟨1705743734437492624456463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1137162489624995082970975 1705743734437492624456463)
      ·
        refine ⟨2558615601656238936684695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1705743734437492624456463 2558615601656238936684695)
        ·
          refine ⟨3837923402484358405027043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2558615601656238936684695 3837923402484358405027043)
          ·
            refine ⟨5756885103726537607540565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3837923402484358405027043 5756885103726537607540565)
            ·
              refine ⟨33731748654647681294183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5756885103726537607540565 33731748654647681294183)
              ·
                rfl

theorem cell21_1330270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 9].length) (baseStart_1330270 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1330270 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1330270 prefixEnd_1330270 := by exact prefixLift 1330270
  have htrace : WordTrace (prefixWord ++ tailWord_1330270) baseStart_1330270 baseEnd_1330270 := by
    simpa [prefixWord, tailWord_1330270, baseEnd_1330270] using wordTrace_append hprefix tailTrace_1330270
  have hstable : (prefixWord ++ tailWord_1330270).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330270).length < 2 ^ (prefixWord ++ tailWord_1330270).sum := by decide
  have hdescent : baseEnd_1330270 < baseStart_1330270 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330281 : List Nat := [1, 2, 1, 1, 1, 6, 2, 1, 6]
def baseStart_1330281 : Nat := 118140960795 + 1330281 * 2 ^ 59
def prefixEnd_1330281 : Nat := 4983230072969 + 3 ^ 40 * 1330281 * 2
def baseEnd_1330281 : Nat := 303588248241695556964291

theorem tailTrace_1330281 : CollatzResearch.WordTrace tailWord_1330281 prefixEnd_1330281 303588248241695556964291 := by
  unfold tailWord_1330281
  simp only [CollatzResearch.WordTrace]
  refine ⟨48519334093626605752078697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32346222729084403834719131 48519334093626605752078697)
  ·
    refine ⟨36389500570219954314059023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48519334093626605752078697 36389500570219954314059023)
    ·
      refine ⟨54584250855329931471088535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36389500570219954314059023 54584250855329931471088535)
      ·
        refine ⟨81876376282994897206632803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54584250855329931471088535 81876376282994897206632803)
        ·
          refine ⟨122814564424492345809949205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81876376282994897206632803 122814564424492345809949205)
          ·
            refine ⟨5756932707398078709841369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 122814564424492345809949205 5756932707398078709841369)
            ·
              refine ⟨4317699530548559032381027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5756932707398078709841369 4317699530548559032381027)
              ·
                refine ⟨6476549295822838548571541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4317699530548559032381027 6476549295822838548571541)
                ·
                  refine ⟨303588248241695556964291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6476549295822838548571541 303588248241695556964291)
                  ·
                    rfl

theorem cell21_1330281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 1, 6].length) (baseStart_1330281 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1330281 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1330281 prefixEnd_1330281 := by exact prefixLift 1330281
  have htrace : WordTrace (prefixWord ++ tailWord_1330281) baseStart_1330281 baseEnd_1330281 := by
    simpa [prefixWord, tailWord_1330281, baseEnd_1330281] using wordTrace_append hprefix tailTrace_1330281
  have hstable : (prefixWord ++ tailWord_1330281).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330281).length < 2 ^ (prefixWord ++ tailWord_1330281).sum := by decide
  have hdescent : baseEnd_1330281 < baseStart_1330281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330335 : List Nat := [1, 1, 2, 6, 3, 1, 2, 2, 3]
def baseStart_1330335 : Nat := 118140960795 + 1330335 * 2 ^ 59
def prefixEnd_1330335 : Nat := 4983230072969 + 3 ^ 40 * 1330335 * 2
def baseEnd_1330335 : Nat := 303600571777403463064181

theorem tailTrace_1330335 : CollatzResearch.WordTrace tailWord_1330335 prefixEnd_1330335 303600571777403463064181 := by
  unfold tailWord_1330335
  simp only [CollatzResearch.WordTrace]
  refine ⟨48521303635430972974544459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32347535756953981983029639 48521303635430972974544459)
  ·
    refine ⟨72781955453146459461816689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48521303635430972974544459 72781955453146459461816689)
    ·
      refine ⟨54586466589859844596362517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72781955453146459461816689 54586466589859844596362517)
      ·
        refine ⟨2558740621399680215454493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 54586466589859844596362517 2558740621399680215454493)
        ·
          refine ⟨959527733024880080795435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2558740621399680215454493 959527733024880080795435)
          ·
            refine ⟨1439291599537320121193153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 959527733024880080795435 1439291599537320121193153)
            ·
              refine ⟨1079468699652990090894865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1439291599537320121193153 1079468699652990090894865)
              ·
                refine ⟨809601524739742568171149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1079468699652990090894865 809601524739742568171149)
                ·
                  refine ⟨303600571777403463064181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 809601524739742568171149 303600571777403463064181)
                  ·
                    rfl

theorem cell21_1330335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 2, 2, 3].length) (baseStart_1330335 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1330335 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1330335 prefixEnd_1330335 := by exact prefixLift 1330335
  have htrace : WordTrace (prefixWord ++ tailWord_1330335) baseStart_1330335 baseEnd_1330335 := by
    simpa [prefixWord, tailWord_1330335, baseEnd_1330335] using wordTrace_append hprefix tailTrace_1330335
  have hstable : (prefixWord ++ tailWord_1330335).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330335).length < 2 ^ (prefixWord ++ tailWord_1330335).sum := by decide
  have hdescent : baseEnd_1330335 < baseStart_1330335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330346 : List Nat := [3, 1, 5, 1, 1, 3, 1, 6]
def baseStart_1330346 : Nat := 118140960795 + 1330346 * 2 ^ 59
def prefixEnd_1330346 : Nat := 4983230072969 + 3 ^ 40 * 1330346 * 2
def baseEnd_1330346 : Nat := 101201027375756629460275

theorem tailTrace_1330346 : CollatzResearch.WordTrace tailWord_1330346 prefixEnd_1330346 101201027375756629460275 := by
  unfold tailWord_1330346
  simp only [CollatzResearch.WordTrace]
  refine ⟨12130426209597780463298723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32347803225594081235463261 12130426209597780463298723)
  ·
    refine ⟨18195639314396670694948085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12130426209597780463298723 18195639314396670694948085)
    ·
      refine ⟨1705841185724687877651383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18195639314396670694948085 1705841185724687877651383)
      ·
        refine ⟨2558761778587031816477075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1705841185724687877651383 2558761778587031816477075)
        ·
          refine ⟨3838142667880547724715613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2558761778587031816477075 3838142667880547724715613)
          ·
            refine ⟨1439303500455205396768355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3838142667880547724715613 1439303500455205396768355)
            ·
              refine ⟨2158955250682808095152533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1439303500455205396768355 2158955250682808095152533)
              ·
                refine ⟨101201027375756629460275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2158955250682808095152533 101201027375756629460275)
                ·
                  rfl

theorem cell21_1330346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 6].length) (baseStart_1330346 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1330346 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1330346 prefixEnd_1330346 := by exact prefixLift 1330346
  have htrace : WordTrace (prefixWord ++ tailWord_1330346) baseStart_1330346 baseEnd_1330346 := by
    simpa [prefixWord, tailWord_1330346, baseEnd_1330346] using wordTrace_append hprefix tailTrace_1330346
  have hstable : (prefixWord ++ tailWord_1330346).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330346).length < 2 ^ (prefixWord ++ tailWord_1330346).sum := by decide
  have hdescent : baseEnd_1330346 < baseStart_1330346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330433 : List Nat := [1, 2, 4, 1, 1, 3, 1, 2, 6]
def baseStart_1330433 : Nat := 118140960795 + 1330433 * 2 ^ 59
def prefixEnd_1330433 : Nat := 4983230072969 + 3 ^ 40 * 1330433 * 2
def baseEnd_1330433 : Nat := 303622936712577070430647

theorem tailTrace_1330433 : CollatzResearch.WordTrace tailWord_1330433 prefixEnd_1330433 303622936712577070430647 := by
  unfold tailWord_1330433
  simp only [CollatzResearch.WordTrace]
  refine ⟨48524877989075935711611953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32349918659383957141074635 48524877989075935711611953)
  ·
    refine ⟨36393658491806951783708965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48524877989075935711611953 36393658491806951783708965)
    ·
      refine ⟨6823810967213803459445431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36393658491806951783708965 6823810967213803459445431)
      ·
        refine ⟨10235716450820705189168147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6823810967213803459445431 10235716450820705189168147)
        ·
          refine ⟨15353574676231057783752221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10235716450820705189168147 15353574676231057783752221)
          ·
            refine ⟨5757590503586646668907083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15353574676231057783752221 5757590503586646668907083)
            ·
              refine ⟨8636385755379970003360625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5757590503586646668907083 8636385755379970003360625)
              ·
                refine ⟨6477289316534977502520469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8636385755379970003360625 6477289316534977502520469)
                ·
                  refine ⟨303622936712577070430647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6477289316534977502520469 303622936712577070430647)
                  ·
                    rfl

theorem cell21_1330433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 2, 6].length) (baseStart_1330433 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1330433 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1330433 prefixEnd_1330433 := by exact prefixLift 1330433
  have htrace : WordTrace (prefixWord ++ tailWord_1330433) baseStart_1330433 baseEnd_1330433 := by
    simpa [prefixWord, tailWord_1330433, baseEnd_1330433] using wordTrace_append hprefix tailTrace_1330433
  have hstable : (prefixWord ++ tailWord_1330433).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330433).length < 2 ^ (prefixWord ++ tailWord_1330433).sum := by decide
  have hdescent : baseEnd_1330433 < baseStart_1330433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330467 : List Nat := [1, 1, 1, 4, 2, 5, 2, 1, 4]
def baseStart_1330467 : Nat := 118140960795 + 1330467 * 2 ^ 59
def prefixEnd_1330467 : Nat := 4983230072969 + 3 ^ 40 * 1330467 * 2
def baseEnd_1330467 : Nat := 303630695975800566863911

theorem tailTrace_1330467 : CollatzResearch.WordTrace tailWord_1330467 prefixEnd_1330467 303630695975800566863911 := by
  unfold tailWord_1330467
  simp only [CollatzResearch.WordTrace]
  refine ⟨48526118070952759518349655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32350745380635173012233103 48526118070952759518349655)
  ·
    refine ⟨72789177106429139277524483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48526118070952759518349655 72789177106429139277524483)
    ·
      refine ⟨109183765659643708916286725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72789177106429139277524483 109183765659643708916286725)
      ·
        refine ⟨20471956061183195421803761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109183765659643708916286725 20471956061183195421803761)
        ·
          refine ⟨15353967045887396566352821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20471956061183195421803761 15353967045887396566352821)
          ·
            refine ⟨1439434410551943428095577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15353967045887396566352821 1439434410551943428095577)
            ·
              refine ⟨1079575807913957571071683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1439434410551943428095577 1079575807913957571071683)
              ·
                refine ⟨1619363711870936356607525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1079575807913957571071683 1619363711870936356607525)
                ·
                  refine ⟨303630695975800566863911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1619363711870936356607525 303630695975800566863911)
                  ·
                    rfl

theorem cell21_1330467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 2, 1, 4].length) (baseStart_1330467 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1330467 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1330467 prefixEnd_1330467 := by exact prefixLift 1330467
  have htrace : WordTrace (prefixWord ++ tailWord_1330467) baseStart_1330467 baseEnd_1330467 := by
    simpa [prefixWord, tailWord_1330467, baseEnd_1330467] using wordTrace_append hprefix tailTrace_1330467
  have hstable : (prefixWord ++ tailWord_1330467).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330467).length < 2 ^ (prefixWord ++ tailWord_1330467).sum := by decide
  have hdescent : baseEnd_1330467 < baseStart_1330467 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330571 : List Nat := [1, 1, 1, 1, 4, 3, 1, 6, 3]
def baseStart_1330571 : Nat := 118140960795 + 1330571 * 2 ^ 59
def prefixEnd_1330571 : Nat := 4983230072969 + 3 ^ 40 * 1330571 * 2
def baseEnd_1330571 : Nat := 303654430192719497130365

theorem tailTrace_1330571 : CollatzResearch.WordTrace tailWord_1330571 prefixEnd_1330571 303654430192719497130365 := by
  unfold tailWord_1330571
  simp only [CollatzResearch.WordTrace]
  refine ⟨48529911262575985280135567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32353274175050656853423711 48529911262575985280135567)
  ·
    refine ⟨72794866893863977920203351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48529911262575985280135567 72794866893863977920203351)
    ·
      refine ⟨109192300340795966880305027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72794866893863977920203351 109192300340795966880305027)
      ·
        refine ⟨163788450511193950320457541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109192300340795966880305027 163788450511193950320457541)
        ·
          refine ⟨30710334470848865685085789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 163788450511193950320457541 30710334470848865685085789)
          ·
            refine ⟨11516375426568324631907171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30710334470848865685085789 11516375426568324631907171)
            ·
              refine ⟨17274563139852486947860757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11516375426568324631907171 17274563139852486947860757)
              ·
                refine ⟨809745147180585325680973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17274563139852486947860757 809745147180585325680973)
                ·
                  refine ⟨303654430192719497130365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 809745147180585325680973 303654430192719497130365)
                  ·
                    rfl

theorem cell21_1330571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 6, 3].length) (baseStart_1330571 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1330571 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1330571 prefixEnd_1330571 := by exact prefixLift 1330571
  have htrace : WordTrace (prefixWord ++ tailWord_1330571) baseStart_1330571 baseEnd_1330571 := by
    simpa [prefixWord, tailWord_1330571, baseEnd_1330571] using wordTrace_append hprefix tailTrace_1330571
  have hstable : (prefixWord ++ tailWord_1330571).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330571).length < 2 ^ (prefixWord ++ tailWord_1330571).sum := by decide
  have hdescent : baseEnd_1330571 < baseStart_1330571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330605 : List Nat := [1, 5, 2, 2, 1, 1, 3, 3, 3]
def baseStart_1330605 : Nat := 118140960795 + 1330605 * 2 ^ 59
def prefixEnd_1330605 : Nat := 4983230072969 + 3 ^ 40 * 1330605 * 2
def baseEnd_1330605 : Nat := 303662189455942993563629

theorem tailTrace_1330605 : CollatzResearch.WordTrace tailWord_1330605 prefixEnd_1330605 303662189455942993563629 := by
  unfold tailWord_1330605
  simp only [CollatzResearch.WordTrace]
  refine ⟨48531151344452809086873269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32354100896301872724582179 48531151344452809086873269)
  ·
    refine ⟨4549795438542450851894369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48531151344452809086873269 4549795438542450851894369)
    ·
      refine ⟨3412346578906838138920777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4549795438542450851894369 3412346578906838138920777)
      ·
        refine ⟨2559259934180128604190583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3412346578906838138920777 2559259934180128604190583)
        ·
          refine ⟨3838889901270192906285875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2559259934180128604190583 3838889901270192906285875)
          ·
            refine ⟨5758334851905289359428813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3838889901270192906285875 5758334851905289359428813)
            ·
              refine ⟨2159375569464483509785805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5758334851905289359428813 2159375569464483509785805)
              ·
                refine ⟨809765838549181316169677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2159375569464483509785805 809765838549181316169677)
                ·
                  refine ⟨303662189455942993563629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 809765838549181316169677 303662189455942993563629)
                  ·
                    rfl

theorem cell21_1330605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 3, 3].length) (baseStart_1330605 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1330605 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1330605 prefixEnd_1330605 := by exact prefixLift 1330605
  have htrace : WordTrace (prefixWord ++ tailWord_1330605) baseStart_1330605 baseEnd_1330605 := by
    simpa [prefixWord, tailWord_1330605, baseEnd_1330605] using wordTrace_append hprefix tailTrace_1330605
  have hstable : (prefixWord ++ tailWord_1330605).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330605).length < 2 ^ (prefixWord ++ tailWord_1330605).sum := by decide
  have hdescent : baseEnd_1330605 < baseStart_1330605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330678 : List Nat := [5, 1, 1, 1, 2, 2, 1, 4, 4]
def baseStart_1330678 : Nat := 118140960795 + 1330678 * 2 ^ 59
def prefixEnd_1330678 : Nat := 4983230072969 + 3 ^ 40 * 1330678 * 2
def baseEnd_1330678 : Nat := 303678849050511088846813

theorem tailTrace_1330678 : CollatzResearch.WordTrace tailWord_1330678 prefixEnd_1330678 303678849050511088846813 := by
  unfold tailWord_1330678
  simp only [CollatzResearch.WordTrace]
  refine ⟨3033363367074271409642543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32355875915458895036187125 3033363367074271409642543)
  ·
    refine ⟨4550045050611407114463815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3033363367074271409642543 4550045050611407114463815)
    ·
      refine ⟨6825067575917110671695723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4550045050611407114463815 6825067575917110671695723)
      ·
        refine ⟨10237601363875666007543585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6825067575917110671695723 10237601363875666007543585)
        ·
          refine ⟨7678201022906749505657689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10237601363875666007543585 7678201022906749505657689)
          ·
            refine ⟨5758650767180062129243267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7678201022906749505657689 5758650767180062129243267)
            ·
              refine ⟨8637976150770093193864901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5758650767180062129243267 8637976150770093193864901)
              ·
                refine ⟨1619620528269392473849669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8637976150770093193864901 1619620528269392473849669)
                ·
                  refine ⟨303678849050511088846813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1619620528269392473849669 303678849050511088846813)
                  ·
                    rfl

theorem cell21_1330678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_1330678 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1330678 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1330678 prefixEnd_1330678 := by exact prefixLift 1330678
  have htrace : WordTrace (prefixWord ++ tailWord_1330678) baseStart_1330678 baseEnd_1330678 := by
    simpa [prefixWord, tailWord_1330678, baseEnd_1330678] using wordTrace_append hprefix tailTrace_1330678
  have hstable : (prefixWord ++ tailWord_1330678).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330678).length < 2 ^ (prefixWord ++ tailWord_1330678).sum := by decide
  have hdescent : baseEnd_1330678 < baseStart_1330678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330841 : List Nat := [1, 2, 1, 2, 1, 2, 2, 1, 9]
def baseStart_1330841 : Nat := 118140960795 + 1330841 * 2 ^ 59
def prefixEnd_1330841 : Nat := 4983230072969 + 3 ^ 40 * 1330841 * 2
def baseEnd_1330841 : Nat := 303716047871259027629813

theorem tailTrace_1330841 : CollatzResearch.WordTrace tailWord_1330841 prefixEnd_1330841 303716047871259027629813 := by
  unfold tailWord_1330841
  simp only [CollatzResearch.WordTrace]
  refine ⟨48539758971597821392464377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32359839314398547594976251 48539758971597821392464377)
  ·
    refine ⟨36404819228698366044348283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48539758971597821392464377 36404819228698366044348283)
    ·
      refine ⟨54607228843047549066522425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36404819228698366044348283 54607228843047549066522425)
      ·
        refine ⟨40955421632285661799891819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54607228843047549066522425 40955421632285661799891819)
        ·
          refine ⟨61433132448428492699837729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40955421632285661799891819 61433132448428492699837729)
          ·
            refine ⟨46074849336321369524878297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61433132448428492699837729 46074849336321369524878297)
            ·
              refine ⟨34556137002241027143658723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46074849336321369524878297 34556137002241027143658723)
              ·
                refine ⟨51834205503361540715488085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34556137002241027143658723 51834205503361540715488085)
                ·
                  refine ⟨303716047871259027629813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 51834205503361540715488085 303716047871259027629813)
                  ·
                    rfl

theorem cell21_1330841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 9].length) (baseStart_1330841 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1330841 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1330841 prefixEnd_1330841 := by exact prefixLift 1330841
  have htrace : WordTrace (prefixWord ++ tailWord_1330841) baseStart_1330841 baseEnd_1330841 := by
    simpa [prefixWord, tailWord_1330841, baseEnd_1330841] using wordTrace_append hprefix tailTrace_1330841
  have hstable : (prefixWord ++ tailWord_1330841).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330841).length < 2 ^ (prefixWord ++ tailWord_1330841).sum := by decide
  have hdescent : baseEnd_1330841 < baseStart_1330841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330844 : List Nat := [2, 2, 3, 2, 4, 8]
def baseStart_1330844 : Nat := 118140960795 + 1330844 * 2 ^ 59
def prefixEnd_1330844 : Nat := 4983230072969 + 3 ^ 40 * 1330844 * 2
def baseEnd_1330844 : Nat := 11248767870819692188141

theorem tailTrace_1330844 : CollatzResearch.WordTrace tailWord_1330844 prefixEnd_1330844 11248767870819692188141 := by
  unfold tailWord_1330844
  simp only [CollatzResearch.WordTrace]
  refine ⟨24269934195293476452411793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32359912260391301936549057 24269934195293476452411793)
  ·
    refine ⟨18202450646470107339308845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24269934195293476452411793 18202450646470107339308845)
    ·
      refine ⟨6825918992426290252240817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18202450646470107339308845 6825918992426290252240817)
      ·
        refine ⟨5119439244319717689180613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6825918992426290252240817 5119439244319717689180613)
        ·
          refine ⟨959894858309947066721365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5119439244319717689180613 959894858309947066721365)
          ·
            refine ⟨11248767870819692188141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 959894858309947066721365 11248767870819692188141)
            ·
              rfl

theorem cell21_1330844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 8].length) (baseStart_1330844 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1330844 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1330844 prefixEnd_1330844 := by exact prefixLift 1330844
  have htrace : WordTrace (prefixWord ++ tailWord_1330844) baseStart_1330844 baseEnd_1330844 := by
    simpa [prefixWord, tailWord_1330844, baseEnd_1330844] using wordTrace_append hprefix tailTrace_1330844
  have hstable : (prefixWord ++ tailWord_1330844).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330844).length < 2 ^ (prefixWord ++ tailWord_1330844).sum := by decide
  have hdescent : baseEnd_1330844 < baseStart_1330844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330847 : List Nat := [1, 1, 2, 7, 1, 1, 2, 2, 4]
def baseStart_1330847 : Nat := 118140960795 + 1330847 * 2 ^ 59
def prefixEnd_1330847 : Nat := 4983230072969 + 3 ^ 40 * 1330847 * 2
def baseEnd_1330847 : Nat := 303717417153004350529801

theorem tailTrace_1330847 : CollatzResearch.WordTrace tailWord_1330847 prefixEnd_1330847 303717417153004350529801 := by
  unfold tailWord_1330847
  simp only [CollatzResearch.WordTrace]
  refine ⟨48539977809576084417182795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32359985206384056278121863 48539977809576084417182795)
  ·
    refine ⟨72809966714364126625774193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48539977809576084417182795 72809966714364126625774193)
    ·
      refine ⟨54607475035773094969330645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72809966714364126625774193 54607475035773094969330645)
      ·
        refine ⟨1279862696150931913343687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 54607475035773094969330645 1279862696150931913343687)
        ·
          refine ⟨1919794044226397870015531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1279862696150931913343687 1919794044226397870015531)
          ·
            refine ⟨2879691066339596805023297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1919794044226397870015531 2879691066339596805023297)
            ·
              refine ⟨2159768299754697603767473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2879691066339596805023297 2159768299754697603767473)
              ·
                refine ⟨1619826224816023202825605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2159768299754697603767473 1619826224816023202825605)
                ·
                  refine ⟨303717417153004350529801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1619826224816023202825605 303717417153004350529801)
                  ·
                    rfl

theorem cell21_1330847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 2, 4].length) (baseStart_1330847 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1330847 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1330847 prefixEnd_1330847 := by exact prefixLift 1330847
  have htrace : WordTrace (prefixWord ++ tailWord_1330847) baseStart_1330847 baseEnd_1330847 := by
    simpa [prefixWord, tailWord_1330847, baseEnd_1330847] using wordTrace_append hprefix tailTrace_1330847
  have hstable : (prefixWord ++ tailWord_1330847).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330847).length < 2 ^ (prefixWord ++ tailWord_1330847).sum := by decide
  have hdescent : baseEnd_1330847 < baseStart_1330847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330906 : List Nat := [3, 1, 1, 2, 2, 5, 1, 2, 4]
def baseStart_1330906 : Nat := 118140960795 + 1330906 * 2 ^ 59
def prefixEnd_1330906 : Nat := 4983230072969 + 3 ^ 40 * 1330906 * 2
def baseEnd_1330906 : Nat := 303730881756833359046347

theorem tailTrace_1330906 : CollatzResearch.WordTrace tailWord_1330906 prefixEnd_1330906 303730881756833359046347 := by
  unfold tailWord_1330906
  simp only [CollatzResearch.WordTrace]
  refine ⟨12135532429090584373395143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32361419810908224995720381 12135532429090584373395143)
  ·
    refine ⟨18203298643635876560092715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12135532429090584373395143 18203298643635876560092715)
    ·
      refine ⟨27304947965453814840139073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18203298643635876560092715 27304947965453814840139073)
      ·
        refine ⟨20478710974090361130104305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27304947965453814840139073 20478710974090361130104305)
        ·
          refine ⟨15359033230567770847578229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20478710974090361130104305 15359033230567770847578229)
          ·
            refine ⟨1439909365365728516960459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15359033230567770847578229 1439909365365728516960459)
            ·
              refine ⟨2159864048048592775440689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1439909365365728516960459 2159864048048592775440689)
              ·
                refine ⟨1619898036036444581580517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2159864048048592775440689 1619898036036444581580517)
                ·
                  refine ⟨303730881756833359046347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1619898036036444581580517 303730881756833359046347)
                  ·
                    rfl

theorem cell21_1330906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 2, 4].length) (baseStart_1330906 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1330906 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1330906 prefixEnd_1330906 := by exact prefixLift 1330906
  have htrace : WordTrace (prefixWord ++ tailWord_1330906) baseStart_1330906 baseEnd_1330906 := by
    simpa [prefixWord, tailWord_1330906, baseEnd_1330906] using wordTrace_append hprefix tailTrace_1330906
  have hstable : (prefixWord ++ tailWord_1330906).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330906).length < 2 ^ (prefixWord ++ tailWord_1330906).sum := by decide
  have hdescent : baseEnd_1330906 < baseStart_1330906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330974 : List Nat := [4, 3, 2, 2, 2, 1, 2, 1, 4]
def baseStart_1330974 : Nat := 118140960795 + 1330974 * 2 ^ 59
def prefixEnd_1330974 : Nat := 4983230072969 + 3 ^ 40 * 1330974 * 2
def baseEnd_1330974 : Nat := 303746400283280351912875

theorem tailTrace_1330974 : CollatzResearch.WordTrace tailWord_1330974 prefixEnd_1330974 303746400283280351912875 := by
  unfold tailWord_1330974
  simp only [CollatzResearch.WordTrace]
  refine ⟨6068076235014498138381997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32363073253410656738037317 6068076235014498138381997)
  ·
    refine ⟨2275528588130436801893249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6068076235014498138381997 2275528588130436801893249)
    ·
      refine ⟨1706646441097827601419937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2275528588130436801893249 1706646441097827601419937)
      ·
        refine ⟨1279984830823370701064953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1706646441097827601419937 1279984830823370701064953)
        ·
          refine ⟨959988623117528025798715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1279984830823370701064953 959988623117528025798715)
          ·
            refine ⟨1439982934676292038698073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 959988623117528025798715 1439982934676292038698073)
            ·
              refine ⟨1079987201007219029023555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1439982934676292038698073 1079987201007219029023555)
              ·
                refine ⟨1619980801510828543535333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1079987201007219029023555 1619980801510828543535333)
                ·
                  refine ⟨303746400283280351912875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1619980801510828543535333 303746400283280351912875)
                  ·
                    rfl

theorem cell21_1330974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_1330974 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1330974 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1330974 prefixEnd_1330974 := by exact prefixLift 1330974
  have htrace : WordTrace (prefixWord ++ tailWord_1330974) baseStart_1330974 baseEnd_1330974 := by
    simpa [prefixWord, tailWord_1330974, baseEnd_1330974] using wordTrace_append hprefix tailTrace_1330974
  have hstable : (prefixWord ++ tailWord_1330974).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330974).length < 2 ^ (prefixWord ++ tailWord_1330974).sum := by decide
  have hdescent : baseEnd_1330974 < baseStart_1330974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1330996 : List Nat := [2, 5, 1, 1, 2, 1, 2, 7]
def baseStart_1330996 : Nat := 118140960795 + 1330996 * 2 ^ 59
def prefixEnd_1330996 : Nat := 4983230072969 + 3 ^ 40 * 1330996 * 2
def baseEnd_1330996 : Nat := 101250473661004400848721

theorem tailTrace_1330996 : CollatzResearch.WordTrace tailWord_1330996 prefixEnd_1330996 101250473661004400848721 := by
  unfold tailWord_1330996
  simp only [CollatzResearch.WordTrace]
  refine ⟨24272706143018141432178421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32363608190690855242904561 24272706143018141432178421)
  ·
    refine ⟨2275566200907950759266727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24272706143018141432178421 2275566200907950759266727)
    ·
      refine ⟨3413349301361926138900091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2275566200907950759266727 3413349301361926138900091)
      ·
        refine ⟨5120023952042889208350137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3413349301361926138900091 5120023952042889208350137)
        ·
          refine ⟨3840017964032166906262603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5120023952042889208350137 3840017964032166906262603)
          ·
            refine ⟨5760026946048250359393905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3840017964032166906262603 5760026946048250359393905)
            ·
              refine ⟨4320020209536187769545429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5760026946048250359393905 4320020209536187769545429)
              ·
                refine ⟨101250473661004400848721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4320020209536187769545429 101250473661004400848721)
                ·
                  rfl

theorem cell21_1330996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 7].length) (baseStart_1330996 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1330996 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1330996 prefixEnd_1330996 := by exact prefixLift 1330996
  have htrace : WordTrace (prefixWord ++ tailWord_1330996) baseStart_1330996 baseEnd_1330996 := by
    simpa [prefixWord, tailWord_1330996, baseEnd_1330996] using wordTrace_append hprefix tailTrace_1330996
  have hstable : (prefixWord ++ tailWord_1330996).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1330996).length < 2 ^ (prefixWord ++ tailWord_1330996).sum := by decide
  have hdescent : baseEnd_1330996 < baseStart_1330996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1330996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331069 : List Nat := [1, 4, 1, 1, 2, 1, 1, 1, 9]
def baseStart_1331069 : Nat := 118140960795 + 1331069 * 2 ^ 59
def prefixEnd_1331069 : Nat := 4983230072969 + 3 ^ 40 * 1331069 * 2
def baseEnd_1331069 : Nat := 303768080577581297829347

theorem tailTrace_1331069 : CollatzResearch.WordTrace tailWord_1331069 prefixEnd_1331069 303768080577581297829347 := by
  unfold tailWord_1331069
  simp only [CollatzResearch.WordTrace]
  refine ⟨48548074814771816331764261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32365383209847877554509507 48548074814771816331764261)
  ·
    refine ⟨9102764027769715562205799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48548074814771816331764261 9102764027769715562205799)
    ·
      refine ⟨13654146041654573343308699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9102764027769715562205799 13654146041654573343308699)
      ·
        refine ⟨20481219062481860014963049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13654146041654573343308699 20481219062481860014963049)
        ·
          refine ⟨15360914296861395011222287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20481219062481860014963049 15360914296861395011222287)
          ·
            refine ⟨23041371445292092516833431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15360914296861395011222287 23041371445292092516833431)
            ·
              refine ⟨34562057167938138775250147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23041371445292092516833431 34562057167938138775250147)
              ·
                refine ⟨51843085751907208162875221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34562057167938138775250147 51843085751907208162875221)
                ·
                  refine ⟨303768080577581297829347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 51843085751907208162875221 303768080577581297829347)
                  ·
                    rfl

theorem cell21_1331069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 9].length) (baseStart_1331069 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1331069 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1331069 prefixEnd_1331069 := by exact prefixLift 1331069
  have htrace : WordTrace (prefixWord ++ tailWord_1331069) baseStart_1331069 baseEnd_1331069 := by
    simpa [prefixWord, tailWord_1331069, baseEnd_1331069] using wordTrace_append hprefix tailTrace_1331069
  have hstable : (prefixWord ++ tailWord_1331069).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331069).length < 2 ^ (prefixWord ++ tailWord_1331069).sum := by decide
  have hdescent : baseEnd_1331069 < baseStart_1331069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331106 : List Nat := [3, 3, 1, 2, 4, 1, 2, 5]
def baseStart_1331106 : Nat := 118140960795 + 1331106 * 2 ^ 59
def prefixEnd_1331106 : Nat := 4983230072969 + 3 ^ 40 * 1331106 * 2
def baseEnd_1331106 : Nat := 101258841493892485237535

theorem tailTrace_1331106 : CollatzResearch.WordTrace tailWord_1331106 prefixEnd_1331106 101258841493892485237535 := by
  unfold tailWord_1331106
  simp only [CollatzResearch.WordTrace]
  refine ⟨12137356078909442912715293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32366282877091847767240781 12137356078909442912715293)
  ·
    refine ⟨4551508529591041092268235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12137356078909442912715293 4551508529591041092268235)
    ·
      refine ⟨6827262794386561638402353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4551508529591041092268235 6827262794386561638402353)
      ·
        refine ⟨5120447095789921228801765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6827262794386561638402353 5120447095789921228801765)
        ·
          refine ⟨960083830460610230400331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5120447095789921228801765 960083830460610230400331)
          ·
            refine ⟨1440125745690915345600497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 960083830460610230400331 1440125745690915345600497)
            ·
              refine ⟨1080094309268186509200373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1440125745690915345600497 1080094309268186509200373)
              ·
                refine ⟨101258841493892485237535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1080094309268186509200373 101258841493892485237535)
                ·
                  rfl

theorem cell21_1331106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 2, 5].length) (baseStart_1331106 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1331106 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1331106 prefixEnd_1331106 := by exact prefixLift 1331106
  have htrace : WordTrace (prefixWord ++ tailWord_1331106) baseStart_1331106 baseEnd_1331106 := by
    simpa [prefixWord, tailWord_1331106, baseEnd_1331106] using wordTrace_append hprefix tailTrace_1331106
  have hstable : (prefixWord ++ tailWord_1331106).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331106).length < 2 ^ (prefixWord ++ tailWord_1331106).sum := by decide
  have hdescent : baseEnd_1331106 < baseStart_1331106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331193 : List Nat := [1, 2, 1, 3, 1, 5, 2, 2, 4]
def baseStart_1331193 : Nat := 118140960795 + 1331193 * 2 ^ 59
def prefixEnd_1331193 : Nat := 4983230072969 + 3 ^ 40 * 1331193 * 2
def baseEnd_1331193 : Nat := 303796379066984637762427

theorem tailTrace_1331193 : CollatzResearch.WordTrace tailWord_1331193 prefixEnd_1331193 303796379066984637762427 := by
  unfold tailWord_1331193
  simp only [CollatzResearch.WordTrace]
  refine ⟨48552597466322585509278233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32368398310881723672852155 48552597466322585509278233)
  ·
    refine ⟨36414448099741939131958675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48552597466322585509278233 36414448099741939131958675)
    ·
      refine ⟨54621672149612908697938013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36414448099741939131958675 54621672149612908697938013)
      ·
        refine ⟨20483127056104840761726755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54621672149612908697938013 20483127056104840761726755)
        ·
          refine ⟨30724690584157261142590133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20483127056104840761726755 30724690584157261142590133)
          ·
            refine ⟨2880439742264743232117825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30724690584157261142590133 2880439742264743232117825)
            ·
              refine ⟨2160329806698557424088369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2880439742264743232117825 2160329806698557424088369)
              ·
                refine ⟨1620247355023918068066277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2160329806698557424088369 1620247355023918068066277)
                ·
                  refine ⟨303796379066984637762427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1620247355023918068066277 303796379066984637762427)
                  ·
                    rfl

theorem cell21_1331193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 2, 4].length) (baseStart_1331193 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1331193 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1331193 prefixEnd_1331193 := by exact prefixLift 1331193
  have htrace : WordTrace (prefixWord ++ tailWord_1331193) baseStart_1331193 baseEnd_1331193 := by
    simpa [prefixWord, tailWord_1331193, baseEnd_1331193] using wordTrace_append hprefix tailTrace_1331193
  have hstable : (prefixWord ++ tailWord_1331193).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331193).length < 2 ^ (prefixWord ++ tailWord_1331193).sum := by decide
  have hdescent : baseEnd_1331193 < baseStart_1331193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331207 : List Nat := [1, 1, 4, 3, 1, 2, 3, 6]
def baseStart_1331207 : Nat := 118140960795 + 1331207 * 2 ^ 59
def prefixEnd_1331207 : Nat := 4983230072969 + 3 ^ 40 * 1331207 * 2
def baseEnd_1331207 : Nat := 101266524685907908176355

theorem tailTrace_1331207 : CollatzResearch.WordTrace tailWord_1331207 prefixEnd_1331207 101266524685907908176355 := by
  unfold tailWord_1331207
  simp only [CollatzResearch.WordTrace]
  refine ⟨48553108088271865900287875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32368738725514577266858583 48553108088271865900287875)
  ·
    refine ⟨72829662132407798850431813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48553108088271865900287875 72829662132407798850431813)
    ·
      refine ⟨13655561649826462284455965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72829662132407798850431813 13655561649826462284455965)
      ·
        refine ⟨5120835618684923356670987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13655561649826462284455965 5120835618684923356670987)
        ·
          refine ⟨7681253428027385035006481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5120835618684923356670987 7681253428027385035006481)
          ·
            refine ⟨5760940071020538776254861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7681253428027385035006481 5760940071020538776254861)
            ·
              refine ⟨2160352526632702041095573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5760940071020538776254861 2160352526632702041095573)
              ·
                refine ⟨101266524685907908176355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2160352526632702041095573 101266524685907908176355)
                ·
                  rfl

theorem cell21_1331207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 6].length) (baseStart_1331207 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1331207 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1331207 prefixEnd_1331207 := by exact prefixLift 1331207
  have htrace : WordTrace (prefixWord ++ tailWord_1331207) baseStart_1331207 baseEnd_1331207 := by
    simpa [prefixWord, tailWord_1331207, baseEnd_1331207] using wordTrace_append hprefix tailTrace_1331207
  have hstable : (prefixWord ++ tailWord_1331207).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331207).length < 2 ^ (prefixWord ++ tailWord_1331207).sum := by decide
  have hdescent : baseEnd_1331207 < baseStart_1331207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331213 : List Nat := [1, 7, 1, 2, 1, 1, 1, 2, 5]
def baseStart_1331213 : Nat := 118140960795 + 1331213 * 2 ^ 59
def prefixEnd_1331213 : Nat := 4983230072969 + 3 ^ 40 * 1331213 * 2
def baseEnd_1331213 : Nat := 303800943339469047429053

theorem tailTrace_1331213 : CollatzResearch.WordTrace tailWord_1331213 prefixEnd_1331213 303800943339469047429053 := by
  unfold tailWord_1331213
  simp only [CollatzResearch.WordTrace]
  refine ⟨48553326926250128925006293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32368884617500085950004195 48553326926250128925006293)
  ·
    refine ⟨1137968599833987396679835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 48553326926250128925006293 1137968599833987396679835)
    ·
      refine ⟨1706952899750981095019753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1137968599833987396679835 1706952899750981095019753)
      ·
        refine ⟨1280214674813235821264815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1706952899750981095019753 1280214674813235821264815)
        ·
          refine ⟨1920322012219853731897223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1280214674813235821264815 1920322012219853731897223)
          ·
            refine ⟨2880483018329780597845835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1920322012219853731897223 2880483018329780597845835)
            ·
              refine ⟨4320724527494670896768753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2880483018329780597845835 4320724527494670896768753)
              ·
                refine ⟨3240543395621003172576565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4320724527494670896768753 3240543395621003172576565)
                ·
                  refine ⟨303800943339469047429053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3240543395621003172576565 303800943339469047429053)
                  ·
                    rfl

theorem cell21_1331213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_1331213 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1331213 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1331213 prefixEnd_1331213 := by exact prefixLift 1331213
  have htrace : WordTrace (prefixWord ++ tailWord_1331213) baseStart_1331213 baseEnd_1331213 := by
    simpa [prefixWord, tailWord_1331213, baseEnd_1331213] using wordTrace_append hprefix tailTrace_1331213
  have hstable : (prefixWord ++ tailWord_1331213).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331213).length < 2 ^ (prefixWord ++ tailWord_1331213).sum := by decide
  have hdescent : baseEnd_1331213 < baseStart_1331213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331286 : List Nat := [5, 2, 2, 1, 1, 1, 1, 2, 6]
def baseStart_1331286 : Nat := 118140960795 + 1331286 * 2 ^ 59
def prefixEnd_1331286 : Nat := 4983230072969 + 3 ^ 40 * 1331286 * 2
def baseEnd_1331286 : Nat := 303817602934037142712237

theorem tailTrace_1331286 : CollatzResearch.WordTrace tailWord_1331286 prefixEnd_1331286 303817602934037142712237 := by
  unfold tailWord_1331286
  simp only [CollatzResearch.WordTrace]
  refine ⟨3034749340936603899525857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32370659636657108261609141 3034749340936603899525857)
  ·
    refine ⟨2276062005702452924644393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3034749340936603899525857 2276062005702452924644393)
    ·
      refine ⟨1707046504276839693483295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2276062005702452924644393 1707046504276839693483295)
      ·
        refine ⟨2560569756415259540224943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1707046504276839693483295 2560569756415259540224943)
        ·
          refine ⟨3840854634622889310337415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2560569756415259540224943 3840854634622889310337415)
          ·
            refine ⟨5761281951934333965506123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3840854634622889310337415 5761281951934333965506123)
            ·
              refine ⟨8641922927901500948259185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5761281951934333965506123 8641922927901500948259185)
              ·
                refine ⟨6481442195926125711194389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8641922927901500948259185 6481442195926125711194389)
                ·
                  refine ⟨303817602934037142712237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6481442195926125711194389 303817602934037142712237)
                  ·
                    rfl

theorem cell21_1331286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_1331286 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1331286 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1331286 prefixEnd_1331286 := by exact prefixLift 1331286
  have htrace : WordTrace (prefixWord ++ tailWord_1331286) baseStart_1331286 baseEnd_1331286 := by
    simpa [prefixWord, tailWord_1331286, baseEnd_1331286] using wordTrace_append hprefix tailTrace_1331286
  have hstable : (prefixWord ++ tailWord_1331286).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331286).length < 2 ^ (prefixWord ++ tailWord_1331286).sum := by decide
  have hdescent : baseEnd_1331286 < baseStart_1331286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331314 : List Nat := [3, 2, 1, 2, 2, 2, 3, 1, 5]
def baseStart_1331314 : Nat := 118140960795 + 1331314 * 2 ^ 59
def prefixEnd_1331314 : Nat := 4983230072969 + 3 ^ 40 * 1331314 * 2
def baseEnd_1331314 : Nat := 303823992915515316245513

theorem tailTrace_1331314 : CollatzResearch.WordTrace tailWord_1331314 prefixEnd_1331314 303823992915515316245513 := by
  unfold tailWord_1331314
  simp only [CollatzResearch.WordTrace]
  refine ⟨12139252674721055793608249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32371340465922815449621997 12139252674721055793608249)
  ·
    refine ⟨9104439506040791845206187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12139252674721055793608249 9104439506040791845206187)
    ·
      refine ⟨13656659259061187767809281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9104439506040791845206187 13656659259061187767809281)
      ·
        refine ⟨10242494444295890825856961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13656659259061187767809281 10242494444295890825856961)
        ·
          refine ⟨7681870833221918119392721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10242494444295890825856961 7681870833221918119392721)
          ·
            refine ⟨5761403124916438589544541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7681870833221918119392721 5761403124916438589544541)
            ·
              refine ⟨2160526171843664471079203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5761403124916438589544541 2160526171843664471079203)
              ·
                refine ⟨3240789257765496706618805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2160526171843664471079203 3240789257765496706618805)
                ·
                  refine ⟨303823992915515316245513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3240789257765496706618805 303823992915515316245513)
                  ·
                    rfl

theorem cell21_1331314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 1, 5].length) (baseStart_1331314 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1331314 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1331314 prefixEnd_1331314 := by exact prefixLift 1331314
  have htrace : WordTrace (prefixWord ++ tailWord_1331314) baseStart_1331314 baseEnd_1331314 := by
    simpa [prefixWord, tailWord_1331314, baseEnd_1331314] using wordTrace_append hprefix tailTrace_1331314
  have hstable : (prefixWord ++ tailWord_1331314).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331314).length < 2 ^ (prefixWord ++ tailWord_1331314).sum := by decide
  have hdescent : baseEnd_1331314 < baseStart_1331314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331362 : List Nat := [3, 3, 1, 3, 1, 2, 2, 2, 4]
def baseStart_1331362 : Nat := 118140960795 + 1331362 * 2 ^ 59
def prefixEnd_1331362 : Nat := 4983230072969 + 3 ^ 40 * 1331362 * 2
def baseEnd_1331362 : Nat := 303834947169477899445415

theorem tailTrace_1331362 : CollatzResearch.WordTrace tailWord_1331362 prefixEnd_1331362 303834947169477899445415 := by
  unfold tailWord_1331362
  simp only [CollatzResearch.WordTrace]
  refine ⟨12139690350677581843045085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32372507601806884914786893 12139690350677581843045085)
  ·
    refine ⟨4552383881504093191141907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12139690350677581843045085 4552383881504093191141907)
    ·
      refine ⟨6828575822256139786712861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4552383881504093191141907 6828575822256139786712861)
      ·
        refine ⟨2560715933346052420017323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6828575822256139786712861 2560715933346052420017323)
        ·
          refine ⟨3841073900019078630025985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2560715933346052420017323 3841073900019078630025985)
          ·
            refine ⟨2880805425014308972519489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3841073900019078630025985 2880805425014308972519489)
            ·
              refine ⟨2160604068760731729389617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2880805425014308972519489 2160604068760731729389617)
              ·
                refine ⟨1620453051570548797042213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2160604068760731729389617 1620453051570548797042213)
                ·
                  refine ⟨303834947169477899445415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1620453051570548797042213 303834947169477899445415)
                  ·
                    rfl

theorem cell21_1331362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_1331362 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1331362 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1331362 prefixEnd_1331362 := by exact prefixLift 1331362
  have htrace : WordTrace (prefixWord ++ tailWord_1331362) baseStart_1331362 baseEnd_1331362 := by
    simpa [prefixWord, tailWord_1331362, baseEnd_1331362] using wordTrace_append hprefix tailTrace_1331362
  have hstable : (prefixWord ++ tailWord_1331362).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331362).length < 2 ^ (prefixWord ++ tailWord_1331362).sum := by decide
  have hdescent : baseEnd_1331362 < baseStart_1331362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331393 : List Nat := [1, 2, 6, 1, 2, 1, 3, 5]
def baseStart_1331393 : Nat := 118140960795 + 1331393 * 2 ^ 59
def prefixEnd_1331393 : Nat := 4983230072969 + 3 ^ 40 * 1331393 * 2
def baseEnd_1331393 : Nat := 101280673930609578142895

theorem tailTrace_1331393 : CollatzResearch.WordTrace tailWord_1331393 prefixEnd_1331393 101280673930609578142895 := by
  unfold tailWord_1331393
  simp only [CollatzResearch.WordTrace]
  refine ⟨48559892065598019666558833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32373261377065346444372555 48559892065598019666558833)
  ·
    refine ⟨36419919049198514749919125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48559892065598019666558833 36419919049198514749919125)
    ·
      refine ⟨1707183705431180378902459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 36419919049198514749919125 1707183705431180378902459)
      ·
        refine ⟨2560775558146770568353689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1707183705431180378902459 2560775558146770568353689)
        ·
          refine ⟨1920581668610077926265267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2560775558146770568353689 1920581668610077926265267)
          ·
            refine ⟨2880872502915116889397901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1920581668610077926265267 2880872502915116889397901)
            ·
              refine ⟨1080327188593168833524213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2880872502915116889397901 1080327188593168833524213)
              ·
                refine ⟨101280673930609578142895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1080327188593168833524213 101280673930609578142895)
                ·
                  rfl

theorem cell21_1331393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 3, 5].length) (baseStart_1331393 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1331393 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1331393 prefixEnd_1331393 := by exact prefixLift 1331393
  have htrace : WordTrace (prefixWord ++ tailWord_1331393) baseStart_1331393 baseEnd_1331393 := by
    simpa [prefixWord, tailWord_1331393, baseEnd_1331393] using wordTrace_append hprefix tailTrace_1331393
  have hstable : (prefixWord ++ tailWord_1331393).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331393).length < 2 ^ (prefixWord ++ tailWord_1331393).sum := by decide
  have hdescent : baseEnd_1331393 < baseStart_1331393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331421 : List Nat := [1, 4, 3, 2, 1, 2, 1, 1, 6]
def baseStart_1331421 : Nat := 118140960795 + 1331421 * 2 ^ 59
def prefixEnd_1331421 : Nat := 4983230072969 + 3 ^ 40 * 1331421 * 2
def baseEnd_1331421 : Nat := 303848411773306907961961

theorem tailTrace_1331421 : CollatzResearch.WordTrace tailWord_1331421 prefixEnd_1331421 303848411773306907961961 := by
  unfold tailWord_1331421
  simp only [CollatzResearch.WordTrace]
  refine ⟨48560913309496580448578117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32373942206331053632385411 48560913309496580448578117)
  ·
    refine ⟨9105171245530608834108397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48560913309496580448578117 9105171245530608834108397)
    ·
      refine ⟨3414439217073978312790649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9105171245530608834108397 3414439217073978312790649)
      ·
        refine ⟨2560829412805483734592987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3414439217073978312790649 2560829412805483734592987)
        ·
          refine ⟨3841244119208225601889481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2560829412805483734592987 3841244119208225601889481)
          ·
            refine ⟨2880933089406169201417111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3841244119208225601889481 2880933089406169201417111)
            ·
              refine ⟨4321399634109253802125667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2880933089406169201417111 4321399634109253802125667)
              ·
                refine ⟨6482099451163880703188501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4321399634109253802125667 6482099451163880703188501)
                ·
                  refine ⟨303848411773306907961961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6482099451163880703188501 303848411773306907961961)
                  ·
                    rfl

theorem cell21_1331421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 1, 6].length) (baseStart_1331421 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1331421 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1331421 prefixEnd_1331421 := by exact prefixLift 1331421
  have htrace : WordTrace (prefixWord ++ tailWord_1331421) baseStart_1331421 baseEnd_1331421 := by
    simpa [prefixWord, tailWord_1331421, baseEnd_1331421] using wordTrace_append hprefix tailTrace_1331421
  have hstable : (prefixWord ++ tailWord_1331421).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331421).length < 2 ^ (prefixWord ++ tailWord_1331421).sum := by decide
  have hdescent : baseEnd_1331421 < baseStart_1331421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331452 : List Nat := [2, 2, 2, 1, 4, 3, 2, 5]
def baseStart_1331452 : Nat := 118140960795 + 1331452 * 2 ^ 59
def prefixEnd_1331452 : Nat := 4983230072969 + 3 ^ 40 * 1331452 * 2
def baseEnd_1331452 : Nat := 101285162131885914315077

theorem tailTrace_1331452 : CollatzResearch.WordTrace tailWord_1331452 prefixEnd_1331452 101285162131885914315077 := by
  unfold tailWord_1331452
  simp only [CollatzResearch.WordTrace]
  refine ⟨24281021986192136371478305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32374695981589515161971073 24281021986192136371478305)
  ·
    refine ⟨18210766489644102278608729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24281021986192136371478305 18210766489644102278608729)
    ·
      refine ⟨13658074867233076708956547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18210766489644102278608729 13658074867233076708956547)
      ·
        refine ⟨20487112300849615063434821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13658074867233076708956547 20487112300849615063434821)
        ·
          refine ⟨3841333556409302824394029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20487112300849615063434821 3841333556409302824394029)
          ·
            refine ⟨1440500083653488559147761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3841333556409302824394029 1440500083653488559147761)
            ·
              refine ⟨1080375062740116419360821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1440500083653488559147761 1080375062740116419360821)
              ·
                refine ⟨101285162131885914315077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1080375062740116419360821 101285162131885914315077)
                ·
                  rfl

theorem cell21_1331452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 2, 5].length) (baseStart_1331452 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1331452 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1331452 prefixEnd_1331452 := by exact prefixLift 1331452
  have htrace : WordTrace (prefixWord ++ tailWord_1331452) baseStart_1331452 baseEnd_1331452 := by
    simpa [prefixWord, tailWord_1331452, baseEnd_1331452] using wordTrace_append hprefix tailTrace_1331452
  have hstable : (prefixWord ++ tailWord_1331452).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331452).length < 2 ^ (prefixWord ++ tailWord_1331452).sum := by decide
  have hdescent : baseEnd_1331452 < baseStart_1331452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331480 : List Nat := [2, 1, 2, 3, 1, 2, 2, 4, 4]
def baseStart_1331480 : Nat := 118140960795 + 1331480 * 2 ^ 59
def prefixEnd_1331480 : Nat := 4983230072969 + 3 ^ 40 * 1331480 * 2
def baseEnd_1331480 : Nat := 303861876377135916478507

theorem tailTrace_1331480 : CollatzResearch.WordTrace tailWord_1331480 prefixEnd_1331480 303861876377135916478507 := by
  unfold tailWord_1331480
  simp only [CollatzResearch.WordTrace]
  refine ⟨24281532608141416762487947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32375376810855222349983929 24281532608141416762487947)
  ·
    refine ⟨36422298912212125143731921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24281532608141416762487947 36422298912212125143731921)
    ·
      refine ⟨27316724184159093857798941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36422298912212125143731921 27316724184159093857798941)
      ·
        refine ⟨10243771569059660196674603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27316724184159093857798941 10243771569059660196674603)
        ·
          refine ⟨15365657353589490295011905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10243771569059660196674603 15365657353589490295011905)
          ·
            refine ⟨11524243015192117721258929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15365657353589490295011905 11524243015192117721258929)
            ·
              refine ⟨8643182261394088290944197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11524243015192117721258929 8643182261394088290944197)
              ·
                refine ⟨1620596674011391554552037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8643182261394088290944197 1620596674011391554552037)
                ·
                  refine ⟨303861876377135916478507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1620596674011391554552037 303861876377135916478507)
                  ·
                    rfl

theorem cell21_1331480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 4, 4].length) (baseStart_1331480 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1331480 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1331480 prefixEnd_1331480 := by exact prefixLift 1331480
  have htrace : WordTrace (prefixWord ++ tailWord_1331480) baseStart_1331480 baseEnd_1331480 := by
    simpa [prefixWord, tailWord_1331480, baseEnd_1331480] using wordTrace_append hprefix tailTrace_1331480
  have hstable : (prefixWord ++ tailWord_1331480).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331480).length < 2 ^ (prefixWord ++ tailWord_1331480).sum := by decide
  have hdescent : baseEnd_1331480 < baseStart_1331480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331556 : List Nat := [2, 3, 1, 1, 3, 1, 1, 5, 4]
def baseStart_1331556 : Nat := 118140960795 + 1331556 * 2 ^ 59
def prefixEnd_1331556 : Nat := 4983230072969 + 3 ^ 40 * 1331556 * 2
def baseEnd_1331556 : Nat := 303879220612576673211685

theorem tailTrace_1331556 : CollatzResearch.WordTrace tailWord_1331556 prefixEnd_1331556 303879220612576673211685 := by
  unfold tailWord_1331556
  simp only [CollatzResearch.WordTrace]
  refine ⟨24282918582003749252371261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32377224776004999003161681 24282918582003749252371261)
  ·
    refine ⟨9106094468251405969639223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24282918582003749252371261 9106094468251405969639223)
    ·
      refine ⟨13659141702377108954458835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9106094468251405969639223 13659141702377108954458835)
      ·
        refine ⟨20488712553565663431688253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13659141702377108954458835 20488712553565663431688253)
        ·
          refine ⟨7683267207587123786883095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20488712553565663431688253 7683267207587123786883095)
          ·
            refine ⟨11524900811380685680324643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7683267207587123786883095 11524900811380685680324643)
            ·
              refine ⟨17287351217071028520486965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11524900811380685680324643 17287351217071028520486965)
              ·
                refine ⟨1620689176600408923795653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17287351217071028520486965 1620689176600408923795653)
                ·
                  refine ⟨303879220612576673211685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1620689176600408923795653 303879220612576673211685)
                  ·
                    rfl

theorem cell21_1331556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 5, 4].length) (baseStart_1331556 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1331556 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1331556 prefixEnd_1331556 := by exact prefixLift 1331556
  have htrace : WordTrace (prefixWord ++ tailWord_1331556) baseStart_1331556 baseEnd_1331556 := by
    simpa [prefixWord, tailWord_1331556, baseEnd_1331556] using wordTrace_append hprefix tailTrace_1331556
  have hstable : (prefixWord ++ tailWord_1331556).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331556).length < 2 ^ (prefixWord ++ tailWord_1331556).sum := by decide
  have hdescent : baseEnd_1331556 < baseStart_1331556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331646 : List Nat := [4, 2, 1, 1, 1, 1, 11]
def baseStart_1331646 : Nat := 118140960795 + 1331646 * 2 ^ 59
def prefixEnd_1331646 : Nat := 4983230072969 + 3 ^ 40 * 1331646 * 2
def baseEnd_1331646 : Nat := 33766639982084057412389

theorem tailTrace_1331646 : CollatzResearch.WordTrace tailWord_1331646 prefixEnd_1331646 33766639982084057412389 := by
  unfold tailWord_1331646
  simp only [CollatzResearch.WordTrace]
  refine ⟨6071139966710180484439849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32379413155787629250345861 6071139966710180484439849)
  ·
    refine ⟨4553354975032635363329887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6071139966710180484439849 4553354975032635363329887)
    ·
      refine ⟨6830032462548953044994831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4553354975032635363329887 6830032462548953044994831)
      ·
        refine ⟨10245048693823429567492247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6830032462548953044994831 10245048693823429567492247)
        ·
          refine ⟨15367573040735144351238371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10245048693823429567492247 15367573040735144351238371)
          ·
            refine ⟨23051359561102716526857557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15367573040735144351238371 23051359561102716526857557)
            ·
              refine ⟨33766639982084057412389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 23051359561102716526857557 33766639982084057412389)
              ·
                rfl

theorem cell21_1331646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 11].length) (baseStart_1331646 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1331646 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1331646 prefixEnd_1331646 := by exact prefixLift 1331646
  have htrace : WordTrace (prefixWord ++ tailWord_1331646) baseStart_1331646 baseEnd_1331646 := by
    simpa [prefixWord, tailWord_1331646, baseEnd_1331646] using wordTrace_append hprefix tailTrace_1331646
  have hstable : (prefixWord ++ tailWord_1331646).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331646).length < 2 ^ (prefixWord ++ tailWord_1331646).sum := by decide
  have hdescent : baseEnd_1331646 < baseStart_1331646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331652 : List Nat := [2, 3, 3, 2, 3, 1, 1, 1, 5]
def baseStart_1331652 : Nat := 118140960795 + 1331652 * 2 ^ 59
def prefixEnd_1331652 : Nat := 4983230072969 + 3 ^ 40 * 1331652 * 2
def baseEnd_1331652 : Nat := 303901129120501839611489

theorem tailTrace_1331652 : CollatzResearch.WordTrace tailWord_1331652 prefixEnd_1331652 303901129120501839611489 := by
  unfold tailWord_1331652
  simp only [CollatzResearch.WordTrace]
  refine ⟨24284669285829853450118605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32379559047773137933491473 24284669285829853450118605)
  ·
    refine ⟨9106750982186195043794477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24284669285829853450118605 9106750982186195043794477)
    ·
      refine ⟨3415031618319823141422929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9106750982186195043794477 3415031618319823141422929)
      ·
        refine ⟨2561273713739867356067197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3415031618319823141422929 2561273713739867356067197)
        ·
          refine ⟨960477642652450258525199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2561273713739867356067197 960477642652450258525199)
          ·
            refine ⟨1440716463978675387787799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 960477642652450258525199 1440716463978675387787799)
            ·
              refine ⟨2161074695968013081681699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1440716463978675387787799 2161074695968013081681699)
              ·
                refine ⟨3241612043952019622522549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2161074695968013081681699 3241612043952019622522549)
                ·
                  refine ⟨303901129120501839611489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3241612043952019622522549 303901129120501839611489)
                  ·
                    rfl

theorem cell21_1331652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 1, 5].length) (baseStart_1331652 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1331652 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1331652 prefixEnd_1331652 := by exact prefixLift 1331652
  have htrace : WordTrace (prefixWord ++ tailWord_1331652) baseStart_1331652 baseEnd_1331652 := by
    simpa [prefixWord, tailWord_1331652, baseEnd_1331652] using wordTrace_append hprefix tailTrace_1331652
  have hstable : (prefixWord ++ tailWord_1331652).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331652).length < 2 ^ (prefixWord ++ tailWord_1331652).sum := by decide
  have hdescent : baseEnd_1331652 < baseStart_1331652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331666 : List Nat := [3, 2, 2, 4, 1, 1, 1, 3, 4]
def baseStart_1331666 : Nat := 118140960795 + 1331666 * 2 ^ 59
def prefixEnd_1331666 : Nat := 4983230072969 + 3 ^ 40 * 1331666 * 2
def baseEnd_1331666 : Nat := 303904324111240926378127

theorem tailTrace_1331666 : CollatzResearch.WordTrace tailWord_1331666 prefixEnd_1331666 303904324111240926378127 := by
  unfold tailWord_1331666
  simp only [CollatzResearch.WordTrace]
  refine ⟨12142462298402246822811713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32379899462405991527497901 12142462298402246822811713)
  ·
    refine ⟨9106846723801685117108785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12142462298402246822811713 9106846723801685117108785)
    ·
      refine ⟨6830135042851263837831589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9106846723801685117108785 6830135042851263837831589)
      ·
        refine ⟨1280650320534611969593423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6830135042851263837831589 1280650320534611969593423)
        ·
          refine ⟨1920975480801917954390135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1280650320534611969593423 1920975480801917954390135)
          ·
            refine ⟨2881463221202876931585203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1920975480801917954390135 2881463221202876931585203)
            ·
              refine ⟨4322194831804315397377805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2881463221202876931585203 4322194831804315397377805)
              ·
                refine ⟨1620823061926618274016677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4322194831804315397377805 1620823061926618274016677)
                ·
                  refine ⟨303904324111240926378127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1620823061926618274016677 303904324111240926378127)
                  ·
                    rfl

theorem cell21_1331666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 3, 4].length) (baseStart_1331666 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1331666 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1331666 prefixEnd_1331666 := by exact prefixLift 1331666
  have htrace : WordTrace (prefixWord ++ tailWord_1331666) baseStart_1331666 baseEnd_1331666 := by
    simpa [prefixWord, tailWord_1331666, baseEnd_1331666] using wordTrace_append hprefix tailTrace_1331666
  have hstable : (prefixWord ++ tailWord_1331666).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331666).length < 2 ^ (prefixWord ++ tailWord_1331666).sum := by decide
  have hdescent : baseEnd_1331666 < baseStart_1331666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331677 : List Nat := [1, 4, 3, 1, 1, 1, 2, 1, 7]
def baseStart_1331677 : Nat := 118140960795 + 1331677 * 2 ^ 59
def prefixEnd_1331677 : Nat := 4983230072969 + 3 ^ 40 * 1331677 * 2
def baseEnd_1331677 : Nat := 303906834461107351694771

theorem tailTrace_1331677 : CollatzResearch.WordTrace tailWord_1331677 prefixEnd_1331677 303906834461107351694771 := by
  unfold tailWord_1331677
  simp only [CollatzResearch.WordTrace]
  refine ⟨48570250396569136169897285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32380166931046090779931523 48570250396569136169897285)
  ·
    refine ⟨9106921949356713031855741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48570250396569136169897285 9106921949356713031855741)
    ·
      refine ⟨3415095731008767386945903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9106921949356713031855741 3415095731008767386945903)
      ·
        refine ⟨5122643596513151080418855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3415095731008767386945903 5122643596513151080418855)
        ·
          refine ⟨7683965394769726620628283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5122643596513151080418855 7683965394769726620628283)
          ·
            refine ⟨11525948092154589930942425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7683965394769726620628283 11525948092154589930942425)
            ·
              refine ⟨8644461069115942448206819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11525948092154589930942425 8644461069115942448206819)
              ·
                refine ⟨12966691603673913672310229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8644461069115942448206819 12966691603673913672310229)
                ·
                  refine ⟨303906834461107351694771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12966691603673913672310229 303906834461107351694771)
                  ·
                    rfl

theorem cell21_1331677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 7].length) (baseStart_1331677 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1331677 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1331677 prefixEnd_1331677 := by exact prefixLift 1331677
  have htrace : WordTrace (prefixWord ++ tailWord_1331677) baseStart_1331677 baseEnd_1331677 := by
    simpa [prefixWord, tailWord_1331677, baseEnd_1331677] using wordTrace_append hprefix tailTrace_1331677
  have hstable : (prefixWord ++ tailWord_1331677).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331677).length < 2 ^ (prefixWord ++ tailWord_1331677).sum := by decide
  have hdescent : baseEnd_1331677 < baseStart_1331677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331767 : List Nat := [1, 1, 3, 1, 2, 3, 3, 1, 6]
def baseStart_1331767 : Nat := 118140960795 + 1331767 * 2 ^ 59
def prefixEnd_1331767 : Nat := 4983230072969 + 3 ^ 40 * 1331767 * 2
def baseEnd_1331767 : Nat := 303927373687287195194587

theorem tailTrace_1331767 : CollatzResearch.WordTrace tailWord_1331767 prefixEnd_1331767 303927373687287195194587 := by
  unfold tailWord_1331767
  simp only [CollatzResearch.WordTrace]
  refine ⟨48573532966243081540673555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32382355310828721027115703 48573532966243081540673555)
  ·
    refine ⟨72860299449364622311010333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48573532966243081540673555 72860299449364622311010333)
    ·
      refine ⟨27322612293511733366628875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72860299449364622311010333 27322612293511733366628875)
      ·
        refine ⟨40983918440267600049943313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27322612293511733366628875 40983918440267600049943313)
        ·
          refine ⟨30737938830200700037457485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40983918440267600049943313 30737938830200700037457485)
          ·
            refine ⟨11526727061325262514046557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30737938830200700037457485 11526727061325262514046557)
            ·
              refine ⟨4322522647996973442767459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11526727061325262514046557 4322522647996973442767459)
              ·
                refine ⟨6483783971995460164151189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4322522647996973442767459 6483783971995460164151189)
                ·
                  refine ⟨303927373687287195194587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6483783971995460164151189 303927373687287195194587)
                  ·
                    rfl

theorem cell21_1331767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 1, 6].length) (baseStart_1331767 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1331767 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1331767 prefixEnd_1331767 := by exact prefixLift 1331767
  have htrace : WordTrace (prefixWord ++ tailWord_1331767) baseStart_1331767 baseEnd_1331767 := by
    simpa [prefixWord, tailWord_1331767, baseEnd_1331767] using wordTrace_append hprefix tailTrace_1331767
  have hstable : (prefixWord ++ tailWord_1331767).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331767).length < 2 ^ (prefixWord ++ tailWord_1331767).sum := by decide
  have hdescent : baseEnd_1331767 < baseStart_1331767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331770 : List Nat := [3, 1, 1, 1, 3, 3, 2, 4, 3]
def baseStart_1331770 : Nat := 118140960795 + 1331770 * 2 ^ 59
def prefixEnd_1331770 : Nat := 4983230072969 + 3 ^ 40 * 1331770 * 2
def baseEnd_1331770 : Nat := 303928058328159856644581

theorem tailTrace_1331770 : CollatzResearch.WordTrace tailWord_1331770 prefixEnd_1331770 303928058328159856644581 := by
  unfold tailWord_1331770
  simp only [CollatzResearch.WordTrace]
  refine ⟨12143410596308053263258191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32382428256821475368688509 12143410596308053263258191)
  ·
    refine ⟨18215115894462079894887287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12143410596308053263258191 18215115894462079894887287)
    ·
      refine ⟨27322673841693119842330931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18215115894462079894887287 27322673841693119842330931)
      ·
        refine ⟨40984010762539679763496397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27322673841693119842330931 40984010762539679763496397)
        ·
          refine ⟨15369004035952379911311149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40984010762539679763496397 15369004035952379911311149)
          ·
            refine ⟨5763376513482142466741681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15369004035952379911311149 5763376513482142466741681)
            ·
              refine ⟨4322532385111606850056261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5763376513482142466741681 4322532385111606850056261)
              ·
                refine ⟨810474822208426284385549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4322532385111606850056261 810474822208426284385549)
                ·
                  refine ⟨303928058328159856644581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 810474822208426284385549 303928058328159856644581)
                  ·
                    rfl

theorem cell21_1331770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 4, 3].length) (baseStart_1331770 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1331770 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1331770 prefixEnd_1331770 := by exact prefixLift 1331770
  have htrace : WordTrace (prefixWord ++ tailWord_1331770) baseStart_1331770 baseEnd_1331770 := by
    simpa [prefixWord, tailWord_1331770, baseEnd_1331770] using wordTrace_append hprefix tailTrace_1331770
  have hstable : (prefixWord ++ tailWord_1331770).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331770).length < 2 ^ (prefixWord ++ tailWord_1331770).sum := by decide
  have hdescent : baseEnd_1331770 < baseStart_1331770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331804 : List Nat := [2, 2, 4, 1, 3, 2, 1, 3, 3]
def baseStart_1331804 : Nat := 118140960795 + 1331804 * 2 ^ 59
def prefixEnd_1331804 : Nat := 4983230072969 + 3 ^ 40 * 1331804 * 2
def baseEnd_1331804 : Nat := 303935817591383353077845

theorem tailTrace_1331804 : CollatzResearch.WordTrace tailWord_1331804 prefixEnd_1331804 303935817591383353077845 := by
  unfold tailWord_1331804
  simp only [CollatzResearch.WordTrace]
  refine ⟨24287441233554518429885233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32383254978072691239846977 24287441233554518429885233)
  ·
    refine ⟨18215580925165888822413925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24287441233554518429885233 18215580925165888822413925)
    ·
      refine ⟨3415421423468604154202611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18215580925165888822413925 3415421423468604154202611)
      ·
        refine ⟨5123132135202906231303917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3415421423468604154202611 5123132135202906231303917)
        ·
          refine ⟨1921174550701089836738969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5123132135202906231303917 1921174550701089836738969)
          ·
            refine ⟨1440880913025817377554227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1921174550701089836738969 1440880913025817377554227)
            ·
              refine ⟨2161321369538726066331341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1440880913025817377554227 2161321369538726066331341)
              ·
                refine ⟨810495513577022274874253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2161321369538726066331341 810495513577022274874253)
                ·
                  refine ⟨303935817591383353077845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 810495513577022274874253 303935817591383353077845)
                  ·
                    rfl

theorem cell21_1331804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 3, 3].length) (baseStart_1331804 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1331804 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1331804 prefixEnd_1331804 := by exact prefixLift 1331804
  have htrace : WordTrace (prefixWord ++ tailWord_1331804) baseStart_1331804 baseEnd_1331804 := by
    simpa [prefixWord, tailWord_1331804, baseEnd_1331804] using wordTrace_append hprefix tailTrace_1331804
  have hstable : (prefixWord ++ tailWord_1331804).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331804).length < 2 ^ (prefixWord ++ tailWord_1331804).sum := by decide
  have hdescent : baseEnd_1331804 < baseStart_1331804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1331888 : List Nat := [2, 1, 1, 1, 2, 1, 3, 5, 5]
def baseStart_1331888 : Nat := 118140960795 + 1331888 * 2 ^ 59
def prefixEnd_1331888 : Nat := 4983230072969 + 3 ^ 40 * 1331888 * 2
def baseEnd_1331888 : Nat := 303954987535817873677673

theorem tailTrace_1331888 : CollatzResearch.WordTrace tailWord_1331888 prefixEnd_1331888 303954987535817873677673 := by
  unfold tailWord_1331888
  simp only [CollatzResearch.WordTrace]
  refine ⟨24288973099402359602914159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32385297465869812803885545 24288973099402359602914159)
  ·
    refine ⟨36433459649103539404371239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24288973099402359602914159 36433459649103539404371239)
    ·
      refine ⟨54650189473655309106556859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36433459649103539404371239 54650189473655309106556859)
      ·
        refine ⟨81975284210482963659835289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54650189473655309106556859 81975284210482963659835289)
        ·
          refine ⟨61481463157862222744876467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81975284210482963659835289 61481463157862222744876467)
          ·
            refine ⟨92222194736793334117314701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61481463157862222744876467 92222194736793334117314701)
            ·
              refine ⟨34583323026297500293993013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92222194736793334117314701 34583323026297500293993013)
              ·
                refine ⟨3242186533715390652561845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34583323026297500293993013 3242186533715390652561845)
                ·
                  refine ⟨303954987535817873677673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3242186533715390652561845 303954987535817873677673)
                  ·
                    rfl

theorem cell21_1331888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 5, 5].length) (baseStart_1331888 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1331888 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1331888 prefixEnd_1331888 := by exact prefixLift 1331888
  have htrace : WordTrace (prefixWord ++ tailWord_1331888) baseStart_1331888 baseEnd_1331888 := by
    simpa [prefixWord, tailWord_1331888, baseEnd_1331888] using wordTrace_append hprefix tailTrace_1331888
  have hstable : (prefixWord ++ tailWord_1331888).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1331888).length < 2 ^ (prefixWord ++ tailWord_1331888).sum := by decide
  have hdescent : baseEnd_1331888 < baseStart_1331888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1331888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332173 : List Nat := [1, 6, 3, 1, 2, 1, 2, 1, 4]
def baseStart_1332173 : Nat := 118140960795 + 1332173 * 2 ^ 59
def prefixEnd_1332173 : Nat := 4983230072969 + 3 ^ 40 * 1332173 * 2
def baseEnd_1332173 : Nat := 304020028418720711427091

theorem tailTrace_1332173 : CollatzResearch.WordTrace tailWord_1332173 prefixEnd_1332173 304020028418720711427091 := by
  unfold tailWord_1332173
  simp only [CollatzResearch.WordTrace]
  refine ⟨48588341002772212879953173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32392227335181475253302115 48588341002772212879953173)
  ·
    refine ⟨2277578484504947478747805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 48588341002772212879953173 2277578484504947478747805)
    ·
      refine ⟨854091931689355304530427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2277578484504947478747805 854091931689355304530427)
      ·
        refine ⟨1281137897534032956795641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 854091931689355304530427 1281137897534032956795641)
        ·
          refine ⟨960853423150524717596731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1281137897534032956795641 960853423150524717596731)
          ·
            refine ⟨1441280134725787076395097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 960853423150524717596731 1441280134725787076395097)
            ·
              refine ⟨1080960101044340307296323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1441280134725787076395097 1080960101044340307296323)
              ·
                refine ⟨1621440151566510460944485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1080960101044340307296323 1621440151566510460944485)
                ·
                  refine ⟨304020028418720711427091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1621440151566510460944485 304020028418720711427091)
                  ·
                    rfl

theorem cell21_1332173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_1332173 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1332173 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1332173 prefixEnd_1332173 := by exact prefixLift 1332173
  have htrace : WordTrace (prefixWord ++ tailWord_1332173) baseStart_1332173 baseEnd_1332173 := by
    simpa [prefixWord, tailWord_1332173, baseEnd_1332173] using wordTrace_append hprefix tailTrace_1332173
  have hstable : (prefixWord ++ tailWord_1332173).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332173).length < 2 ^ (prefixWord ++ tailWord_1332173).sum := by decide
  have hdescent : baseEnd_1332173 < baseStart_1332173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332178 : List Nat := [3, 2, 2, 3, 1, 1, 1, 8]
def baseStart_1332178 : Nat := 118140960795 + 1332178 * 2 ^ 59
def prefixEnd_1332178 : Nat := 4983230072969 + 3 ^ 40 * 1332178 * 2
def baseEnd_1332178 : Nat := 101340389828947271281249

theorem tailTrace_1332178 : CollatzResearch.WordTrace tailWord_1332178 prefixEnd_1332178 101340389828947271281249 := by
  unfold tailWord_1332178
  simp only [CollatzResearch.WordTrace]
  refine ⟨12147130841938524683471297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32392348911836065822590125 12147130841938524683471297)
  ·
    refine ⟨9110348131453893512603473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12147130841938524683471297 9110348131453893512603473)
    ·
      refine ⟨6832761098590420134452605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9110348131453893512603473 6832761098590420134452605)
      ·
        refine ⟨2562285411971407550419727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6832761098590420134452605 2562285411971407550419727)
        ·
          refine ⟨3843428117957111325629591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2562285411971407550419727 3843428117957111325629591)
          ·
            refine ⟨5765142176935666988444387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3843428117957111325629591 5765142176935666988444387)
            ·
              refine ⟨8647713265403500482666581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5765142176935666988444387 8647713265403500482666581)
              ·
                refine ⟨101340389828947271281249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8647713265403500482666581 101340389828947271281249)
                ·
                  rfl

theorem cell21_1332178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 8].length) (baseStart_1332178 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1332178 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1332178 prefixEnd_1332178 := by exact prefixLift 1332178
  have htrace : WordTrace (prefixWord ++ tailWord_1332178) baseStart_1332178 baseEnd_1332178 := by
    simpa [prefixWord, tailWord_1332178, baseEnd_1332178] using wordTrace_append hprefix tailTrace_1332178
  have hstable : (prefixWord ++ tailWord_1332178).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332178).length < 2 ^ (prefixWord ++ tailWord_1332178).sum := by decide
  have hdescent : baseEnd_1332178 < baseStart_1332178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332212 : List Nat := [2, 6, 2, 1, 10]
def baseStart_1332212 : Nat := 118140960795 + 1332212 * 2 ^ 59
def prefixEnd_1332212 : Nat := 4983230072969 + 3 ^ 40 * 1332212 * 2
def baseEnd_1332212 : Nat := 3753443564815621114531

theorem tailTrace_1332212 : CollatzResearch.WordTrace tailWord_1332212 prefixEnd_1332212 3753443564815621114531 := by
  unfold tailWord_1332212
  simp only [CollatzResearch.WordTrace]
  refine ⟨24294881724815461270311445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32393175633087281693748593 24294881724815461270311445)
  ·
    refine ⟨1138822580850724747045849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 24294881724815461270311445 1138822580850724747045849)
    ·
      refine ⟨854116935638043560284387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1138822580850724747045849 854116935638043560284387)
      ·
        refine ⟨1281175403457065340426581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 854116935638043560284387 1281175403457065340426581)
        ·
          refine ⟨3753443564815621114531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1281175403457065340426581 3753443564815621114531)
          ·
            rfl

theorem cell21_1332212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 10].length) (baseStart_1332212 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1332212 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1332212 prefixEnd_1332212 := by exact prefixLift 1332212
  have htrace : WordTrace (prefixWord ++ tailWord_1332212) baseStart_1332212 baseEnd_1332212 := by
    simpa [prefixWord, tailWord_1332212, baseEnd_1332212] using wordTrace_append hprefix tailTrace_1332212
  have hstable : (prefixWord ++ tailWord_1332212).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332212).length < 2 ^ (prefixWord ++ tailWord_1332212).sum := by decide
  have hdescent : baseEnd_1332212 < baseStart_1332212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332285 : List Nat := [1, 4, 1, 3, 1, 3, 2, 1, 5]
def baseStart_1332285 : Nat := 118140960795 + 1332285 * 2 ^ 59
def prefixEnd_1332285 : Nat := 4983230072969 + 3 ^ 40 * 1332285 * 2
def baseEnd_1332285 : Nat := 304045588344633405560195

theorem tailTrace_1332285 : CollatzResearch.WordTrace tailWord_1332285 prefixEnd_1332285 304045588344633405560195 := by
  unfold tailWord_1332285
  simp only [CollatzResearch.WordTrace]
  refine ⟨48592425978366456008030309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32394950652244304005353539 48592425978366456008030309)
  ·
    refine ⟨9111079870943710501505683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48592425978366456008030309 9111079870943710501505683)
    ·
      refine ⟨13666619806415565752258525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9111079870943710501505683 13666619806415565752258525)
      ·
        refine ⟨5124982427405837157096947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13666619806415565752258525 5124982427405837157096947)
        ·
          refine ⟨7687473641108755735645421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5124982427405837157096947 7687473641108755735645421)
          ·
            refine ⟨2882802615415783400867033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7687473641108755735645421 2882802615415783400867033)
            ·
              refine ⟨2162101961561837550650275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2882802615415783400867033 2162101961561837550650275)
              ·
                refine ⟨3243152942342756325975413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2162101961561837550650275 3243152942342756325975413)
                ·
                  refine ⟨304045588344633405560195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3243152942342756325975413 304045588344633405560195)
                  ·
                    rfl

theorem cell21_1332285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 1, 5].length) (baseStart_1332285 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1332285 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1332285 prefixEnd_1332285 := by exact prefixLift 1332285
  have htrace : WordTrace (prefixWord ++ tailWord_1332285) baseStart_1332285 baseEnd_1332285 := by
    simpa [prefixWord, tailWord_1332285, baseEnd_1332285] using wordTrace_append hprefix tailTrace_1332285
  have hstable : (prefixWord ++ tailWord_1332285).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332285).length < 2 ^ (prefixWord ++ tailWord_1332285).sum := by decide
  have hdescent : baseEnd_1332285 < baseStart_1332285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332330 : List Nat := [3, 1, 3, 2, 2, 3, 7]
def baseStart_1332330 : Nat := 118140960795 + 1332330 * 2 ^ 59
def prefixEnd_1332330 : Nat := 4983230072969 + 3 ^ 40 * 1332330 * 2
def baseEnd_1332330 : Nat := 33783984217524814145567

theorem tailTrace_1332330 : CollatzResearch.WordTrace tailWord_1332330 prefixEnd_1332330 33783984217524814145567 := by
  unfold tailWord_1332330
  simp only [CollatzResearch.WordTrace]
  refine ⟨12148516815800857173354611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32396044842135619128945629 12148516815800857173354611)
  ·
    refine ⟨18222775223701285760031917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12148516815800857173354611 18222775223701285760031917)
    ·
      refine ⟨6833540708887982160011969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18222775223701285760031917 6833540708887982160011969)
      ·
        refine ⟨5125155531665986620008977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6833540708887982160011969 5125155531665986620008977)
        ·
          refine ⟨3843866648749489965006733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5125155531665986620008977 3843866648749489965006733)
          ·
            refine ⟨1441449993281058736877525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3843866648749489965006733 1441449993281058736877525)
            ·
              refine ⟨33783984217524814145567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1441449993281058736877525 33783984217524814145567)
              ·
                rfl

theorem cell21_1332330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 7].length) (baseStart_1332330 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1332330 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1332330 prefixEnd_1332330 := by exact prefixLift 1332330
  have htrace : WordTrace (prefixWord ++ tailWord_1332330) baseStart_1332330 baseEnd_1332330 := by
    simpa [prefixWord, tailWord_1332330, baseEnd_1332330] using wordTrace_append hprefix tailTrace_1332330
  have hstable : (prefixWord ++ tailWord_1332330).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332330).length < 2 ^ (prefixWord ++ tailWord_1332330).sum := by decide
  have hdescent : baseEnd_1332330 < baseStart_1332330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332344 : List Nat := [2, 1, 2, 1, 1, 1, 7, 1, 5]
def baseStart_1332344 : Nat := 118140960795 + 1332344 * 2 ^ 59
def prefixEnd_1332344 : Nat := 4983230072969 + 3 ^ 40 * 1332344 * 2
def baseEnd_1332344 : Nat := 304059052948462414076741

theorem tailTrace_1332344 : CollatzResearch.WordTrace tailWord_1332344 prefixEnd_1332344 304059052948462414076741 := by
  unfold tailWord_1332344
  simp only [CollatzResearch.WordTrace]
  refine ⟨24297288942576354542214043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32396385256768472722952057 24297288942576354542214043)
  ·
    refine ⟨36445933413864531813321065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24297288942576354542214043 36445933413864531813321065)
    ·
      refine ⟨27334450060398398859990799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36445933413864531813321065 27334450060398398859990799)
      ·
        refine ⟨41001675090597598289986199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27334450060398398859990799 41001675090597598289986199)
        ·
          refine ⟨61502512635896397434979299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41001675090597598289986199 61502512635896397434979299)
          ·
            refine ⟨92253768953844596152468949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61502512635896397434979299 92253768953844596152468949)
            ·
              refine ⟨2162197709855732722323491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 92253768953844596152468949 2162197709855732722323491)
              ·
                refine ⟨3243296564783599083485237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2162197709855732722323491 3243296564783599083485237)
                ·
                  refine ⟨304059052948462414076741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3243296564783599083485237 304059052948462414076741)
                  ·
                    rfl

theorem cell21_1332344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 1, 5].length) (baseStart_1332344 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1332344 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1332344 prefixEnd_1332344 := by exact prefixLift 1332344
  have htrace : WordTrace (prefixWord ++ tailWord_1332344) baseStart_1332344 baseEnd_1332344 := by
    simpa [prefixWord, tailWord_1332344, baseEnd_1332344] using wordTrace_append hprefix tailTrace_1332344
  have hstable : (prefixWord ++ tailWord_1332344).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332344).length < 2 ^ (prefixWord ++ tailWord_1332344).sum := by decide
  have hdescent : baseEnd_1332344 < baseStart_1332344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332617 : List Nat := [1, 2, 1, 1, 7, 1, 8]
def baseStart_1332617 : Nat := 118140960795 + 1332617 * 2 ^ 59
def prefixEnd_1332617 : Nat := 4983230072969 + 3 ^ 40 * 1332617 * 2
def baseEnd_1332617 : Nat := 33791261696430511780687

theorem tailTrace_1332617 : CollatzResearch.WordTrace tailWord_1332617 prefixEnd_1332617 33791261696430511780687 := by
  unfold tailWord_1332617
  simp only [CollatzResearch.WordTrace]
  refine ⟨48604535013163676709116105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32403023342109117806077403 48604535013163676709116105)
  ·
    refine ⟨36453401259872757531837079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48604535013163676709116105 36453401259872757531837079)
    ·
      refine ⟨54680101889809136297755619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36453401259872757531837079 54680101889809136297755619)
      ·
        refine ⟨82020152834713704446633429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54680101889809136297755619 82020152834713704446633429)
        ·
          refine ⟨1922347332063602447967971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 82020152834713704446633429 1922347332063602447967971)
          ·
            refine ⟨2883520998095403671951957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1922347332063602447967971 2883520998095403671951957)
            ·
              refine ⟨33791261696430511780687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2883520998095403671951957 33791261696430511780687)
              ·
                rfl

theorem cell21_1332617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 8].length) (baseStart_1332617 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1332617 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1332617 prefixEnd_1332617 := by exact prefixLift 1332617
  have htrace : WordTrace (prefixWord ++ tailWord_1332617) baseStart_1332617 baseEnd_1332617 := by
    simpa [prefixWord, tailWord_1332617, baseEnd_1332617] using wordTrace_append hprefix tailTrace_1332617
  have hstable : (prefixWord ++ tailWord_1332617).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332617).length < 2 ^ (prefixWord ++ tailWord_1332617).sum := by decide
  have hdescent : baseEnd_1332617 < baseStart_1332617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332674 : List Nat := [3, 5, 2, 1, 1, 1, 3, 2, 3]
def baseStart_1332674 : Nat := 118140960795 + 1332674 * 2 ^ 59
def prefixEnd_1332674 : Nat := 4983230072969 + 3 ^ 40 * 1332674 * 2
def baseEnd_1332674 : Nat := 304134363444455173576067

theorem tailTrace_1332674 : CollatzResearch.WordTrace tailWord_1332674 prefixEnd_1332674 304134363444455173576067 := by
  unfold tailWord_1332674
  simp only [CollatzResearch.WordTrace]
  refine ⟨12151653493489293860985269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32404409315971450295960717 12151653493489293860985269)
  ·
    refine ⟨1139217515014621299467369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12151653493489293860985269 1139217515014621299467369)
    ·
      refine ⟨854413136260965974600527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1139217515014621299467369 854413136260965974600527)
      ·
        refine ⟨1281619704391448961900791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 854413136260965974600527 1281619704391448961900791)
        ·
          refine ⟨1922429556587173442851187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1281619704391448961900791 1922429556587173442851187)
          ·
            refine ⟨2883644334880760164276781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1922429556587173442851187 2883644334880760164276781)
            ·
              refine ⟨1081366625580285061603793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2883644334880760164276781 1081366625580285061603793)
              ·
                refine ⟨811024969185213796202845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1081366625580285061603793 811024969185213796202845)
                ·
                  refine ⟨304134363444455173576067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 811024969185213796202845 304134363444455173576067)
                  ·
                    rfl

theorem cell21_1332674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_1332674 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1332674 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1332674 prefixEnd_1332674 := by exact prefixLift 1332674
  have htrace : WordTrace (prefixWord ++ tailWord_1332674) baseStart_1332674 baseEnd_1332674 := by
    simpa [prefixWord, tailWord_1332674, baseEnd_1332674] using wordTrace_append hprefix tailTrace_1332674
  have hstable : (prefixWord ++ tailWord_1332674).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332674).length < 2 ^ (prefixWord ++ tailWord_1332674).sum := by decide
  have hdescent : baseEnd_1332674 < baseStart_1332674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332682 : List Nat := [3, 1, 2, 1, 2, 4, 3, 2, 3]
def baseStart_1332682 : Nat := 118140960795 + 1332682 * 2 ^ 59
def prefixEnd_1332682 : Nat := 4983230072969 + 3 ^ 40 * 1332682 * 2
def baseEnd_1332682 : Nat := 304136189153448937442717

theorem tailTrace_1332682 : CollatzResearch.WordTrace tailWord_1332682 prefixEnd_1332682 304136189153448937442717 := by
  unfold tailWord_1332682
  simp only [CollatzResearch.WordTrace]
  refine ⟨12151726439482048202558075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32404603838618795206821533 12151726439482048202558075)
  ·
    refine ⟨18227589659223072303837113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12151726439482048202558075 18227589659223072303837113)
    ·
      refine ⟨13670692244417304227877835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18227589659223072303837113 13670692244417304227877835)
      ·
        refine ⟨20506038366625956341816753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13670692244417304227877835 20506038366625956341816753)
        ·
          refine ⟨15379528774969467256362565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20506038366625956341816753 15379528774969467256362565)
          ·
            refine ⟨2883661645306775110567981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15379528774969467256362565 2883661645306775110567981)
            ·
              refine ⟨1081373116990040666462993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2883661645306775110567981 1081373116990040666462993)
              ·
                refine ⟨811029837742530499847245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1081373116990040666462993 811029837742530499847245)
                ·
                  refine ⟨304136189153448937442717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 811029837742530499847245 304136189153448937442717)
                  ·
                    rfl

theorem cell21_1332682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 3, 2, 3].length) (baseStart_1332682 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1332682 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1332682 prefixEnd_1332682 := by exact prefixLift 1332682
  have htrace : WordTrace (prefixWord ++ tailWord_1332682) baseStart_1332682 baseEnd_1332682 := by
    simpa [prefixWord, tailWord_1332682, baseEnd_1332682] using wordTrace_append hprefix tailTrace_1332682
  have hstable : (prefixWord ++ tailWord_1332682).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332682).length < 2 ^ (prefixWord ++ tailWord_1332682).sum := by decide
  have hdescent : baseEnd_1332682 < baseStart_1332682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332693 : List Nat := [1, 3, 2, 3, 1, 1, 4, 6]
def baseStart_1332693 : Nat := 118140960795 + 1332693 * 2 ^ 59
def prefixEnd_1332693 : Nat := 4983230072969 + 3 ^ 40 * 1332693 * 2
def baseEnd_1332693 : Nat := 101379566501105120919787

theorem tailTrace_1332693 : CollatzResearch.WordTrace tailWord_1332693 prefixEnd_1332693 101379566501105120919787 := by
  unfold tailWord_1332693
  simp only [CollatzResearch.WordTrace]
  refine ⟨48607306960888341688882733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32404871307258894459255155 48607306960888341688882733)
  ·
    refine ⟨18227740110333128133331025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48607306960888341688882733 18227740110333128133331025)
    ·
      refine ⟨13670805082749846099998269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18227740110333128133331025 13670805082749846099998269)
      ·
        refine ⟨5126551906031192287499351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13670805082749846099998269 5126551906031192287499351)
        ·
          refine ⟨7689827859046788431249027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5126551906031192287499351 7689827859046788431249027)
          ·
            refine ⟨11534741788570182646873541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7689827859046788431249027 11534741788570182646873541)
            ·
              refine ⟨2162764085356909246288789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11534741788570182646873541 2162764085356909246288789)
              ·
                refine ⟨101379566501105120919787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2162764085356909246288789 101379566501105120919787)
                ·
                  rfl

theorem cell21_1332693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 6].length) (baseStart_1332693 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1332693 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1332693 prefixEnd_1332693 := by exact prefixLift 1332693
  have htrace : WordTrace (prefixWord ++ tailWord_1332693) baseStart_1332693 baseEnd_1332693 := by
    simpa [prefixWord, tailWord_1332693, baseEnd_1332693] using wordTrace_append hprefix tailTrace_1332693
  have hstable : (prefixWord ++ tailWord_1332693).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332693).length < 2 ^ (prefixWord ++ tailWord_1332693).sum := by decide
  have hdescent : baseEnd_1332693 < baseStart_1332693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332806 : List Nat := [6, 1, 1, 1, 3, 1, 3, 1, 4]
def baseStart_1332806 : Nat := 118140960795 + 1332806 * 2 ^ 59
def prefixEnd_1332806 : Nat := 4983230072969 + 3 ^ 40 * 1332806 * 2
def baseEnd_1332806 : Nat := 304164487642852277375797

theorem tailTrace_1332806 : CollatzResearch.WordTrace tailWord_1332806 prefixEnd_1332806 304164487642852277375797 := by
  unfold tailWord_1332806
  simp only [CollatzResearch.WordTrace]
  refine ⟨1519107137796217562117071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 32407618939652641325164181 1519107137796217562117071)
  ·
    refine ⟨2278660706694326343175607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1519107137796217562117071 2278660706694326343175607)
    ·
      refine ⟨3417991060041489514763411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2278660706694326343175607 3417991060041489514763411)
      ·
        refine ⟨5126986590062234272145117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3417991060041489514763411 5126986590062234272145117)
        ·
          refine ⟨1922619971273337852054419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5126986590062234272145117 1922619971273337852054419)
          ·
            refine ⟨2883929956910006778081629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1922619971273337852054419 2883929956910006778081629)
            ·
              refine ⟨1081473733841252541780611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2883929956910006778081629 1081473733841252541780611)
              ·
                refine ⟨1622210600761878812670917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1081473733841252541780611 1622210600761878812670917)
                ·
                  refine ⟨304164487642852277375797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1622210600761878812670917 304164487642852277375797)
                  ·
                    rfl

theorem cell21_1332806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_1332806 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1332806 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1332806 prefixEnd_1332806 := by exact prefixLift 1332806
  have htrace : WordTrace (prefixWord ++ tailWord_1332806) baseStart_1332806 baseEnd_1332806 := by
    simpa [prefixWord, tailWord_1332806, baseEnd_1332806] using wordTrace_append hprefix tailTrace_1332806
  have hstable : (prefixWord ++ tailWord_1332806).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332806).length < 2 ^ (prefixWord ++ tailWord_1332806).sum := by decide
  have hdescent : baseEnd_1332806 < baseStart_1332806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332935 : List Nat := [1, 1, 4, 1, 1, 1, 5, 2, 5]
def baseStart_1332935 : Nat := 118140960795 + 1332935 * 2 ^ 59
def prefixEnd_1332935 : Nat := 4983230072969 + 3 ^ 40 * 1332935 * 2
def baseEnd_1332935 : Nat := 304193927200376719725533

theorem tailTrace_1332935 : CollatzResearch.WordTrace tailWord_1332935 prefixEnd_1332935 304193927200376719725533 := by
  unfold tailWord_1332935
  simp only [CollatzResearch.WordTrace]
  refine ⟨48616133426011617019192259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32410755617341078012794839 48616133426011617019192259)
  ·
    refine ⟨72924200139017425528788389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48616133426011617019192259 72924200139017425528788389)
    ·
      refine ⟨13673287526065767286647823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72924200139017425528788389 13673287526065767286647823)
      ·
        refine ⟨20509931289098650929971735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13673287526065767286647823 20509931289098650929971735)
        ·
          refine ⟨30764896933647976394957603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20509931289098650929971735 30764896933647976394957603)
          ·
            refine ⟨46147345400471964592436405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30764896933647976394957603 46147345400471964592436405)
            ·
              refine ⟨4326313631294246680540913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46147345400471964592436405 4326313631294246680540913)
              ·
                refine ⟨3244735223470685010405685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4326313631294246680540913 3244735223470685010405685)
                ·
                  refine ⟨304193927200376719725533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3244735223470685010405685 304193927200376719725533)
                  ·
                    rfl

theorem cell21_1332935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 2, 5].length) (baseStart_1332935 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1332935 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1332935 prefixEnd_1332935 := by exact prefixLift 1332935
  have htrace : WordTrace (prefixWord ++ tailWord_1332935) baseStart_1332935 baseEnd_1332935 := by
    simpa [prefixWord, tailWord_1332935, baseEnd_1332935] using wordTrace_append hprefix tailTrace_1332935
  have hstable : (prefixWord ++ tailWord_1332935).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332935).length < 2 ^ (prefixWord ++ tailWord_1332935).sum := by decide
  have hdescent : baseEnd_1332935 < baseStart_1332935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1332938 : List Nat := [3, 1, 2, 1, 5, 1, 3, 5]
def baseStart_1332938 : Nat := 118140960795 + 1332938 * 2 ^ 59
def prefixEnd_1332938 : Nat := 4983230072969 + 3 ^ 40 * 1332938 * 2
def baseEnd_1332938 : Nat := 101398203947083127058509

theorem tailTrace_1332938 : CollatzResearch.WordTrace tailWord_1332938 prefixEnd_1332938 101398203947083127058509 := by
  unfold tailWord_1332938
  simp only [CollatzResearch.WordTrace]
  refine ⟨12154060711250187132887867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32410828563333832354367645 12154060711250187132887867)
  ·
    refine ⟨18231091066875280699331801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12154060711250187132887867 18231091066875280699331801)
    ·
      refine ⟨13673318300156460524498851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18231091066875280699331801 13673318300156460524498851)
      ·
        refine ⟨20509977450234690786748277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13673318300156460524498851 20509977450234690786748277)
        ·
          refine ⟨1922810385959502261257651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20509977450234690786748277 1922810385959502261257651)
          ·
            refine ⟨2884215578939253391886477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1922810385959502261257651 2884215578939253391886477)
            ·
              refine ⟨1081580842102220021957429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2884215578939253391886477 1081580842102220021957429)
              ·
                refine ⟨101398203947083127058509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1081580842102220021957429 101398203947083127058509)
                ·
                  rfl

theorem cell21_1332938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 3, 5].length) (baseStart_1332938 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1332938 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1332938 prefixEnd_1332938 := by exact prefixLift 1332938
  have htrace : WordTrace (prefixWord ++ tailWord_1332938) baseStart_1332938 baseEnd_1332938 := by
    simpa [prefixWord, tailWord_1332938, baseEnd_1332938] using wordTrace_append hprefix tailTrace_1332938
  have hstable : (prefixWord ++ tailWord_1332938).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1332938).length < 2 ^ (prefixWord ++ tailWord_1332938).sum := by decide
  have hdescent : baseEnd_1332938 < baseStart_1332938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1332938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333028 : List Nat := [2, 3, 1, 3, 2, 1, 3, 1, 5]
def baseStart_1333028 : Nat := 118140960795 + 1333028 * 2 ^ 59
def prefixEnd_1333028 : Nat := 4983230072969 + 3 ^ 40 * 1333028 * 2
def baseEnd_1333028 : Nat := 304215151067429224675343

theorem tailTrace_1333028 : CollatzResearch.WordTrace tailWord_1333028 prefixEnd_1333028 304215151067429224675343 := by
  unfold tailWord_1333028
  simp only [CollatzResearch.WordTrace]
  refine ⟨24309762707337346951163869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32413016943116462601551825 24309762707337346951163869)
  ·
    refine ⟨9116161015251505106686451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24309762707337346951163869 9116161015251505106686451)
    ·
      refine ⟨13674241522877257660029677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9116161015251505106686451 13674241522877257660029677)
      ·
        refine ⟨5127840571078971622511129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13674241522877257660029677 5127840571078971622511129)
        ·
          refine ⟨3845880428309228716883347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5127840571078971622511129 3845880428309228716883347)
          ·
            refine ⟨5768820642463843075325021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3845880428309228716883347 5768820642463843075325021)
            ·
              refine ⟨2163307740923941153246883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5768820642463843075325021 2163307740923941153246883)
              ·
                refine ⟨3244961611385911729870325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2163307740923941153246883 3244961611385911729870325)
                ·
                  refine ⟨304215151067429224675343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3244961611385911729870325 304215151067429224675343)
                  ·
                    rfl

theorem cell21_1333028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 1, 5].length) (baseStart_1333028 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1333028 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1333028 prefixEnd_1333028 := by exact prefixLift 1333028
  have htrace : WordTrace (prefixWord ++ tailWord_1333028) baseStart_1333028 baseEnd_1333028 := by
    simpa [prefixWord, tailWord_1333028, baseEnd_1333028] using wordTrace_append hprefix tailTrace_1333028
  have hstable : (prefixWord ++ tailWord_1333028).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333028).length < 2 ^ (prefixWord ++ tailWord_1333028).sum := by decide
  have hdescent : baseEnd_1333028 < baseStart_1333028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333079 : List Nat := [1, 1, 3, 2, 6, 1, 2, 2, 3]
def baseStart_1333079 : Nat := 118140960795 + 1333079 * 2 ^ 59
def prefixEnd_1333079 : Nat := 4983230072969 + 3 ^ 40 * 1333079 * 2
def baseEnd_1333079 : Nat := 304226789962264469325239

theorem tailTrace_1333079 : CollatzResearch.WordTrace tailWord_1333079 prefixEnd_1333079 304226789962264469325239 := by
  unfold tailWord_1333079
  simp only [CollatzResearch.WordTrace]
  refine ⟨48621385537489929612434291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32414257024993286408289527 48621385537489929612434291)
  ·
    refine ⟨72932078306234894418651437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48621385537489929612434291 72932078306234894418651437)
    ·
      refine ⟨27349529364838085406994289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72932078306234894418651437 27349529364838085406994289)
      ·
        refine ⟨20512147023628564055245717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27349529364838085406994289 20512147023628564055245717)
        ·
          refine ⟨961506891732588940089643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 20512147023628564055245717 961506891732588940089643)
          ·
            refine ⟨1442260337598883410134465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 961506891732588940089643 1442260337598883410134465)
            ·
              refine ⟨1081695253199162557600849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1442260337598883410134465 1081695253199162557600849)
              ·
                refine ⟨811271439899371918200637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1081695253199162557600849 811271439899371918200637)
                ·
                  refine ⟨304226789962264469325239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 811271439899371918200637 304226789962264469325239)
                  ·
                    rfl

theorem cell21_1333079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 2, 2, 3].length) (baseStart_1333079 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1333079 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1333079 prefixEnd_1333079 := by exact prefixLift 1333079
  have htrace : WordTrace (prefixWord ++ tailWord_1333079) baseStart_1333079 baseEnd_1333079 := by
    simpa [prefixWord, tailWord_1333079, baseEnd_1333079] using wordTrace_append hprefix tailTrace_1333079
  have hstable : (prefixWord ++ tailWord_1333079).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333079).length < 2 ^ (prefixWord ++ tailWord_1333079).sum := by decide
  have hdescent : baseEnd_1333079 < baseStart_1333079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333090 : List Nat := [3, 3, 2, 1, 2, 3, 1, 6]
def baseStart_1333090 : Nat := 118140960795 + 1333090 * 2 ^ 59
def prefixEnd_1333090 : Nat := 4983230072969 + 3 ^ 40 * 1333090 * 2
def baseEnd_1333090 : Nat := 101409766770710298213961

theorem tailTrace_1333090 : CollatzResearch.WordTrace tailWord_1333090 prefixEnd_1333090 101409766770710298213961 := by
  unfold tailWord_1333090
  simp only [CollatzResearch.WordTrace]
  refine ⟨12155446685112519622771181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32414524493633385660723149 12155446685112519622771181)
  ·
    refine ⟨4558292506917194858539193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12155446685112519622771181 4558292506917194858539193)
    ·
      refine ⟨3418719380187896143904395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4558292506917194858539193 3418719380187896143904395)
      ·
        refine ⟨5128079070281844215856593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3418719380187896143904395 5128079070281844215856593)
        ·
          refine ⟨3846059302711383161892445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5128079070281844215856593 3846059302711383161892445)
          ·
            refine ⟨1442272238516768685709667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3846059302711383161892445 1442272238516768685709667)
            ·
              refine ⟨2163408357775153028564501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1442272238516768685709667 2163408357775153028564501)
              ·
                refine ⟨101409766770710298213961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2163408357775153028564501 101409766770710298213961)
                ·
                  rfl

theorem cell21_1333090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 6].length) (baseStart_1333090 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1333090 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1333090 prefixEnd_1333090 := by exact prefixLift 1333090
  have htrace : WordTrace (prefixWord ++ tailWord_1333090) baseStart_1333090 baseEnd_1333090 := by
    simpa [prefixWord, tailWord_1333090, baseEnd_1333090] using wordTrace_append hprefix tailTrace_1333090
  have hstable : (prefixWord ++ tailWord_1333090).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333090).length < 2 ^ (prefixWord ++ tailWord_1333090).sum := by decide
  have hdescent : baseEnd_1333090 < baseStart_1333090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333172 : List Nat := [2, 5, 2, 1, 3, 1, 1, 3, 3]
def baseStart_1333172 : Nat := 118140960795 + 1333172 * 2 ^ 59
def prefixEnd_1333172 : Nat := 4983230072969 + 3 ^ 40 * 1333172 * 2
def baseEnd_1333172 : Nat := 304248013829316974275049

theorem tailTrace_1333172 : CollatzResearch.WordTrace tailWord_1333172 prefixEnd_1333172 304248013829316974275049 := by
  unfold tailWord_1333172
  simp only [CollatzResearch.WordTrace]
  refine ⟨24312388763076503247784885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32416518350768670997046513 24312388763076503247784885)
  ·
    refine ⟨2279286446538422179479833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24312388763076503247784885 2279286446538422179479833)
    ·
      refine ⟨1709464834903816634609875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2279286446538422179479833 1709464834903816634609875)
      ·
        refine ⟨2564197252355724951914813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1709464834903816634609875 2564197252355724951914813)
        ·
          refine ⟨961573969633396856968055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2564197252355724951914813 961573969633396856968055)
          ·
            refine ⟨1442360954450095285452083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 961573969633396856968055 1442360954450095285452083)
            ·
              refine ⟨2163541431675142928178125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1442360954450095285452083 2163541431675142928178125)
              ·
                refine ⟨811328036878178598066797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2163541431675142928178125 811328036878178598066797)
                ·
                  refine ⟨304248013829316974275049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 811328036878178598066797 304248013829316974275049)
                  ·
                    rfl

theorem cell21_1333172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_1333172 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1333172 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1333172 prefixEnd_1333172 := by exact prefixLift 1333172
  have htrace : WordTrace (prefixWord ++ tailWord_1333172) baseStart_1333172 baseEnd_1333172 := by
    simpa [prefixWord, tailWord_1333172, baseEnd_1333172] using wordTrace_append hprefix tailTrace_1333172
  have hstable : (prefixWord ++ tailWord_1333172).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333172).length < 2 ^ (prefixWord ++ tailWord_1333172).sum := by decide
  have hdescent : baseEnd_1333172 < baseStart_1333172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333177 : List Nat := [1, 2, 1, 4, 2, 1, 1, 1, 8]
def baseStart_1333177 : Nat := 118140960795 + 1333177 * 2 ^ 59
def prefixEnd_1333177 : Nat := 4983230072969 + 3 ^ 40 * 1333177 * 2
def baseEnd_1333177 : Nat := 304249154897438076691705

theorem tailTrace_1333177 : CollatzResearch.WordTrace tailWord_1333177 prefixEnd_1333177 304249154897438076691705 := by
  unfold tailWord_1333177
  simp only [CollatzResearch.WordTrace]
  refine ⟨48624959891134892349501785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32416639927423261566334523 48624959891134892349501785)
  ·
    refine ⟨36468719918351169262126339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48624959891134892349501785 36468719918351169262126339)
    ·
      refine ⟨54703079877526753893189509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36468719918351169262126339 54703079877526753893189509)
      ·
        refine ⟨10256827477036266354973033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54703079877526753893189509 10256827477036266354973033)
        ·
          refine ⟨7692620607777199766229775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10256827477036266354973033 7692620607777199766229775)
          ·
            refine ⟨11538930911665799649344663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7692620607777199766229775 11538930911665799649344663)
            ·
              refine ⟨17308396367498699474016995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11538930911665799649344663 17308396367498699474016995)
              ·
                refine ⟨25962594551248049211025493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17308396367498699474016995 25962594551248049211025493)
                ·
                  refine ⟨304249154897438076691705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25962594551248049211025493 304249154897438076691705)
                  ·
                    rfl

theorem cell21_1333177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 8].length) (baseStart_1333177 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1333177 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1333177 prefixEnd_1333177 := by exact prefixLift 1333177
  have htrace : WordTrace (prefixWord ++ tailWord_1333177) baseStart_1333177 baseEnd_1333177 := by
    simpa [prefixWord, tailWord_1333177, baseEnd_1333177] using wordTrace_append hprefix tailTrace_1333177
  have hstable : (prefixWord ++ tailWord_1333177).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333177).length < 2 ^ (prefixWord ++ tailWord_1333177).sum := by decide
  have hdescent : baseEnd_1333177 < baseStart_1333177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333208 : List Nat := [2, 1, 2, 2, 2, 2, 4, 6]
def baseStart_1333208 : Nat := 118140960795 + 1333208 * 2 ^ 59
def prefixEnd_1333208 : Nat := 4983230072969 + 3 ^ 40 * 1333208 * 2
def baseEnd_1333208 : Nat := 101418743173262970558325

theorem tailTrace_1333208 : CollatzResearch.WordTrace tailWord_1333208 prefixEnd_1333208 101418743173262970558325 := by
  unfold tailWord_1333208
  simp only [CollatzResearch.WordTrace]
  refine ⟨24313045277011292321940139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32417393702681723095920185 24313045277011292321940139)
  ·
    refine ⟨36469567915516938482910209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24313045277011292321940139 36469567915516938482910209)
    ·
      refine ⟨27352175936637703862182657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36469567915516938482910209 27352175936637703862182657)
      ·
        refine ⟨20514131952478277896636993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27352175936637703862182657 20514131952478277896636993)
        ·
          refine ⟨15385598964358708422477745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20514131952478277896636993 15385598964358708422477745)
          ·
            refine ⟨11539199223269031316858309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15385598964358708422477745 11539199223269031316858309)
            ·
              refine ⟨2163599854362943371910933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11539199223269031316858309 2163599854362943371910933)
              ·
                refine ⟨101418743173262970558325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2163599854362943371910933 101418743173262970558325)
                ·
                  rfl

theorem cell21_1333208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 6].length) (baseStart_1333208 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1333208 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1333208 prefixEnd_1333208 := by exact prefixLift 1333208
  have htrace : WordTrace (prefixWord ++ tailWord_1333208) baseStart_1333208 baseEnd_1333208 := by
    simpa [prefixWord, tailWord_1333208, baseEnd_1333208] using wordTrace_append hprefix tailTrace_1333208
  have hstable : (prefixWord ++ tailWord_1333208).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333208).length < 2 ^ (prefixWord ++ tailWord_1333208).sum := by decide
  have hdescent : baseEnd_1333208 < baseStart_1333208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333256 : List Nat := [2, 1, 3, 2, 1, 2, 3, 4, 3]
def baseStart_1333256 : Nat := 118140960795 + 1333256 * 2 ^ 59
def prefixEnd_1333256 : Nat := 4983230072969 + 3 ^ 40 * 1333256 * 2
def baseEnd_1333256 : Nat := 304267183773751494874877

theorem tailTrace_1333256 : CollatzResearch.WordTrace tailWord_1333256 prefixEnd_1333256 304267183773751494874877 := by
  unfold tailWord_1333256
  simp only [CollatzResearch.WordTrace]
  refine ⟨24313920628924344420813811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32418560838565792561085081 24313920628924344420813811)
  ·
    refine ⟨36470880943386516631220717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24313920628924344420813811 36470880943386516631220717)
    ·
      refine ⟨13676580353769943736707769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36470880943386516631220717 13676580353769943736707769)
      ·
        refine ⟨10257435265327457802530827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13676580353769943736707769 10257435265327457802530827)
        ·
          refine ⟨15386152897991186703796241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10257435265327457802530827 15386152897991186703796241)
          ·
            refine ⟨11539614673493390027847181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15386152897991186703796241 11539614673493390027847181)
            ·
              refine ⟨4327355502560021260442693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11539614673493390027847181 4327355502560021260442693)
              ·
                refine ⟨811379156730003986333005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4327355502560021260442693 811379156730003986333005)
                ·
                  refine ⟨304267183773751494874877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 811379156730003986333005 304267183773751494874877)
                  ·
                    rfl

theorem cell21_1333256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 4, 3].length) (baseStart_1333256 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1333256 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1333256 prefixEnd_1333256 := by exact prefixLift 1333256
  have htrace : WordTrace (prefixWord ++ tailWord_1333256) baseStart_1333256 baseEnd_1333256 := by
    simpa [prefixWord, tailWord_1333256, baseEnd_1333256] using wordTrace_append hprefix tailTrace_1333256
  have hstable : (prefixWord ++ tailWord_1333256).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333256).length < 2 ^ (prefixWord ++ tailWord_1333256).sum := by decide
  have hdescent : baseEnd_1333256 < baseStart_1333256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333304 : List Nat := [2, 1, 2, 1, 7, 1, 1, 2, 4]
def baseStart_1333304 : Nat := 118140960795 + 1333304 * 2 ^ 59
def prefixEnd_1333304 : Nat := 4983230072969 + 3 ^ 40 * 1333304 * 2
def baseEnd_1333304 : Nat := 304278138027714078074779

theorem tailTrace_1333304 : CollatzResearch.WordTrace tailWord_1333304 prefixEnd_1333304 304278138027714078074779 := by
  unfold tailWord_1333304
  simp only [CollatzResearch.WordTrace]
  refine ⟨24314795980837396519687483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32419727974449862026249977 24314795980837396519687483)
  ·
    refine ⟨36472193971256094779531225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24314795980837396519687483 36472193971256094779531225)
    ·
      refine ⟨27354145478442071084648419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36472193971256094779531225 27354145478442071084648419)
      ·
        refine ⟨41031218217663106626972629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27354145478442071084648419 41031218217663106626972629)
        ·
          refine ⟨961669176976479061569671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 41031218217663106626972629 961669176976479061569671)
          ·
            refine ⟨1442503765464718592354507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 961669176976479061569671 1442503765464718592354507)
            ·
              refine ⟨2163755648197077888531761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1442503765464718592354507 2163755648197077888531761)
              ·
                refine ⟨1622816736147808416398821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2163755648197077888531761 1622816736147808416398821)
                ·
                  refine ⟨304278138027714078074779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1622816736147808416398821 304278138027714078074779)
                  ·
                    rfl

theorem cell21_1333304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 2, 4].length) (baseStart_1333304 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1333304 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1333304 prefixEnd_1333304 := by exact prefixLift 1333304
  have htrace : WordTrace (prefixWord ++ tailWord_1333304) baseStart_1333304 baseEnd_1333304 := by
    simpa [prefixWord, tailWord_1333304, baseEnd_1333304] using wordTrace_append hprefix tailTrace_1333304
  have hstable : (prefixWord ++ tailWord_1333304).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333304).length < 2 ^ (prefixWord ++ tailWord_1333304).sum := by decide
  have hdescent : baseEnd_1333304 < baseStart_1333304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333349 : List Nat := [1, 3, 1, 3, 2, 4, 1, 3, 3]
def baseStart_1333349 : Nat := 118140960795 + 1333349 * 2 ^ 59
def prefixEnd_1333349 : Nat := 4983230072969 + 3 ^ 40 * 1333349 * 2
def baseEnd_1333349 : Nat := 304288407640803999824687

theorem tailTrace_1333349 : CollatzResearch.WordTrace tailWord_1333349 prefixEnd_1333349 304288407640803999824687 := by
  unfold tailWord_1333349
  simp only [CollatzResearch.WordTrace]
  refine ⟨48631233246511765724763101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32420822164341177149842067 48631233246511765724763101)
  ·
    refine ⟨18236712467441912146786163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48631233246511765724763101 18236712467441912146786163)
    ·
      refine ⟨27355068701162868220179245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18236712467441912146786163 27355068701162868220179245)
      ·
        refine ⟨10258150762936075582567217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27355068701162868220179245 10258150762936075582567217)
        ·
          refine ⟨7693613072202056686925413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10258150762936075582567217 7693613072202056686925413)
          ·
            refine ⟨1442552451037885628798515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7693613072202056686925413 1442552451037885628798515)
            ·
              refine ⟨2163828676556828443197773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1442552451037885628798515 2163828676556828443197773)
              ·
                refine ⟨811435753708810666199165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2163828676556828443197773 811435753708810666199165)
                ·
                  refine ⟨304288407640803999824687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 811435753708810666199165 304288407640803999824687)
                  ·
                    rfl

theorem cell21_1333349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 3, 3].length) (baseStart_1333349 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1333349 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1333349 prefixEnd_1333349 := by exact prefixLift 1333349
  have htrace : WordTrace (prefixWord ++ tailWord_1333349) baseStart_1333349 baseEnd_1333349 := by
    simpa [prefixWord, tailWord_1333349, baseEnd_1333349] using wordTrace_append hprefix tailTrace_1333349
  have hstable : (prefixWord ++ tailWord_1333349).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333349).length < 2 ^ (prefixWord ++ tailWord_1333349).sum := by decide
  have hdescent : baseEnd_1333349 < baseStart_1333349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333360 : List Nat := [2, 1, 1, 1, 5, 4, 7]
def baseStart_1333360 : Nat := 118140960795 + 1333360 * 2 ^ 59
def prefixEnd_1333360 : Nat := 4983230072969 + 3 ^ 40 * 1333360 * 2
def baseEnd_1333360 : Nat := 33810101998963380571259

theorem tailTrace_1333360 : CollatzResearch.WordTrace tailWord_1333360 prefixEnd_1333360 33810101998963380571259 := by
  unfold tailWord_1333360
  simp only [CollatzResearch.WordTrace]
  refine ⟨24315817224735957301706767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32421089632981276402275689 24315817224735957301706767)
  ·
    refine ⟨36473725837103935952560151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24315817224735957301706767 36473725837103935952560151)
    ·
      refine ⟨54710588755655903928840227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36473725837103935952560151 54710588755655903928840227)
      ·
        refine ⟨82065883133483855893260341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54710588755655903928840227 82065883133483855893260341)
        ·
          refine ⟨7693676543764111489993157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 82065883133483855893260341 7693676543764111489993157)
          ·
            refine ⟨1442564351955770904373717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7693676543764111489993157 1442564351955770904373717)
            ·
              refine ⟨33810101998963380571259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1442564351955770904373717 33810101998963380571259)
              ·
                rfl

theorem cell21_1333360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 7].length) (baseStart_1333360 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1333360 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1333360 prefixEnd_1333360 := by exact prefixLift 1333360
  have htrace : WordTrace (prefixWord ++ tailWord_1333360) baseStart_1333360 baseEnd_1333360 := by
    simpa [prefixWord, tailWord_1333360, baseEnd_1333360] using wordTrace_append hprefix tailTrace_1333360
  have hstable : (prefixWord ++ tailWord_1333360).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333360).length < 2 ^ (prefixWord ++ tailWord_1333360).sum := by decide
  have hdescent : baseEnd_1333360 < baseStart_1333360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333366 : List Nat := [5, 1, 1, 2, 1, 3, 3, 2, 3]
def baseStart_1333366 : Nat := 118140960795 + 1333366 * 2 ^ 59
def prefixEnd_1333366 : Nat := 4983230072969 + 3 ^ 40 * 1333366 * 2
def baseEnd_1333366 : Nat := 304292287272415748041319

theorem tailTrace_1333366 : CollatzResearch.WordTrace tailWord_1333366 prefixEnd_1333366 304292287272415748041319 := by
  unfold tailWord_1333366
  simp only [CollatzResearch.WordTrace]
  refine ⟨3039490830465636101758247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32421235524966785085421301 3039490830465636101758247)
  ·
    refine ⟨4559236245698454152637371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3039490830465636101758247 4559236245698454152637371)
    ·
      refine ⟨6838854368547681228956057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4559236245698454152637371 6838854368547681228956057)
      ·
        refine ⟨5129140776410760921717043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6838854368547681228956057 5129140776410760921717043)
        ·
          refine ⟨7693711164616141382575565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5129140776410760921717043 7693711164616141382575565)
          ·
            refine ⟨2885141686731053018465837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7693711164616141382575565 2885141686731053018465837)
            ·
              refine ⟨1081928132524144881924689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2885141686731053018465837 1081928132524144881924689)
              ·
                refine ⟨811446099393108661443517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1081928132524144881924689 811446099393108661443517)
                ·
                  refine ⟨304292287272415748041319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 811446099393108661443517 304292287272415748041319)
                  ·
                    rfl

theorem cell21_1333366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 3, 2, 3].length) (baseStart_1333366 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1333366 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1333366 prefixEnd_1333366 := by exact prefixLift 1333366
  have htrace : WordTrace (prefixWord ++ tailWord_1333366) baseStart_1333366 baseEnd_1333366 := by
    simpa [prefixWord, tailWord_1333366, baseEnd_1333366] using wordTrace_append hprefix tailTrace_1333366
  have hstable : (prefixWord ++ tailWord_1333366).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333366).length < 2 ^ (prefixWord ++ tailWord_1333366).sum := by decide
  have hdescent : baseEnd_1333366 < baseStart_1333366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333377 : List Nat := [1, 2, 4, 2, 3, 1, 2, 6]
def baseStart_1333377 : Nat := 118140960795 + 1333377 * 2 ^ 59
def prefixEnd_1333377 : Nat := 4983230072969 + 3 ^ 40 * 1333377 * 2
def baseEnd_1333377 : Nat := 101431599207427391119321

theorem tailTrace_1333377 : CollatzResearch.WordTrace tailWord_1333377 prefixEnd_1333377 101431599207427391119321 := by
  unfold tailWord_1333377
  simp only [CollatzResearch.WordTrace]
  refine ⟨48632254490410326506782385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32421502993606884337854923 48632254490410326506782385)
  ·
    refine ⟨36474190867807744880086789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48632254490410326506782385 36474190867807744880086789)
    ·
      refine ⟨6838910787713952165016273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36474190867807744880086789 6838910787713952165016273)
      ·
        refine ⟨5129183090785464123762205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6838910787713952165016273 5129183090785464123762205)
        ·
          refine ⟨1923443659044549046410827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5129183090785464123762205 1923443659044549046410827)
          ·
            refine ⟨2885165488566823569616241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1923443659044549046410827 2885165488566823569616241)
            ·
              refine ⟨2163874116425117677212181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2885165488566823569616241 2163874116425117677212181)
              ·
                refine ⟨101431599207427391119321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2163874116425117677212181 101431599207427391119321)
                ·
                  rfl

theorem cell21_1333377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 6].length) (baseStart_1333377 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1333377 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1333377 prefixEnd_1333377 := by exact prefixLift 1333377
  have htrace : WordTrace (prefixWord ++ tailWord_1333377) baseStart_1333377 baseEnd_1333377 := by
    simpa [prefixWord, tailWord_1333377, baseEnd_1333377] using wordTrace_append hprefix tailTrace_1333377
  have hstable : (prefixWord ++ tailWord_1333377).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333377).length < 2 ^ (prefixWord ++ tailWord_1333377).sum := by decide
  have hdescent : baseEnd_1333377 < baseStart_1333377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333425 : List Nat := [1, 2, 2, 5, 2, 1, 1, 4, 3]
def baseStart_1333425 : Nat := 118140960795 + 1333425 * 2 ^ 59
def prefixEnd_1333425 : Nat := 4983230072969 + 3 ^ 40 * 1333425 * 2
def baseEnd_1333425 : Nat := 304305751876244756557865

theorem tailTrace_1333425 : CollatzResearch.WordTrace tailWord_1333425 prefixEnd_1333425 304305751876244756557865 := by
  unfold tailWord_1333425
  simp only [CollatzResearch.WordTrace]
  refine ⟨48634005194236430704529729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32422670129490953803019819 48634005194236430704529729)
  ·
    refine ⟨36475503895677323028397297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48634005194236430704529729 36475503895677323028397297)
    ·
      refine ⟨27356627921757992271297973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36475503895677323028397297 27356627921757992271297973)
      ·
        refine ⟨2564683867664811775434185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27356627921757992271297973 2564683867664811775434185)
        ·
          refine ⟨1923512900748608831575639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2564683867664811775434185 1923512900748608831575639)
          ·
            refine ⟨2885269351122913247363459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1923512900748608831575639 2885269351122913247363459)
            ·
              refine ⟨4327904026684369871045189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2885269351122913247363459 4327904026684369871045189)
              ·
                refine ⟨811482005003319350820973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4327904026684369871045189 811482005003319350820973)
                ·
                  refine ⟨304305751876244756557865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 811482005003319350820973 304305751876244756557865)
                  ·
                    rfl

theorem cell21_1333425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 4, 3].length) (baseStart_1333425 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1333425 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1333425 prefixEnd_1333425 := by exact prefixLift 1333425
  have htrace : WordTrace (prefixWord ++ tailWord_1333425) baseStart_1333425 baseEnd_1333425 := by
    simpa [prefixWord, tailWord_1333425, baseEnd_1333425] using wordTrace_append hprefix tailTrace_1333425
  have hstable : (prefixWord ++ tailWord_1333425).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333425).length < 2 ^ (prefixWord ++ tailWord_1333425).sum := by decide
  have hdescent : baseEnd_1333425 < baseStart_1333425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333428 : List Nat := [2, 5, 3, 1, 1, 2, 1, 6]
def baseStart_1333428 : Nat := 118140960795 + 1333428 * 2 ^ 59
def prefixEnd_1333428 : Nat := 4983230072969 + 3 ^ 40 * 1333428 * 2
def baseEnd_1333428 : Nat := 101435478839039139335953

theorem tailTrace_1333428 : CollatzResearch.WordTrace tailWord_1333428 prefixEnd_1333428 101435478839039139335953 := by
  unfold tailWord_1333428
  simp only [CollatzResearch.WordTrace]
  refine ⟨24317057306612781108444469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32422743075483708144592625 24317057306612781108444469)
  ·
    refine ⟨2279724122494948228916669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24317057306612781108444469 2279724122494948228916669)
    ·
      refine ⟨854896545935605585843751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2279724122494948228916669 854896545935605585843751)
      ·
        refine ⟨1282344818903408378765627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 854896545935605585843751 1282344818903408378765627)
        ·
          refine ⟨1923517228355112568148441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1282344818903408378765627 1923517228355112568148441)
          ·
            refine ⟨1442637921266334426111331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1923517228355112568148441 1442637921266334426111331)
            ·
              refine ⟨2163956881899501639166997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1442637921266334426111331 2163956881899501639166997)
              ·
                refine ⟨101435478839039139335953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2163956881899501639166997 101435478839039139335953)
                ·
                  rfl

theorem cell21_1333428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 6].length) (baseStart_1333428 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1333428 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1333428 prefixEnd_1333428 := by exact prefixLift 1333428
  have htrace : WordTrace (prefixWord ++ tailWord_1333428) baseStart_1333428 baseEnd_1333428 := by
    simpa [prefixWord, tailWord_1333428, baseEnd_1333428] using wordTrace_append hprefix tailTrace_1333428
  have hstable : (prefixWord ++ tailWord_1333428).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333428).length < 2 ^ (prefixWord ++ tailWord_1333428).sum := by decide
  have hdescent : baseEnd_1333428 < baseStart_1333428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333467 : List Nat := [1, 1, 1, 1, 1, 1, 1, 11, 3]
def baseStart_1333467 : Nat := 118140960795 + 1333467 * 2 ^ 59
def prefixEnd_1333467 : Nat := 4983230072969 + 3 ^ 40 * 1333467 * 2
def baseEnd_1333467 : Nat := 304315336848462016857779

theorem tailTrace_1333467 : CollatzResearch.WordTrace tailWord_1333467 prefixEnd_1333467 304315336848462016857779 := by
  unfold tailWord_1333467
  simp only [CollatzResearch.WordTrace]
  refine ⟨48635537060084271877558655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32423691373389514585039103 48635537060084271877558655)
  ·
    refine ⟨72953305590126407816337983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48635537060084271877558655 72953305590126407816337983)
    ·
      refine ⟨109429958385189611724506975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72953305590126407816337983 109429958385189611724506975)
      ·
        refine ⟨164144937577784417586760463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109429958385189611724506975 164144937577784417586760463)
        ·
          refine ⟨246217406366676626380140695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164144937577784417586760463 246217406366676626380140695)
          ·
            refine ⟨369326109550014939570211043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246217406366676626380140695 369326109550014939570211043)
            ·
              refine ⟨553989164325022409355316565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 369326109550014939570211043 553989164325022409355316565)
              ·
                refine ⟨811507564929232044954077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 553989164325022409355316565 811507564929232044954077)
                ·
                  refine ⟨304315336848462016857779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 811507564929232044954077 304315336848462016857779)
                  ·
                    rfl

theorem cell21_1333467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 11, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 11, 3].length) (baseStart_1333467 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1333467 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1333467 prefixEnd_1333467 := by exact prefixLift 1333467
  have htrace : WordTrace (prefixWord ++ tailWord_1333467) baseStart_1333467 baseEnd_1333467 := by
    simpa [prefixWord, tailWord_1333467, baseEnd_1333467] using wordTrace_append hprefix tailTrace_1333467
  have hstable : (prefixWord ++ tailWord_1333467).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333467).length < 2 ^ (prefixWord ++ tailWord_1333467).sum := by decide
  have hdescent : baseEnd_1333467 < baseStart_1333467 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333512 : List Nat := [2, 1, 3, 2, 3, 2, 1, 7]
def baseStart_1333512 : Nat := 118140960795 + 1333512 * 2 ^ 59
def prefixEnd_1333512 : Nat := 4983230072969 + 3 ^ 40 * 1333512 * 2
def baseEnd_1333512 : Nat := 101441868820517312869229

theorem tailTrace_1333512 : CollatzResearch.WordTrace tailWord_1333512 prefixEnd_1333512 101441868820517312869229 := by
  unfold tailWord_1333512
  simp only [CollatzResearch.WordTrace]
  refine ⟨24318589172460622281473395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32424785563280829708631193 24318589172460622281473395)
  ·
    refine ⟨36477883758690933422210093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24318589172460622281473395 36477883758690933422210093)
    ·
      refine ⟨13679206409509100033328785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36477883758690933422210093 13679206409509100033328785)
      ·
        refine ⟨10259404807131825024996589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13679206409509100033328785 10259404807131825024996589)
        ·
          refine ⟨3847276802674434384373721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10259404807131825024996589 3847276802674434384373721)
          ·
            refine ⟨2885457602005825788280291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3847276802674434384373721 2885457602005825788280291)
            ·
              refine ⟨4328186403008738682420437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2885457602005825788280291 4328186403008738682420437)
              ·
                refine ⟨101441868820517312869229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4328186403008738682420437 101441868820517312869229)
                ·
                  rfl

theorem cell21_1333512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 7].length) (baseStart_1333512 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1333512 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1333512 prefixEnd_1333512 := by exact prefixLift 1333512
  have htrace : WordTrace (prefixWord ++ tailWord_1333512) baseStart_1333512 baseEnd_1333512 := by
    simpa [prefixWord, tailWord_1333512, baseEnd_1333512] using wordTrace_append hprefix tailTrace_1333512
  have hstable : (prefixWord ++ tailWord_1333512).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333512).length < 2 ^ (prefixWord ++ tailWord_1333512).sum := by decide
  have hdescent : baseEnd_1333512 < baseStart_1333512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333549 : List Nat := [1, 5, 3, 1, 2, 2, 2, 1, 4]
def baseStart_1333549 : Nat := 118140960795 + 1333549 * 2 ^ 59
def prefixEnd_1333549 : Nat := 4983230072969 + 3 ^ 40 * 1333549 * 2
def baseEnd_1333549 : Nat := 304334050365648096490945

theorem tailTrace_1333549 : CollatzResearch.WordTrace tailWord_1333549 prefixEnd_1333549 304334050365648096490945 := by
  unfold tailWord_1333549
  simp only [CollatzResearch.WordTrace]
  refine ⟨48638527845787199882043701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32425685230524799921362467 48638527845787199882043701)
  ·
    refine ⟨4559861985542549988941597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48638527845787199882043701 4559861985542549988941597)
    ·
      refine ⟨1709948244578456245853099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4559861985542549988941597 1709948244578456245853099)
      ·
        refine ⟨2564922366867684368779649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1709948244578456245853099 2564922366867684368779649)
        ·
          refine ⟨1923691775150763276584737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2564922366867684368779649 1923691775150763276584737)
          ·
            refine ⟨1442768831363072457438553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1923691775150763276584737 1442768831363072457438553)
            ·
              refine ⟨1082076623522304343078915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1442768831363072457438553 1082076623522304343078915)
              ·
                refine ⟨1623114935283456514618373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1082076623522304343078915 1623114935283456514618373)
                ·
                  refine ⟨304334050365648096490945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1623114935283456514618373 304334050365648096490945)
                  ·
                    rfl

theorem cell21_1333549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_1333549 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1333549 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1333549 prefixEnd_1333549 := by exact prefixLift 1333549
  have htrace : WordTrace (prefixWord ++ tailWord_1333549) baseStart_1333549 baseEnd_1333549 := by
    simpa [prefixWord, tailWord_1333549, baseEnd_1333549] using wordTrace_append hprefix tailTrace_1333549
  have hstable : (prefixWord ++ tailWord_1333549).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333549).length < 2 ^ (prefixWord ++ tailWord_1333549).sum := by decide
  have hdescent : baseEnd_1333549 < baseStart_1333549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333571 : List Nat := [1, 1, 1, 3, 1, 3, 4, 7]
def baseStart_1333571 : Nat := 118140960795 + 1333571 * 2 ^ 59
def prefixEnd_1333571 : Nat := 4983230072969 + 3 ^ 40 * 1333571 * 2
def baseEnd_1333571 : Nat := 101446357021793649041411

theorem tailTrace_1333571 : CollatzResearch.WordTrace tailWord_1333571 prefixEnd_1333571 101446357021793649041411 := by
  unfold tailWord_1333571
  simp only [CollatzResearch.WordTrace]
  refine ⟨48639330251707497639344567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32426220167804998426229711 48639330251707497639344567)
  ·
    refine ⟨72958995377561246459016851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48639330251707497639344567 72958995377561246459016851)
    ·
      refine ⟨109438493066341869688525277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72958995377561246459016851 109438493066341869688525277)
      ·
        refine ⟨41039434899878201133196979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109438493066341869688525277 41039434899878201133196979)
        ·
          refine ⟨61559152349817301699795469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41039434899878201133196979 61559152349817301699795469)
          ·
            refine ⟨23084682131181488137423301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61559152349817301699795469 23084682131181488137423301)
            ·
              refine ⟨4328377899596529025766869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23084682131181488137423301 4328377899596529025766869)
              ·
                refine ⟨101446357021793649041411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4328377899596529025766869 101446357021793649041411)
                ·
                  rfl

theorem cell21_1333571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 7].length) (baseStart_1333571 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1333571 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1333571 prefixEnd_1333571 := by exact prefixLift 1333571
  have htrace : WordTrace (prefixWord ++ tailWord_1333571) baseStart_1333571 baseEnd_1333571 := by
    simpa [prefixWord, tailWord_1333571, baseEnd_1333571] using wordTrace_append hprefix tailTrace_1333571
  have hstable : (prefixWord ++ tailWord_1333571).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333571).length < 2 ^ (prefixWord ++ tailWord_1333571).sum := by decide
  have hdescent : baseEnd_1333571 < baseStart_1333571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333636 : List Nat := [2, 3, 2, 1, 1, 2, 4, 3, 3]
def baseStart_1333636 : Nat := 118140960795 + 1333636 * 2 ^ 59
def prefixEnd_1333636 : Nat := 4983230072969 + 3 ^ 40 * 1333636 * 2
def baseEnd_1333636 : Nat := 304353904950955278540767

theorem tailTrace_1333636 : CollatzResearch.WordTrace tailWord_1333636 prefixEnd_1333636 304353904950955278540767 := by
  unfold tailWord_1333636
  simp only [CollatzResearch.WordTrace]
  refine ⟨24320850498236006870230381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32427800664314675826973841 24320850498236006870230381)
  ·
    refine ⟨9120318936838502576336393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24320850498236006870230381 9120318936838502576336393)
    ·
      refine ⟨6840239202628876932252295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9120318936838502576336393 6840239202628876932252295)
      ·
        refine ⟨10260358803943315398378443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6840239202628876932252295 10260358803943315398378443)
        ·
          refine ⟨15390538205914973097567665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10260358803943315398378443 15390538205914973097567665)
          ·
            refine ⟨11542903654436229823175749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15390538205914973097567665 11542903654436229823175749)
            ·
              refine ⟨2164294435206793091845453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11542903654436229823175749 2164294435206793091845453)
              ·
                refine ⟨811610413202547409442045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2164294435206793091845453 811610413202547409442045)
                ·
                  refine ⟨304353904950955278540767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 811610413202547409442045 304353904950955278540767)
                  ·
                    rfl

theorem cell21_1333636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 3, 3].length) (baseStart_1333636 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1333636 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1333636 prefixEnd_1333636 := by exact prefixLift 1333636
  have htrace : WordTrace (prefixWord ++ tailWord_1333636) baseStart_1333636 baseEnd_1333636 := by
    simpa [prefixWord, tailWord_1333636, baseEnd_1333636] using wordTrace_append hprefix tailTrace_1333636
  have hstable : (prefixWord ++ tailWord_1333636).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333636).length < 2 ^ (prefixWord ++ tailWord_1333636).sum := by decide
  have hdescent : baseEnd_1333636 < baseStart_1333636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333681 : List Nat := [1, 2, 2, 4, 1, 4, 2, 5]
def baseStart_1333681 : Nat := 118140960795 + 1333681 * 2 ^ 59
def prefixEnd_1333681 : Nat := 4983230072969 + 3 ^ 40 * 1333681 * 2
def baseEnd_1333681 : Nat := 101454724854681733430225

theorem tailTrace_1333681 : CollatzResearch.WordTrace tailWord_1333681 prefixEnd_1333681 101454724854681733430225 := by
  unfold tailWord_1333681
  simp only [CollatzResearch.WordTrace]
  refine ⟨48643342281308986425848897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32428894854205990950565931 48643342281308986425848897)
  ·
    refine ⟨36482506710981739819386673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48643342281308986425848897 36482506710981739819386673)
    ·
      refine ⟨27361880033236304864540005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36482506710981739819386673 27361880033236304864540005)
      ·
        refine ⟨5130352506231807162101251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27361880033236304864540005 5130352506231807162101251)
        ·
          refine ⟨7695528759347710743151877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5130352506231807162101251 7695528759347710743151877)
          ·
            refine ⟨1442911642377695764340977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7695528759347710743151877 1442911642377695764340977)
            ·
              refine ⟨1082183731783271823255733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1442911642377695764340977 1082183731783271823255733)
              ·
                refine ⟨101454724854681733430225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1082183731783271823255733 101454724854681733430225)
                ·
                  rfl

theorem cell21_1333681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 2, 5].length) (baseStart_1333681 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1333681 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1333681 prefixEnd_1333681 := by exact prefixLift 1333681
  have htrace : WordTrace (prefixWord ++ tailWord_1333681) baseStart_1333681 baseEnd_1333681 := by
    simpa [prefixWord, tailWord_1333681, baseEnd_1333681] using wordTrace_append hprefix tailTrace_1333681
  have hstable : (prefixWord ++ tailWord_1333681).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333681).length < 2 ^ (prefixWord ++ tailWord_1333681).sum := by decide
  have hdescent : baseEnd_1333681 < baseStart_1333681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333892 : List Nat := [2, 3, 2, 1, 3, 2, 2, 6]
def baseStart_1333892 : Nat := 118140960795 + 1333892 * 2 ^ 59
def prefixEnd_1333892 : Nat := 4983230072969 + 3 ^ 40 * 1333892 * 2
def baseEnd_1333892 : Nat := 101470775879585240757859

theorem tailTrace_1333892 : CollatzResearch.WordTrace tailWord_1333892 prefixEnd_1333892 101470775879585240757859 := by
  unfold tailWord_1333892
  simp only [CollatzResearch.WordTrace]
  refine ⟨24325519041772284730889965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32434025389029712974519953 24325519041772284730889965)
  ·
    refine ⟨9122069640664606774083737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24325519041772284730889965 9122069640664606774083737)
    ·
      refine ⟨6841552230498455080562803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9122069640664606774083737 6841552230498455080562803)
      ·
        refine ⟨10262328345747682620844205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6841552230498455080562803 10262328345747682620844205)
        ·
          refine ⟨3848373129655380982816577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10262328345747682620844205 3848373129655380982816577)
          ·
            refine ⟨2886279847241535737112433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3848373129655380982816577 2886279847241535737112433)
            ·
              refine ⟨2164709885431151802834325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2886279847241535737112433 2164709885431151802834325)
              ·
                refine ⟨101470775879585240757859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2164709885431151802834325 101470775879585240757859)
                ·
                  rfl

theorem cell21_1333892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 6].length) (baseStart_1333892 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1333892 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1333892 prefixEnd_1333892 := by exact prefixLift 1333892
  have htrace : WordTrace (prefixWord ++ tailWord_1333892) baseStart_1333892 baseEnd_1333892 := by
    simpa [prefixWord, tailWord_1333892, baseEnd_1333892] using wordTrace_append hprefix tailTrace_1333892
  have hstable : (prefixWord ++ tailWord_1333892).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333892).length < 2 ^ (prefixWord ++ tailWord_1333892).sum := by decide
  have hdescent : baseEnd_1333892 < baseStart_1333892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333951 : List Nat := [1, 1, 2, 2, 2, 4, 3, 6]
def baseStart_1333951 : Nat := 118140960795 + 1333951 * 2 ^ 59
def prefixEnd_1333951 : Nat := 4983230072969 + 3 ^ 40 * 1333951 * 2
def baseEnd_1333951 : Nat := 101475264080861576930041

theorem tailTrace_1333951 : CollatzResearch.WordTrace tailWord_1333951 prefixEnd_1333951 101475264080861576930041 := by
  unfold tailWord_1333951
  simp only [CollatzResearch.WordTrace]
  refine ⟨48653189990330822538177707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32435459993553881692118471 48653189990330822538177707)
  ·
    refine ⟨72979784985496233807266561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48653189990330822538177707 72979784985496233807266561)
    ·
      refine ⟨54734838739122175355449921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72979784985496233807266561 54734838739122175355449921)
      ·
        refine ⟨41051129054341631516587441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54734838739122175355449921 41051129054341631516587441)
        ·
          refine ⟨30788346790756223637440581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41051129054341631516587441 30788346790756223637440581)
          ·
            refine ⟨5772815023266791932020109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30788346790756223637440581 5772815023266791932020109)
            ·
              refine ⟨2164805633725046974507541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5772815023266791932020109 2164805633725046974507541)
              ·
                refine ⟨101475264080861576930041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2164805633725046974507541 101475264080861576930041)
                ·
                  rfl

theorem cell21_1333951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 6].length) (baseStart_1333951 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1333951 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1333951 prefixEnd_1333951 := by exact prefixLift 1333951
  have htrace : WordTrace (prefixWord ++ tailWord_1333951) baseStart_1333951 baseEnd_1333951 := by
    simpa [prefixWord, tailWord_1333951, baseEnd_1333951] using wordTrace_append hprefix tailTrace_1333951
  have hstable : (prefixWord ++ tailWord_1333951).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333951).length < 2 ^ (prefixWord ++ tailWord_1333951).sum := by decide
  have hdescent : baseEnd_1333951 < baseStart_1333951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1333999 : List Nat := [1, 1, 2, 1, 5, 2, 2, 4, 3]
def baseStart_1333999 : Nat := 118140960795 + 1333999 * 2 ^ 59
def prefixEnd_1333999 : Nat := 4983230072969 + 3 ^ 40 * 1333999 * 2
def baseEnd_1333999 : Nat := 304436746496547313990025

theorem tailTrace_1333999 : CollatzResearch.WordTrace tailWord_1333999 prefixEnd_1333999 304436746496547313990025 := by
  unfold tailWord_1333999
  simp only [CollatzResearch.WordTrace]
  refine ⟨48654940694156926735925051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32436627129437951157283367 48654940694156926735925051)
  ·
    refine ⟨72982411041235390103887577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48654940694156926735925051 72982411041235390103887577)
    ·
      refine ⟨54736808280926542577915683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72982411041235390103887577 54736808280926542577915683)
      ·
        refine ⟨82105212421389813866873525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54736808280926542577915683 82105212421389813866873525)
        ·
          refine ⟨7697363664505295050019393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 82105212421389813866873525 7697363664505295050019393)
          ·
            refine ⟨5773022748378971287514545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7697363664505295050019393 5773022748378971287514545)
            ·
              refine ⟨4329767061284228465635909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5773022748378971287514545 4329767061284228465635909)
              ·
                refine ⟨811831323990792837306733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4329767061284228465635909 811831323990792837306733)
                ·
                  refine ⟨304436746496547313990025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 811831323990792837306733 304436746496547313990025)
                  ·
                    rfl

theorem cell21_1333999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 4, 3].length) (baseStart_1333999 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1333999 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1333999 prefixEnd_1333999 := by exact prefixLift 1333999
  have htrace : WordTrace (prefixWord ++ tailWord_1333999) baseStart_1333999 baseEnd_1333999 := by
    simpa [prefixWord, tailWord_1333999, baseEnd_1333999] using wordTrace_append hprefix tailTrace_1333999
  have hstable : (prefixWord ++ tailWord_1333999).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1333999).length < 2 ^ (prefixWord ++ tailWord_1333999).sum := by decide
  have hdescent : baseEnd_1333999 < baseStart_1333999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1333999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334005 : List Nat := [1, 3, 6, 1, 1, 1, 3, 1, 4]
def baseStart_1334005 : Nat := 118140960795 + 1334005 * 2 ^ 59
def prefixEnd_1334005 : Nat := 4983230072969 + 3 ^ 40 * 1334005 * 2
def baseEnd_1334005 : Nat := 304438115778292636890013

theorem tailTrace_1334005 : CollatzResearch.WordTrace tailWord_1334005 prefixEnd_1334005 304438115778292636890013 := by
  unfold tailWord_1334005
  simp only [CollatzResearch.WordTrace]
  refine ⟨48655159532135189760643469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32436773021423459840428979 48655159532135189760643469)
  ·
    refine ⟨18245684824550696160241301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48655159532135189760643469 18245684824550696160241301)
    ·
      refine ⟨855266476150813882511311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 18245684824550696160241301 855266476150813882511311)
      ·
        refine ⟨1282899714226220823766967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 855266476150813882511311 1282899714226220823766967)
        ·
          refine ⟨1924349571339331235650451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1282899714226220823766967 1924349571339331235650451)
          ·
            refine ⟨2886524357008996853475677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1924349571339331235650451 2886524357008996853475677)
            ·
              refine ⟨1082446633878373820053379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2886524357008996853475677 1082446633878373820053379)
              ·
                refine ⟨1623669950817560730080069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1082446633878373820053379 1623669950817560730080069)
                ·
                  refine ⟨304438115778292636890013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1623669950817560730080069 304438115778292636890013)
                  ·
                    rfl

theorem cell21_1334005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 3, 1, 4].length) (baseStart_1334005 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1334005 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1334005 prefixEnd_1334005 := by exact prefixLift 1334005
  have htrace : WordTrace (prefixWord ++ tailWord_1334005) baseStart_1334005 baseEnd_1334005 := by
    simpa [prefixWord, tailWord_1334005, baseEnd_1334005] using wordTrace_append hprefix tailTrace_1334005
  have hstable : (prefixWord ++ tailWord_1334005).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334005).length < 2 ^ (prefixWord ++ tailWord_1334005).sum := by decide
  have hdescent : baseEnd_1334005 < baseStart_1334005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334120 : List Nat := [2, 1, 4, 2, 1, 4, 1, 6]
def baseStart_1334120 : Nat := 118140960795 + 1334120 * 2 ^ 59
def prefixEnd_1334120 : Nat := 4983230072969 + 3 ^ 40 * 1334120 * 2
def baseEnd_1334120 : Nat := 101488120115025997491037

theorem tailTrace_1334120 : CollatzResearch.WordTrace tailWord_1334120 prefixEnd_1334120 101488120115025997491037 := by
  unfold tailWord_1334120
  simp only [CollatzResearch.WordTrace]
  refine ⟨24329676963359282200539907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32439569284479042934053209 24329676963359282200539907)
  ·
    refine ⟨36494515445038923300809861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24329676963359282200539907 36494515445038923300809861)
    ·
      refine ⟨6842721645944798118901849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36494515445038923300809861 6842721645944798118901849)
      ·
        refine ⟨5132041234458598589176387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6842721645944798118901849 5132041234458598589176387)
        ·
          refine ⟨7698061851687897883764581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5132041234458598589176387 7698061851687897883764581)
          ·
            refine ⟨1443386597191480853205859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7698061851687897883764581 1443386597191480853205859)
            ·
              refine ⟨2165079895787221279808789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1443386597191480853205859 2165079895787221279808789)
              ·
                refine ⟨101488120115025997491037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2165079895787221279808789 101488120115025997491037)
                ·
                  rfl

theorem cell21_1334120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 6].length) (baseStart_1334120 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1334120 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1334120 prefixEnd_1334120 := by exact prefixLift 1334120
  have htrace : WordTrace (prefixWord ++ tailWord_1334120) baseStart_1334120 baseEnd_1334120 := by
    simpa [prefixWord, tailWord_1334120, baseEnd_1334120] using wordTrace_append hprefix tailTrace_1334120
  have hstable : (prefixWord ++ tailWord_1334120).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334120).length < 2 ^ (prefixWord ++ tailWord_1334120).sum := by decide
  have hdescent : baseEnd_1334120 < baseStart_1334120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334148 : List Nat := [2, 3, 2, 1, 1, 1, 1, 4, 6]
def baseStart_1334148 : Nat := 118140960795 + 1334148 * 2 ^ 59
def prefixEnd_1334148 : Nat := 4983230072969 + 3 ^ 40 * 1334148 * 2
def baseEnd_1334148 : Nat := 304470750326556166006387

theorem tailTrace_1334148 : CollatzResearch.WordTrace tailWord_1334148 prefixEnd_1334148 304470750326556166006387 := by
  unfold tailWord_1334148
  simp only [CollatzResearch.WordTrace]
  refine ⟨24330187585308562591549549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32440250113744750122066065 24330187585308562591549549)
  ·
    refine ⟨9123820344490710971831081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24330187585308562591549549 9123820344490710971831081)
    ·
      refine ⟨6842865258368033228873311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9123820344490710971831081 6842865258368033228873311)
      ·
        refine ⟨10264297887552049843309967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6842865258368033228873311 10264297887552049843309967)
        ·
          refine ⟨15396446831328074764964951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10264297887552049843309967 15396446831328074764964951)
          ·
            refine ⟨23094670246992112147447427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15396446831328074764964951 23094670246992112147447427)
            ·
              refine ⟨34642005370488168221171141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23094670246992112147447427 34642005370488168221171141)
              ·
                refine ⟨6495376006966531541469589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34642005370488168221171141 6495376006966531541469589)
                ·
                  refine ⟨304470750326556166006387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6495376006966531541469589 304470750326556166006387)
                  ·
                    rfl

theorem cell21_1334148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 4, 6].length) (baseStart_1334148 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1334148 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1334148 prefixEnd_1334148 := by exact prefixLift 1334148
  have htrace : WordTrace (prefixWord ++ tailWord_1334148) baseStart_1334148 baseEnd_1334148 := by
    simpa [prefixWord, tailWord_1334148, baseEnd_1334148] using wordTrace_append hprefix tailTrace_1334148
  have hstable : (prefixWord ++ tailWord_1334148).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334148).length < 2 ^ (prefixWord ++ tailWord_1334148).sum := by decide
  have hdescent : baseEnd_1334148 < baseStart_1334148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334151 : List Nat := [1, 1, 4, 2, 3, 1, 1, 5, 3]
def baseStart_1334151 : Nat := 118140960795 + 1334151 * 2 ^ 59
def prefixEnd_1334151 : Nat := 4983230072969 + 3 ^ 40 * 1334151 * 2
def baseEnd_1334151 : Nat := 304471434967428827456381

theorem tailTrace_1334151 : CollatzResearch.WordTrace tailWord_1334151 prefixEnd_1334151 304471434967428827456381 := by
  unfold tailWord_1334151
  simp only [CollatzResearch.WordTrace]
  refine ⟨48660484589606256695458307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32440323059737504463638871 48660484589606256695458307)
  ·
    refine ⟨72990726884409385043187461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48660484589606256695458307 72990726884409385043187461)
    ·
      refine ⟨13685761290826759695597649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72990726884409385043187461 13685761290826759695597649)
      ·
        refine ⟨10264320968120069771698237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13685761290826759695597649 10264320968120069771698237)
        ·
          refine ⟨3849120363045026164386839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10264320968120069771698237 3849120363045026164386839)
          ·
            refine ⟨5773680544567539246580259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3849120363045026164386839 5773680544567539246580259)
            ·
              refine ⟨8660520816851308869870389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5773680544567539246580259 8660520816851308869870389)
              ·
                refine ⟨811923826579810206550349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8660520816851308869870389 811923826579810206550349)
                ·
                  refine ⟨304471434967428827456381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 811923826579810206550349 304471434967428827456381)
                  ·
                    rfl

theorem cell21_1334151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 5, 3].length) (baseStart_1334151 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1334151 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1334151 prefixEnd_1334151 := by exact prefixLift 1334151
  have htrace : WordTrace (prefixWord ++ tailWord_1334151) baseStart_1334151 baseEnd_1334151 := by
    simpa [prefixWord, tailWord_1334151, baseEnd_1334151] using wordTrace_append hprefix tailTrace_1334151
  have hstable : (prefixWord ++ tailWord_1334151).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334151).length < 2 ^ (prefixWord ++ tailWord_1334151).sum := by decide
  have hdescent : baseEnd_1334151 < baseStart_1334151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334165 : List Nat := [1, 3, 2, 1, 1, 4, 3, 2, 4]
def baseStart_1334165 : Nat := 118140960795 + 1334165 * 2 ^ 59
def prefixEnd_1334165 : Nat := 4983230072969 + 3 ^ 40 * 1334165 * 2
def baseEnd_1334165 : Nat := 304474629958167914223019

theorem tailTrace_1334165 : CollatzResearch.WordTrace tailWord_1334165 prefixEnd_1334165 304474629958167914223019 := by
  unfold tailWord_1334165
  simp only [CollatzResearch.WordTrace]
  refine ⟨48660995211555537086467949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32440663474370358057645299 48660995211555537086467949)
  ·
    refine ⟨18247873204333326407425481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48660995211555537086467949 18247873204333326407425481)
    ·
      refine ⟨13685904903249994805569111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18247873204333326407425481 13685904903249994805569111)
      ·
        refine ⟨20528857354874992208353667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13685904903249994805569111 20528857354874992208353667)
        ·
          refine ⟨30793286032312488312530501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20528857354874992208353667 30793286032312488312530501)
          ·
            refine ⟨5773741131058591558599469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30793286032312488312530501 5773741131058591558599469)
            ·
              refine ⟨2165152924146971834474801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5773741131058591558599469 2165152924146971834474801)
              ·
                refine ⟨1623864693110228875856101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2165152924146971834474801 1623864693110228875856101)
                ·
                  refine ⟨304474629958167914223019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1623864693110228875856101 304474629958167914223019)
                  ·
                    rfl

theorem cell21_1334165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 2, 4].length) (baseStart_1334165 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1334165 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1334165 prefixEnd_1334165 := by exact prefixLift 1334165
  have htrace : WordTrace (prefixWord ++ tailWord_1334165) baseStart_1334165 baseEnd_1334165 := by
    simpa [prefixWord, tailWord_1334165, baseEnd_1334165] using wordTrace_append hprefix tailTrace_1334165
  have hstable : (prefixWord ++ tailWord_1334165).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334165).length < 2 ^ (prefixWord ++ tailWord_1334165).sum := by decide
  have hdescent : baseEnd_1334165 < baseStart_1334165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334224 : List Nat := [2, 1, 1, 1, 1, 2, 3, 6, 4]
def baseStart_1334224 : Nat := 118140960795 + 1334224 * 2 ^ 59
def prefixEnd_1334224 : Nat := 4983230072969 + 3 ^ 40 * 1334224 * 2
def baseEnd_1334224 : Nat := 304488094561996922739565

theorem tailTrace_1334224 : CollatzResearch.WordTrace tailWord_1334224 prefixEnd_1334224 304488094561996922739565 := by
  unfold tailWord_1334224
  simp only [CollatzResearch.WordTrace]
  refine ⟨24331573559170895081432863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32442098078894526775243817 24331573559170895081432863)
  ·
    refine ⟨36497360338756342622149295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24331573559170895081432863 36497360338756342622149295)
    ·
      refine ⟨54746040508134513933223943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36497360338756342622149295 54746040508134513933223943)
      ·
        refine ⟨82119060762201770899835915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54746040508134513933223943 82119060762201770899835915)
        ·
          refine ⟨123178591143302656349753873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82119060762201770899835915 123178591143302656349753873)
          ·
            refine ⟨92383943357476992262315405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123178591143302656349753873 92383943357476992262315405)
            ·
              refine ⟨34643978759053872098368277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92383943357476992262315405 34643978759053872098368277)
              ·
                refine ⟨1623936504330650254611013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34643978759053872098368277 1623936504330650254611013)
                ·
                  refine ⟨304488094561996922739565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1623936504330650254611013 304488094561996922739565)
                  ·
                    rfl

theorem cell21_1334224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 6, 4].length) (baseStart_1334224 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1334224 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1334224 prefixEnd_1334224 := by exact prefixLift 1334224
  have htrace : WordTrace (prefixWord ++ tailWord_1334224) baseStart_1334224 baseEnd_1334224 := by
    simpa [prefixWord, tailWord_1334224, baseEnd_1334224] using wordTrace_append hprefix tailTrace_1334224
  have hstable : (prefixWord ++ tailWord_1334224).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334224).length < 2 ^ (prefixWord ++ tailWord_1334224).sum := by decide
  have hdescent : baseEnd_1334224 < baseStart_1334224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334334 : List Nat := [4, 2, 1, 3, 1, 1, 3, 2, 4]
def baseStart_1334334 : Nat := 118140960795 + 1334334 * 2 ^ 59
def prefixEnd_1334334 : Nat := 4983230072969 + 3 ^ 40 * 1334334 * 2
def baseEnd_1334334 : Nat := 304513198060661175906007

theorem tailTrace_1334334 : CollatzResearch.WordTrace tailWord_1334334 prefixEnd_1334334 304513198060661175906007 := by
  unfold tailWord_1334334
  simp only [CollatzResearch.WordTrace]
  refine ⟨6083394893492909868671257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32444772765295519299580037 6083394893492909868671257)
  ·
    refine ⟨4562546170119682401503443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6083394893492909868671257 4562546170119682401503443)
    ·
      refine ⟨6843819255179523602255165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4562546170119682401503443 6843819255179523602255165)
      ·
        refine ⟨2566432220692321350845687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6843819255179523602255165 2566432220692321350845687)
        ·
          refine ⟨3849648331038482026268531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2566432220692321350845687 3849648331038482026268531)
          ·
            refine ⟨5774472496557723039402797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3849648331038482026268531 5774472496557723039402797)
            ·
              refine ⟨2165427186209146139776049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5774472496557723039402797 2165427186209146139776049)
              ·
                refine ⟨1624070389656859604832037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2165427186209146139776049 1624070389656859604832037)
                ·
                  refine ⟨304513198060661175906007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1624070389656859604832037 304513198060661175906007)
                  ·
                    rfl

theorem cell21_1334334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_1334334 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1334334 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1334334 prefixEnd_1334334 := by exact prefixLift 1334334
  have htrace : WordTrace (prefixWord ++ tailWord_1334334) baseStart_1334334 baseEnd_1334334 := by
    simpa [prefixWord, tailWord_1334334, baseEnd_1334334] using wordTrace_append hprefix tailTrace_1334334
  have hstable : (prefixWord ++ tailWord_1334334).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334334).length < 2 ^ (prefixWord ++ tailWord_1334334).sum := by decide
  have hdescent : baseEnd_1334334 < baseStart_1334334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334435 : List Nat := [1, 1, 1, 4, 1, 1, 1, 3, 8]
def baseStart_1334435 : Nat := 118140960795 + 1334435 * 2 ^ 59
def prefixEnd_1334435 : Nat := 4983230072969 + 3 ^ 40 * 1334435 * 2
def baseEnd_1334435 : Nat := 304536247636707444722467

theorem tailTrace_1334435 : CollatzResearch.WordTrace tailWord_1334435 prefixEnd_1334435 304536247636707444722467 := by
  unfold tailWord_1334435
  simp only [CollatzResearch.WordTrace]
  refine ⟨48670842920577373198796759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32447228613718248799197839 48670842920577373198796759)
  ·
    refine ⟨73006264380866059798195139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48670842920577373198796759 73006264380866059798195139)
    ·
      refine ⟨109509396571299089697292709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73006264380866059798195139 109509396571299089697292709)
      ·
        refine ⟨20533011857118579318242383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109509396571299089697292709 20533011857118579318242383)
        ·
          refine ⟨30799517785677868977363575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20533011857118579318242383 30799517785677868977363575)
          ·
            refine ⟨46199276678516803466045363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30799517785677868977363575 46199276678516803466045363)
            ·
              refine ⟨69298915017775205199068045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46199276678516803466045363 69298915017775205199068045)
              ·
                refine ⟨25987093131665701949650517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69298915017775205199068045 25987093131665701949650517)
                ·
                  refine ⟨304536247636707444722467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25987093131665701949650517 304536247636707444722467)
                  ·
                    rfl

theorem cell21_1334435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 8].length) (baseStart_1334435 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1334435 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1334435 prefixEnd_1334435 := by exact prefixLift 1334435
  have htrace : WordTrace (prefixWord ++ tailWord_1334435) baseStart_1334435 baseEnd_1334435 := by
    simpa [prefixWord, tailWord_1334435, baseEnd_1334435] using wordTrace_append hprefix tailTrace_1334435
  have hstable : (prefixWord ++ tailWord_1334435).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334435).length < 2 ^ (prefixWord ++ tailWord_1334435).sum := by decide
  have hdescent : baseEnd_1334435 < baseStart_1334435 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334503 : List Nat := [1, 1, 5, 3, 3, 1, 1, 2, 4]
def baseStart_1334503 : Nat := 118140960795 + 1334503 * 2 ^ 59
def prefixEnd_1334503 : Nat := 4983230072969 + 3 ^ 40 * 1334503 * 2
def baseEnd_1334503 : Nat := 304551766163154437588995

theorem tailTrace_1334503 : CollatzResearch.WordTrace tailWord_1334503 prefixEnd_1334503 304551766163154437588995 := by
  unfold tailWord_1334503
  simp only [CollatzResearch.WordTrace]
  refine ⟨48673323084331020812272163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32448882056220680541514775 48673323084331020812272163)
  ·
    refine ⟨73009984626496531218408245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48673323084331020812272163 73009984626496531218408245)
    ·
      refine ⟨6844686058734049801725773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 73009984626496531218408245 6844686058734049801725773)
      ·
        refine ⟨2566757272025268675647165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6844686058734049801725773 2566757272025268675647165)
        ·
          refine ⟨962533977009475753367687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2566757272025268675647165 962533977009475753367687)
          ·
            refine ⟨1443800965514213630051531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 962533977009475753367687 1443800965514213630051531)
            ·
              refine ⟨2165701448271320445077297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1443800965514213630051531 2165701448271320445077297)
              ·
                refine ⟨1624276086203490333807973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2165701448271320445077297 1624276086203490333807973)
                ·
                  refine ⟨304551766163154437588995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1624276086203490333807973 304551766163154437588995)
                  ·
                    rfl

theorem cell21_1334503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 2, 4].length) (baseStart_1334503 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1334503 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1334503 prefixEnd_1334503 := by exact prefixLift 1334503
  have htrace : WordTrace (prefixWord ++ tailWord_1334503) baseStart_1334503 baseEnd_1334503 := by
    simpa [prefixWord, tailWord_1334503, baseEnd_1334503] using wordTrace_append hprefix tailTrace_1334503
  have hstable : (prefixWord ++ tailWord_1334503).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334503).length < 2 ^ (prefixWord ++ tailWord_1334503).sum := by decide
  have hdescent : baseEnd_1334503 < baseStart_1334503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334559 : List Nat := [1, 1, 2, 4, 4, 2, 7]
def baseStart_1334559 : Nat := 118140960795 + 1334559 * 2 ^ 59
def prefixEnd_1334559 : Nat := 4983230072969 + 3 ^ 40 * 1334559 * 2
def baseEnd_1334559 : Nat := 33840505125123420517283

theorem tailTrace_1334559 : CollatzResearch.WordTrace tailWord_1334559 prefixEnd_1334559 33840505125123420517283 := by
  unfold tailWord_1334559
  simp only [CollatzResearch.WordTrace]
  refine ⟨48675365572128142376310731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32450243714752094917540487 48675365572128142376310731)
  ·
    refine ⟨73013048358192213564466097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48675365572128142376310731 73013048358192213564466097)
    ·
      refine ⟨54759786268644160173349573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73013048358192213564466097 54759786268644160173349573)
      ·
        refine ⟨10267459925370780032503045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54759786268644160173349573 10267459925370780032503045)
        ·
          refine ⟨1925148736007021256094321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10267459925370780032503045 1925148736007021256094321)
          ·
            refine ⟨1443861552005265942070741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1925148736007021256094321 1443861552005265942070741)
            ·
              refine ⟨33840505125123420517283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1443861552005265942070741 33840505125123420517283)
              ·
                rfl

theorem cell21_1334559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 7].length) (baseStart_1334559 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1334559 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1334559 prefixEnd_1334559 := by exact prefixLift 1334559
  have htrace : WordTrace (prefixWord ++ tailWord_1334559) baseStart_1334559 baseEnd_1334559 := by
    simpa [prefixWord, tailWord_1334559, baseEnd_1334559] using wordTrace_append hprefix tailTrace_1334559
  have hstable : (prefixWord ++ tailWord_1334559).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334559).length < 2 ^ (prefixWord ++ tailWord_1334559).sum := by decide
  have hdescent : baseEnd_1334559 < baseStart_1334559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334624 : List Nat := [2, 1, 1, 3, 4, 3, 2, 2, 3]
def baseStart_1334624 : Nat := 118140960795 + 1334624 * 2 ^ 59
def prefixEnd_1334624 : Nat := 4983230072969 + 3 ^ 40 * 1334624 * 2
def baseEnd_1334624 : Nat := 304579380011685116072081

theorem tailTrace_1334624 : CollatzResearch.WordTrace tailWord_1334624 prefixEnd_1334624 304579380011685116072081 := by
  unfold tailWord_1334624
  simp only [CollatzResearch.WordTrace]
  refine ⟨24338868158446329238713463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32451824211261772318284617 24338868158446329238713463)
  ·
    refine ⟨36508302237669493858070195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24338868158446329238713463 36508302237669493858070195)
    ·
      refine ⟨54762453356504240787105293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36508302237669493858070195 54762453356504240787105293)
      ·
        refine ⟨20535920008689090295164485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54762453356504240787105293 20535920008689090295164485)
        ·
          refine ⟨3850485001629204430343341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20535920008689090295164485 3850485001629204430343341)
          ·
            refine ⟨1443931875610951661378753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3850485001629204430343341 1443931875610951661378753)
            ·
              refine ⟨1082948906708213746034065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1443931875610951661378753 1082948906708213746034065)
              ·
                refine ⟨812211680031160309525549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1082948906708213746034065 812211680031160309525549)
                ·
                  refine ⟨304579380011685116072081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 812211680031160309525549 304579380011685116072081)
                  ·
                    rfl

theorem cell21_1334624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 2, 2, 3].length) (baseStart_1334624 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1334624 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1334624 prefixEnd_1334624 := by exact prefixLift 1334624
  have htrace : WordTrace (prefixWord ++ tailWord_1334624) baseStart_1334624 baseEnd_1334624 := by
    simpa [prefixWord, tailWord_1334624, baseEnd_1334624] using wordTrace_append hprefix tailTrace_1334624
  have hstable : (prefixWord ++ tailWord_1334624).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334624).length < 2 ^ (prefixWord ++ tailWord_1334624).sum := by decide
  have hdescent : baseEnd_1334624 < baseStart_1334624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334922 : List Nat := [3, 1, 2, 3, 2, 1, 1, 8]
def baseStart_1334922 : Nat := 118140960795 + 1334922 * 2 ^ 59
def prefixEnd_1334922 : Nat := 4983230072969 + 3 ^ 40 * 1334922 * 2
def baseEnd_1334922 : Nat := 101549129223900940034935

theorem tailTrace_1334922 : CollatzResearch.WordTrace tailWord_1334922 prefixEnd_1334922 101549129223900940034935 := by
  unfold tailWord_1334922
  simp only [CollatzResearch.WordTrace]
  refine ⟨12172151317453263842943755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32459070179875370247850013 12172151317453263842943755)
  ·
    refine ⟨18258226976179895764415633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12172151317453263842943755 18258226976179895764415633)
    ·
      refine ⟨13693670232134921823311725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18258226976179895764415633 13693670232134921823311725)
      ·
        refine ⟨5135126337050595683741897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13693670232134921823311725 5135126337050595683741897)
        ·
          refine ⟨3851344752787946762806423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5135126337050595683741897 3851344752787946762806423)
          ·
            refine ⟨5777017129181920144209635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3851344752787946762806423 5777017129181920144209635)
            ·
              refine ⟨8665525693772880216314453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5777017129181920144209635 8665525693772880216314453)
              ·
                refine ⟨101549129223900940034935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8665525693772880216314453 101549129223900940034935)
                ·
                  rfl

theorem cell21_1334922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 8].length) (baseStart_1334922 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1334922 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1334922 prefixEnd_1334922 := by exact prefixLift 1334922
  have htrace : WordTrace (prefixWord ++ tailWord_1334922) baseStart_1334922 baseEnd_1334922 := by
    simpa [prefixWord, tailWord_1334922, baseEnd_1334922] using wordTrace_append hprefix tailTrace_1334922
  have hstable : (prefixWord ++ tailWord_1334922).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334922).length < 2 ^ (prefixWord ++ tailWord_1334922).sum := by decide
  have hdescent : baseEnd_1334922 < baseStart_1334922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1334970 : List Nat := [3, 1, 1, 1, 2, 5, 1, 4, 3]
def baseStart_1334970 : Nat := 118140960795 + 1334970 * 2 ^ 59
def prefixEnd_1334970 : Nat := 4983230072969 + 3 ^ 40 * 1334970 * 2
def baseEnd_1334970 : Nat := 304658341925665403304707

theorem tailTrace_1334970 : CollatzResearch.WordTrace tailWord_1334970 prefixEnd_1334970 304658341925665403304707 := by
  unfold tailWord_1334970
  simp only [CollatzResearch.WordTrace]
  refine ⟨12172588993409789892380591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32460237315759439713014909 12172588993409789892380591)
  ·
    refine ⟨18258883490114684838570887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12172588993409789892380591 18258883490114684838570887)
    ·
      refine ⟨27388325235172027257856331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18258883490114684838570887 27388325235172027257856331)
      ·
        refine ⟨41082487852758040886784497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27388325235172027257856331 41082487852758040886784497)
        ·
          refine ⟨30811865889568530665088373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41082487852758040886784497 30811865889568530665088373)
          ·
            refine ⟨2888612427147049749852035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30811865889568530665088373 2888612427147049749852035)
            ·
              refine ⟨4332918640720574624778053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2888612427147049749852035 4332918640720574624778053)
              ·
                refine ⟨812422245135107742145885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4332918640720574624778053 812422245135107742145885)
                ·
                  refine ⟨304658341925665403304707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 812422245135107742145885 304658341925665403304707)
                  ·
                    rfl

theorem cell21_1334970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 4, 3].length) (baseStart_1334970 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1334970 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1334970 prefixEnd_1334970 := by exact prefixLift 1334970
  have htrace : WordTrace (prefixWord ++ tailWord_1334970) baseStart_1334970 baseEnd_1334970 := by
    simpa [prefixWord, tailWord_1334970, baseEnd_1334970] using wordTrace_append hprefix tailTrace_1334970
  have hstable : (prefixWord ++ tailWord_1334970).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1334970).length < 2 ^ (prefixWord ++ tailWord_1334970).sum := by decide
  have hdescent : baseEnd_1334970 < baseStart_1334970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1334970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335004 : List Nat := [2, 2, 5, 1, 2, 1, 2, 3, 3]
def baseStart_1335004 : Nat := 118140960795 + 1335004 * 2 ^ 59
def prefixEnd_1335004 : Nat := 4983230072969 + 3 ^ 40 * 1335004 * 2
def baseEnd_1335004 : Nat := 304666101188888899737971

theorem tailTrace_1335004 : CollatzResearch.WordTrace tailWord_1335004 prefixEnd_1335004 304666101188888899737971 := by
  unfold tailWord_1335004
  simp only [CollatzResearch.WordTrace]
  refine ⟨24345798027757991688130033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32461064037010655584173377 24345798027757991688130033)
  ·
    refine ⟨18259348520818493766097525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24345798027757991688130033 18259348520818493766097525)
    ·
      refine ⟨1711813923826733790571643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18259348520818493766097525 1711813923826733790571643)
      ·
        refine ⟨2567720885740100685857465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1711813923826733790571643 2567720885740100685857465)
        ·
          refine ⟨1925790664305075514393099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2567720885740100685857465 1925790664305075514393099)
          ·
            refine ⟨2888685996457613271589649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1925790664305075514393099 2888685996457613271589649)
            ·
              refine ⟨2166514497343209953692237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2888685996457613271589649 2166514497343209953692237)
              ·
                refine ⟨812442936503703732634589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2166514497343209953692237 812442936503703732634589)
                ·
                  refine ⟨304666101188888899737971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 812442936503703732634589 304666101188888899737971)
                  ·
                    rfl

theorem cell21_1335004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 3, 3].length) (baseStart_1335004 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1335004 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1335004 prefixEnd_1335004 := by exact prefixLift 1335004
  have htrace : WordTrace (prefixWord ++ tailWord_1335004) baseStart_1335004 baseEnd_1335004 := by
    simpa [prefixWord, tailWord_1335004, baseEnd_1335004] using wordTrace_append hprefix tailTrace_1335004
  have hstable : (prefixWord ++ tailWord_1335004).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335004).length < 2 ^ (prefixWord ++ tailWord_1335004).sum := by decide
  have hdescent : baseEnd_1335004 < baseStart_1335004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335012 : List Nat := [2, 3, 1, 1, 1, 3, 1, 2, 7]
def baseStart_1335012 : Nat := 118140960795 + 1335012 * 2 ^ 59
def prefixEnd_1335012 : Nat := 4983230072969 + 3 ^ 40 * 1335012 * 2
def baseEnd_1335012 : Nat := 304667926897882663604621

theorem tailTrace_1335012 : CollatzResearch.WordTrace tailWord_1335012 prefixEnd_1335012 304667926897882663604621 := by
  unfold tailWord_1335012
  simp only [CollatzResearch.WordTrace]
  refine ⟨24345943919743500371275645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32461258559658000495034193 24345943919743500371275645)
  ·
    refine ⟨9129728969903812639228367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24345943919743500371275645 9129728969903812639228367)
    ·
      refine ⟨13694593454855718958842551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9129728969903812639228367 13694593454855718958842551)
      ·
        refine ⟨20541890182283578438263827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13694593454855718958842551 20541890182283578438263827)
        ·
          refine ⟨30812835273425367657395741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20541890182283578438263827 30812835273425367657395741)
          ·
            refine ⟨11554813227534512871523403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30812835273425367657395741 11554813227534512871523403)
            ·
              refine ⟨17332219841301769307285105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11554813227534512871523403 17332219841301769307285105)
              ·
                refine ⟨12999164880976326980463829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17332219841301769307285105 12999164880976326980463829)
                ·
                  refine ⟨304667926897882663604621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12999164880976326980463829 304667926897882663604621)
                  ·
                    rfl

theorem cell21_1335012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 7].length) (baseStart_1335012 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1335012 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1335012 prefixEnd_1335012 := by exact prefixLift 1335012
  have htrace : WordTrace (prefixWord ++ tailWord_1335012) baseStart_1335012 baseEnd_1335012 := by
    simpa [prefixWord, tailWord_1335012, baseEnd_1335012] using wordTrace_append hprefix tailTrace_1335012
  have hstable : (prefixWord ++ tailWord_1335012).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335012).length < 2 ^ (prefixWord ++ tailWord_1335012).sum := by decide
  have hdescent : baseEnd_1335012 < baseStart_1335012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335015 : List Nat := [1, 1, 5, 4, 1, 1, 8]
def baseStart_1335015 : Nat := 118140960795 + 1335015 * 2 ^ 59
def prefixEnd_1335015 : Nat := 4983230072969 + 3 ^ 40 * 1335015 * 2
def baseEnd_1335015 : Nat := 33852067948750591672735

theorem tailTrace_1335015 : CollatzResearch.WordTrace tailWord_1335015 prefixEnd_1335015 33852067948750591672735 := by
  unfold tailWord_1335015
  simp only [CollatzResearch.WordTrace]
  refine ⟨48691997258476132254910499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32461331505650754836606999 48691997258476132254910499)
  ·
    refine ⟨73037995887714198382365749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48691997258476132254910499 73037995887714198382365749)
    ·
      refine ⟨6847312114473206098346789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 73037995887714198382365749 6847312114473206098346789)
      ·
        refine ⟨1283871021463726143440023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6847312114473206098346789 1283871021463726143440023)
        ·
          refine ⟨1925806532195589215160035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1283871021463726143440023 1925806532195589215160035)
          ·
            refine ⟨2888709798293383822740053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1925806532195589215160035 2888709798293383822740053)
            ·
              refine ⟨33852067948750591672735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2888709798293383822740053 33852067948750591672735)
              ·
                rfl

theorem cell21_1335015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 8].length) (baseStart_1335015 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1335015 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1335015 prefixEnd_1335015 := by exact prefixLift 1335015
  have htrace : WordTrace (prefixWord ++ tailWord_1335015) baseStart_1335015 baseEnd_1335015 := by
    simpa [prefixWord, tailWord_1335015, baseEnd_1335015] using wordTrace_append hprefix tailTrace_1335015
  have hstable : (prefixWord ++ tailWord_1335015).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335015).length < 2 ^ (prefixWord ++ tailWord_1335015).sum := by decide
  have hdescent : baseEnd_1335015 < baseStart_1335015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335043 : List Nat := [1, 1, 1, 3, 2, 2, 2, 5, 4]
def baseStart_1335043 : Nat := 118140960795 + 1335043 * 2 ^ 59
def prefixEnd_1335043 : Nat := 4983230072969 + 3 ^ 40 * 1335043 * 2
def baseEnd_1335043 : Nat := 304675001520233498587891

theorem tailTrace_1335043 : CollatzResearch.WordTrace tailWord_1335043 prefixEnd_1335043 304675001520233498587891 := by
  unfold tailWord_1335043
  simp only [CollatzResearch.WordTrace]
  refine ⟨48693018502374693036929783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32462012334916462024619855 48693018502374693036929783)
  ·
    refine ⟨73039527753562039555394675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48693018502374693036929783 73039527753562039555394675)
    ·
      refine ⟨109559291630343059333092013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73039527753562039555394675 109559291630343059333092013)
      ·
        refine ⟨41084734361378647249909505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109559291630343059333092013 41084734361378647249909505)
        ·
          refine ⟨30813550771033985437432129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41084734361378647249909505 30813550771033985437432129)
          ·
            refine ⟨23110163078275489078074097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30813550771033985437432129 23110163078275489078074097)
            ·
              refine ⟨17332622308706616808555573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23110163078275489078074097 17332622308706616808555573)
              ·
                refine ⟨1624933341441245325802085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17332622308706616808555573 1624933341441245325802085)
                ·
                  refine ⟨304675001520233498587891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1624933341441245325802085 304675001520233498587891)
                  ·
                    rfl

theorem cell21_1335043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 5, 4].length) (baseStart_1335043 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1335043 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1335043 prefixEnd_1335043 := by exact prefixLift 1335043
  have htrace : WordTrace (prefixWord ++ tailWord_1335043) baseStart_1335043 baseEnd_1335043 := by
    simpa [prefixWord, tailWord_1335043, baseEnd_1335043] using wordTrace_append hprefix tailTrace_1335043
  have hstable : (prefixWord ++ tailWord_1335043).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335043).length < 2 ^ (prefixWord ++ tailWord_1335043).sum := by decide
  have hdescent : baseEnd_1335043 < baseStart_1335043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335063 : List Nat := [1, 1, 3, 4, 2, 3, 1, 3, 3]
def baseStart_1335063 : Nat := 118140960795 + 1335063 * 2 ^ 59
def prefixEnd_1335063 : Nat := 4983230072969 + 3 ^ 40 * 1335063 * 2
def baseEnd_1335063 : Nat := 304679565792717908254517

theorem tailTrace_1335063 : CollatzResearch.WordTrace tailWord_1335063 prefixEnd_1335063 304679565792717908254517 := by
  unfold tailWord_1335063
  simp only [CollatzResearch.WordTrace]
  refine ⟨48693747962302236452657843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32462498641534824301771895 48693747962302236452657843)
  ·
    refine ⟨73040621943453354678986765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48693747962302236452657843 73040621943453354678986765)
    ·
      refine ⟨27390233228795008004620037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73040621943453354678986765 27390233228795008004620037)
      ·
        refine ⟨5135668730399064000866257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27390233228795008004620037 5135668730399064000866257)
        ·
          refine ⟨3851751547799298000649693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5135668730399064000866257 3851751547799298000649693)
          ·
            refine ⟨1444406830424736750243635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3851751547799298000649693 1444406830424736750243635)
            ·
              refine ⟨2166610245637105125365453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1444406830424736750243635 2166610245637105125365453)
              ·
                refine ⟨812478842113914422012045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2166610245637105125365453 812478842113914422012045)
                ·
                  refine ⟨304679565792717908254517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 812478842113914422012045 304679565792717908254517)
                  ·
                    rfl

theorem cell21_1335063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 3, 3].length) (baseStart_1335063 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1335063 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1335063 prefixEnd_1335063 := by exact prefixLift 1335063
  have htrace : WordTrace (prefixWord ++ tailWord_1335063) baseStart_1335063 baseEnd_1335063 := by
    simpa [prefixWord, tailWord_1335063, baseEnd_1335063] using wordTrace_append hprefix tailTrace_1335063
  have hstable : (prefixWord ++ tailWord_1335063).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335063).length < 2 ^ (prefixWord ++ tailWord_1335063).sum := by decide
  have hdescent : baseEnd_1335063 < baseStart_1335063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335094 : List Nat := [5, 1, 2, 2, 1, 1, 4, 1, 4]
def baseStart_1335094 : Nat := 118140960795 + 1335094 * 2 ^ 59
def prefixEnd_1335094 : Nat := 4983230072969 + 3 ^ 40 * 1335094 * 2
def baseEnd_1335094 : Nat := 304686640415068743237787

theorem tailTrace_1335094 : CollatzResearch.WordTrace tailWord_1335094 prefixEnd_1335094 304686640415068743237787 := by
  unfold tailWord_1335094
  simp only [CollatzResearch.WordTrace]
  refine ⟨3043429914074370546689771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32463252416793285831357557 3043429914074370546689771)
  ·
    refine ⟨4565144871111555820034657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3043429914074370546689771 4565144871111555820034657)
    ·
      refine ⟨3423858653333666865025993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4565144871111555820034657 3423858653333666865025993)
      ·
        refine ⟨2567893990000250148769495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3423858653333666865025993 2567893990000250148769495)
        ·
          refine ⟨3851840985000375223154243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2567893990000250148769495 3851840985000375223154243)
          ·
            refine ⟨5777761477500562834731365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3851840985000375223154243 5777761477500562834731365)
            ·
              refine ⟨1083330277031355531512131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5777761477500562834731365 1083330277031355531512131)
              ·
                refine ⟨1624995415547033297268197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1083330277031355531512131 1624995415547033297268197)
                ·
                  refine ⟨304686640415068743237787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1624995415547033297268197 304686640415068743237787)
                  ·
                    rfl

theorem cell21_1335094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_1335094 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1335094 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1335094 prefixEnd_1335094 := by exact prefixLift 1335094
  have htrace : WordTrace (prefixWord ++ tailWord_1335094) baseStart_1335094 baseEnd_1335094 := by
    simpa [prefixWord, tailWord_1335094, baseEnd_1335094] using wordTrace_append hprefix tailTrace_1335094
  have hstable : (prefixWord ++ tailWord_1335094).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335094).length < 2 ^ (prefixWord ++ tailWord_1335094).sum := by decide
  have hdescent : baseEnd_1335094 < baseStart_1335094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335136 : List Nat := [2, 1, 1, 3, 3, 3, 2, 2, 4]
def baseStart_1335136 : Nat := 118140960795 + 1335136 * 2 ^ 59
def prefixEnd_1335136 : Nat := 4983230072969 + 3 ^ 40 * 1335136 * 2
def baseEnd_1335136 : Nat := 304696225387286003537701

theorem tailTrace_1335136 : CollatzResearch.WordTrace tailWord_1335136 prefixEnd_1335136 304696225387286003537701 := by
  unfold tailWord_1335136
  simp only [CollatzResearch.WordTrace]
  refine ⟨24348205245518884960032631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32464273660691846613376841 24348205245518884960032631)
  ·
    refine ⟨36522307868278327440048947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24348205245518884960032631 36522307868278327440048947)
    ·
      refine ⟨54783461802417491160073421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36522307868278327440048947 54783461802417491160073421)
      ·
        refine ⟨20543798175906559185027533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54783461802417491160073421 20543798175906559185027533)
        ·
          refine ⟨7703924315964959694385325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20543798175906559185027533 7703924315964959694385325)
          ·
            refine ⟨2888971618486859885394497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7703924315964959694385325 2888971618486859885394497)
            ·
              refine ⟨2166728713865144914045873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2888971618486859885394497 2166728713865144914045873)
              ·
                refine ⟨1625046535398858685534405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2166728713865144914045873 1625046535398858685534405)
                ·
                  refine ⟨304696225387286003537701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1625046535398858685534405 304696225387286003537701)
                  ·
                    rfl

theorem cell21_1335136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 2, 4].length) (baseStart_1335136 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1335136 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1335136 prefixEnd_1335136 := by exact prefixLift 1335136
  have htrace : WordTrace (prefixWord ++ tailWord_1335136) baseStart_1335136 baseEnd_1335136 := by
    simpa [prefixWord, tailWord_1335136, baseEnd_1335136] using wordTrace_append hprefix tailTrace_1335136
  have hstable : (prefixWord ++ tailWord_1335136).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335136).length < 2 ^ (prefixWord ++ tailWord_1335136).sum := by decide
  have hdescent : baseEnd_1335136 < baseStart_1335136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335319 : List Nat := [1, 1, 3, 5, 2, 2, 1, 6]
def baseStart_1335319 : Nat := 118140960795 + 1335319 * 2 ^ 59
def prefixEnd_1335319 : Nat := 4983230072969 + 3 ^ 40 * 1335319 * 2
def baseEnd_1335319 : Nat := 101579329493506117329109

theorem tailTrace_1335319 : CollatzResearch.WordTrace tailWord_1335319 prefixEnd_1335319 101579329493506117329109 := by
  unfold tailWord_1335319
  simp only [CollatzResearch.WordTrace]
  refine ⟨48703085049374792173977011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32468723366249861449318007 48703085049374792173977011)
  ·
    refine ⟨73054627574062188260965517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48703085049374792173977011 73054627574062188260965517)
    ·
      refine ⟨27395485340273320597862069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73054627574062188260965517 27395485340273320597862069)
      ·
        refine ⟨2568326750650623806049569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27395485340273320597862069 2568326750650623806049569)
        ·
          refine ⟨1926245062987967854537177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2568326750650623806049569 1926245062987967854537177)
          ·
            refine ⟨1444683797240975890902883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1926245062987967854537177 1444683797240975890902883)
            ·
              refine ⟨2167025695861463836354325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1444683797240975890902883 2167025695861463836354325)
              ·
                refine ⟨101579329493506117329109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2167025695861463836354325 101579329493506117329109)
                ·
                  rfl

theorem cell21_1335319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 6].length) (baseStart_1335319 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1335319 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1335319 prefixEnd_1335319 := by exact prefixLift 1335319
  have htrace : WordTrace (prefixWord ++ tailWord_1335319) baseStart_1335319 baseEnd_1335319 := by
    simpa [prefixWord, tailWord_1335319, baseEnd_1335319] using wordTrace_append hprefix tailTrace_1335319
  have hstable : (prefixWord ++ tailWord_1335319).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335319).length < 2 ^ (prefixWord ++ tailWord_1335319).sum := by decide
  have hdescent : baseEnd_1335319 < baseStart_1335319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335336 : List Nat := [2, 1, 5, 3, 1, 1, 3, 5]
def baseStart_1335336 : Nat := 118140960795 + 1335336 * 2 ^ 59
def prefixEnd_1335336 : Nat := 4983230072969 + 3 ^ 40 * 1335336 * 2
def baseEnd_1335336 : Nat := 101580622704043366734653

theorem tailTrace_1335336 : CollatzResearch.WordTrace tailWord_1335336 prefixEnd_1335336 101580622704043366734653 := by
  unfold tailWord_1335336
  simp only [CollatzResearch.WordTrace]
  refine ⟨24351852545156602038672931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32469136726875469384897241 24351852545156602038672931)
  ·
    refine ⟨36527778817734903058009397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24351852545156602038672931 36527778817734903058009397)
    ·
      refine ⟨3424479264162647161688381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36527778817734903058009397 3424479264162647161688381)
      ·
        refine ⟨1284179724060992685633143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3424479264162647161688381 1284179724060992685633143)
        ·
          refine ⟨1926269586091489028449715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1284179724060992685633143 1926269586091489028449715)
          ·
            refine ⟨2889404379137233542674573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1926269586091489028449715 2889404379137233542674573)
            ·
              refine ⟨1083526642176462578502965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2889404379137233542674573 1083526642176462578502965)
              ·
                refine ⟨101580622704043366734653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1083526642176462578502965 101580622704043366734653)
                ·
                  rfl

theorem cell21_1335336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 3, 5].length) (baseStart_1335336 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1335336 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1335336 prefixEnd_1335336 := by exact prefixLift 1335336
  have htrace : WordTrace (prefixWord ++ tailWord_1335336) baseStart_1335336 baseEnd_1335336 := by
    simpa [prefixWord, tailWord_1335336, baseEnd_1335336] using wordTrace_append hprefix tailTrace_1335336
  have hstable : (prefixWord ++ tailWord_1335336).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335336).length < 2 ^ (prefixWord ++ tailWord_1335336).sum := by decide
  have hdescent : baseEnd_1335336 < baseStart_1335336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335375 : List Nat := [1, 1, 2, 1, 1, 2, 2, 2, 9]
def baseStart_1335375 : Nat := 118140960795 + 1335375 * 2 ^ 59
def prefixEnd_1335375 : Nat := 4983230072969 + 3 ^ 40 * 1335375 * 2
def baseEnd_1335375 : Nat := 304750768443474699053879

theorem tailTrace_1335375 : CollatzResearch.WordTrace tailWord_1335375 prefixEnd_1335375 304750768443474699053879 := by
  unfold tailWord_1335375
  simp only [CollatzResearch.WordTrace]
  refine ⟨48705127537171913738015579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32470085024781275825343719 48705127537171913738015579)
  ·
    refine ⟨73057691305757870607023369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48705127537171913738015579 73057691305757870607023369)
    ·
      refine ⟨54793268479318402955267527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73057691305757870607023369 54793268479318402955267527)
      ·
        refine ⟨82189902718977604432901291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54793268479318402955267527 82189902718977604432901291)
        ·
          refine ⟨123284854078466406649351937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82189902718977604432901291 123284854078466406649351937)
          ·
            refine ⟨92463640558849804987013953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123284854078466406649351937 92463640558849804987013953)
            ·
              refine ⟨69347730419137353740260465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92463640558849804987013953 69347730419137353740260465)
              ·
                refine ⟨52010797814353015305195349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69347730419137353740260465 52010797814353015305195349)
                ·
                  refine ⟨304750768443474699053879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 52010797814353015305195349 304750768443474699053879)
                  ·
                    rfl

theorem cell21_1335375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 9].length) (baseStart_1335375 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1335375 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1335375 prefixEnd_1335375 := by exact prefixLift 1335375
  have htrace : WordTrace (prefixWord ++ tailWord_1335375) baseStart_1335375 baseEnd_1335375 := by
    simpa [prefixWord, tailWord_1335375, baseEnd_1335375] using wordTrace_append hprefix tailTrace_1335375
  have hstable : (prefixWord ++ tailWord_1335375).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335375).length < 2 ^ (prefixWord ++ tailWord_1335375).sum := by decide
  have hdescent : baseEnd_1335375 < baseStart_1335375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335392 : List Nat := [2, 1, 1, 3, 2, 3, 2, 2, 5]
def baseStart_1335392 : Nat := 118140960795 + 1335392 * 2 ^ 59
def prefixEnd_1335392 : Nat := 4983230072969 + 3 ^ 40 * 1335392 * 2
def baseEnd_1335392 : Nat := 304754648075086447270511

theorem tailTrace_1335392 : CollatzResearch.WordTrace tailWord_1335392 prefixEnd_1335392 304754648075086447270511 := by
  unfold tailWord_1335392
  simp only [CollatzResearch.WordTrace]
  refine ⟨24352873789055162820692215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32470498385406883760922953 24352873789055162820692215)
  ·
    refine ⟨36529310683582744231038323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24352873789055162820692215 36529310683582744231038323)
    ·
      refine ⟨54793966025374116346557485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36529310683582744231038323 54793966025374116346557485)
      ·
        refine ⟨20547737259515293629959057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54793966025374116346557485 20547737259515293629959057)
        ·
          refine ⟨15410802944636470222469293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20547737259515293629959057 15410802944636470222469293)
          ·
            refine ⟨5779051104238676333425985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15410802944636470222469293 5779051104238676333425985)
            ·
              refine ⟨4334288328179007250069489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5779051104238676333425985 4334288328179007250069489)
              ·
                refine ⟨3250716246134255437552117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4334288328179007250069489 3250716246134255437552117)
                ·
                  refine ⟨304754648075086447270511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3250716246134255437552117 304754648075086447270511)
                  ·
                    rfl

theorem cell21_1335392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 2, 5].length) (baseStart_1335392 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1335392 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1335392 prefixEnd_1335392 := by exact prefixLift 1335392
  have htrace : WordTrace (prefixWord ++ tailWord_1335392) baseStart_1335392 baseEnd_1335392 := by
    simpa [prefixWord, tailWord_1335392, baseEnd_1335392] using wordTrace_append hprefix tailTrace_1335392
  have hstable : (prefixWord ++ tailWord_1335392).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335392).length < 2 ^ (prefixWord ++ tailWord_1335392).sum := by decide
  have hdescent : baseEnd_1335392 < baseStart_1335392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335477 : List Nat := [1, 3, 3, 4, 2, 1, 2, 2, 3]
def baseStart_1335477 : Nat := 118140960795 + 1335477 * 2 ^ 59
def prefixEnd_1335477 : Nat := 4983230072969 + 3 ^ 40 * 1335477 * 2
def baseEnd_1335477 : Nat := 304774046233145188353671

theorem tailTrace_1335477 : CollatzResearch.WordTrace tailWord_1335477 prefixEnd_1335477 304774046233145188353671 := by
  unfold tailWord_1335477
  simp only [CollatzResearch.WordTrace]
  refine ⟨48708847782802385158228685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32472565188534923438819123 48708847782802385158228685)
  ·
    refine ⟨18265817918550894434335757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48708847782802385158228685 18265817918550894434335757)
    ·
      refine ⟨6849681719456585412875909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18265817918550894434335757 6849681719456585412875909)
      ·
        refine ⟨1284315322398109764914233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6849681719456585412875909 1284315322398109764914233)
        ·
          refine ⟨963236491798582323685675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1284315322398109764914233 963236491798582323685675)
          ·
            refine ⟨1444854737697873485528513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 963236491798582323685675 1444854737697873485528513)
            ·
              refine ⟨1083641053273405114146385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1444854737697873485528513 1083641053273405114146385)
              ·
                refine ⟨812730789955053835609789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1083641053273405114146385 812730789955053835609789)
                ·
                  refine ⟨304774046233145188353671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 812730789955053835609789 304774046233145188353671)
                  ·
                    rfl

theorem cell21_1335477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 2, 2, 3].length) (baseStart_1335477 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1335477 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1335477 prefixEnd_1335477 := by exact prefixLift 1335477
  have htrace : WordTrace (prefixWord ++ tailWord_1335477) baseStart_1335477 baseEnd_1335477 := by
    simpa [prefixWord, tailWord_1335477, baseEnd_1335477] using wordTrace_append hprefix tailTrace_1335477
  have hstable : (prefixWord ++ tailWord_1335477).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335477).length < 2 ^ (prefixWord ++ tailWord_1335477).sum := by decide
  have hdescent : baseEnd_1335477 < baseStart_1335477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335482 : List Nat := [3, 1, 1, 1, 2, 2, 2, 3, 6]
def baseStart_1335482 : Nat := 118140960795 + 1335482 * 2 ^ 59
def prefixEnd_1335482 : Nat := 4983230072969 + 3 ^ 40 * 1335482 * 2
def baseEnd_1335482 : Nat := 304775187301266290770327

theorem tailTrace_1335482 : CollatzResearch.WordTrace tailWord_1335482 prefixEnd_1335482 304775187301266290770327 := by
  unfold tailWord_1335482
  simp only [CollatzResearch.WordTrace]
  refine ⟨12177257536946067753040175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32472686765189514008107133 12177257536946067753040175)
  ·
    refine ⟨18265886305419101629560263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12177257536946067753040175 18265886305419101629560263)
    ·
      refine ⟨27398829458128652444340395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18265886305419101629560263 27398829458128652444340395)
      ·
        refine ⟨41098244187192978666510593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27398829458128652444340395 41098244187192978666510593)
        ·
          refine ⟨30823683140394733999882945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41098244187192978666510593 30823683140394733999882945)
          ·
            refine ⟨23117762355296050499912209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30823683140394733999882945 23117762355296050499912209)
            ·
              refine ⟨17338321766472037874934157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23117762355296050499912209 17338321766472037874934157)
              ·
                refine ⟨6501870662427014203100309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17338321766472037874934157 6501870662427014203100309)
                ·
                  refine ⟨304775187301266290770327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6501870662427014203100309 304775187301266290770327)
                  ·
                    rfl

theorem cell21_1335482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3, 6].length) (baseStart_1335482 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1335482 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1335482 prefixEnd_1335482 := by exact prefixLift 1335482
  have htrace : WordTrace (prefixWord ++ tailWord_1335482) baseStart_1335482 baseEnd_1335482 := by
    simpa [prefixWord, tailWord_1335482, baseEnd_1335482] using wordTrace_append hprefix tailTrace_1335482
  have hstable : (prefixWord ++ tailWord_1335482).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335482).length < 2 ^ (prefixWord ++ tailWord_1335482).sum := by decide
  have hdescent : baseEnd_1335482 < baseStart_1335482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335533 : List Nat := [1, 5, 1, 2, 3, 2, 1, 2, 4]
def baseStart_1335533 : Nat := 118140960795 + 1335533 * 2 ^ 59
def prefixEnd_1335533 : Nat := 4983230072969 + 3 ^ 40 * 1335533 * 2
def baseEnd_1335533 : Nat := 304786826196101535420223

theorem tailTrace_1335533 : CollatzResearch.WordTrace tailWord_1335533 prefixEnd_1335533 304786826196101535420223 := by
  unfold tailWord_1335533
  simp only [CollatzResearch.WordTrace]
  refine ⟨48710890270599506722267253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32473926847066337814844835 48710890270599506722267253)
  ·
    refine ⟨4566645962868703755212555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48710890270599506722267253 4566645962868703755212555)
    ·
      refine ⟨6849968944303055632818833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4566645962868703755212555 6849968944303055632818833)
      ·
        refine ⟨5137476708227291724614125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6849968944303055632818833 5137476708227291724614125)
        ·
          refine ⟨1926553765585234396730297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5137476708227291724614125 1926553765585234396730297)
          ·
            refine ⟨1444915324188925797547723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1926553765585234396730297 1444915324188925797547723)
            ·
              refine ⟨2167372986283388696321585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1444915324188925797547723 2167372986283388696321585)
              ·
                refine ⟨1625529739712541522241189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2167372986283388696321585 1625529739712541522241189)
                ·
                  refine ⟨304786826196101535420223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1625529739712541522241189 304786826196101535420223)
                  ·
                    rfl

theorem cell21_1335533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_1335533 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1335533 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1335533 prefixEnd_1335533 := by exact prefixLift 1335533
  have htrace : WordTrace (prefixWord ++ tailWord_1335533) baseStart_1335533 baseEnd_1335533 := by
    simpa [prefixWord, tailWord_1335533, baseEnd_1335533] using wordTrace_append hprefix tailTrace_1335533
  have hstable : (prefixWord ++ tailWord_1335533).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335533).length < 2 ^ (prefixWord ++ tailWord_1335533).sum := by decide
  have hdescent : baseEnd_1335533 < baseStart_1335533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335609 : List Nat := [1, 2, 1, 6, 1, 3, 2, 1, 4]
def baseStart_1335609 : Nat := 118140960795 + 1335609 * 2 ^ 59
def prefixEnd_1335609 : Nat := 4983230072969 + 3 ^ 40 * 1335609 * 2
def baseEnd_1335609 : Nat := 304804170431542292153401

theorem tailTrace_1335609 : CollatzResearch.WordTrace tailWord_1335609 prefixEnd_1335609 304804170431542292153401 := by
  unfold tailWord_1335609
  simp only [CollatzResearch.WordTrace]
  refine ⟨48713662218324171702033881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32475774812216114468022587 48713662218324171702033881)
  ·
    refine ⟨36535246663743128776525411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48713662218324171702033881 36535246663743128776525411)
    ·
      refine ⟨54802869995614693164788117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36535246663743128776525411 54802869995614693164788117)
      ·
        refine ⟨2568884531044438742099443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 54802869995614693164788117 2568884531044438742099443)
        ·
          refine ⟨3853326796566658113149165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2568884531044438742099443 3853326796566658113149165)
          ·
            refine ⟨1444997548712496792430937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3853326796566658113149165 1444997548712496792430937)
            ·
              refine ⟨1083748161534372594323203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1444997548712496792430937 1083748161534372594323203)
              ·
                refine ⟨1625622242301558891484805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1083748161534372594323203 1625622242301558891484805)
                ·
                  refine ⟨304804170431542292153401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1625622242301558891484805 304804170431542292153401)
                  ·
                    rfl

theorem cell21_1335609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 2, 1, 4].length) (baseStart_1335609 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1335609 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1335609 prefixEnd_1335609 := by exact prefixLift 1335609
  have htrace : WordTrace (prefixWord ++ tailWord_1335609) baseStart_1335609 baseEnd_1335609 := by
    simpa [prefixWord, tailWord_1335609, baseEnd_1335609] using wordTrace_append hprefix tailTrace_1335609
  have hstable : (prefixWord ++ tailWord_1335609).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335609).length < 2 ^ (prefixWord ++ tailWord_1335609).sum := by decide
  have hdescent : baseEnd_1335609 < baseStart_1335609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335634 : List Nat := [3, 2, 2, 1, 1, 1, 2, 1, 8]
def baseStart_1335634 : Nat := 118140960795 + 1335634 * 2 ^ 59
def prefixEnd_1335634 : Nat := 4983230072969 + 3 ^ 40 * 1335634 * 2
def baseEnd_1335634 : Nat := 304809875772147804236683

theorem tailTrace_1335634 : CollatzResearch.WordTrace tailWord_1335634 prefixEnd_1335634 304809875772147804236683 := by
  unfold tailWord_1335634
  simp only [CollatzResearch.WordTrace]
  refine ⟨12178643510808400242923489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32476382695489067314462637 12178643510808400242923489)
  ·
    refine ⟨9133982633106300182192617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12178643510808400242923489 9133982633106300182192617)
    ·
      refine ⟨6850486974829725136644463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9133982633106300182192617 6850486974829725136644463)
      ·
        refine ⟨10275730462244587704966695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6850486974829725136644463 10275730462244587704966695)
        ·
          refine ⟨15413595693366881557450043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10275730462244587704966695 15413595693366881557450043)
          ·
            refine ⟨23120393540050322336175065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15413595693366881557450043 23120393540050322336175065)
            ·
              refine ⟨17340295155037741752131299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23120393540050322336175065 17340295155037741752131299)
              ·
                refine ⟨26010442732556612628196949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17340295155037741752131299 26010442732556612628196949)
                ·
                  refine ⟨304809875772147804236683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26010442732556612628196949 304809875772147804236683)
                  ·
                    rfl

theorem cell21_1335634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 8].length) (baseStart_1335634 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1335634 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1335634 prefixEnd_1335634 := by exact prefixLift 1335634
  have htrace : WordTrace (prefixWord ++ tailWord_1335634) baseStart_1335634 baseEnd_1335634 := by
    simpa [prefixWord, tailWord_1335634, baseEnd_1335634] using wordTrace_append hprefix tailTrace_1335634
  have hstable : (prefixWord ++ tailWord_1335634).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335634).length < 2 ^ (prefixWord ++ tailWord_1335634).sum := by decide
  have hdescent : baseEnd_1335634 < baseStart_1335634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335648 : List Nat := [2, 1, 1, 3, 14]
def baseStart_1335648 : Nat := 118140960795 + 1335648 * 2 ^ 59
def prefixEnd_1335648 : Nat := 4983230072969 + 3 ^ 40 * 1335648 * 2
def baseEnd_1335648 : Nat := 3763124330406011000041

theorem tailTrace_1335648 : CollatzResearch.WordTrace tailWord_1335648 prefixEnd_1335648 3763124330406011000041 := by
  unfold tailWord_1335648
  simp only [CollatzResearch.WordTrace]
  refine ⟨24357542332591440681351799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32476723110121920908469065 24357542332591440681351799)
  ·
    refine ⟨36536313498887161022027699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24357542332591440681351799 36536313498887161022027699)
    ·
      refine ⟨54804470248330741533041549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36536313498887161022027699 54804470248330741533041549)
      ·
        refine ⟨20551676343124028074890581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54804470248330741533041549 20551676343124028074890581)
        ·
          refine ⟨3763124330406011000041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 20551676343124028074890581 3763124330406011000041)
          ·
            rfl

theorem cell21_1335648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 14].length) (baseStart_1335648 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1335648 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1335648 prefixEnd_1335648 := by exact prefixLift 1335648
  have htrace : WordTrace (prefixWord ++ tailWord_1335648) baseStart_1335648 baseEnd_1335648 := by
    simpa [prefixWord, tailWord_1335648, baseEnd_1335648] using wordTrace_append hprefix tailTrace_1335648
  have hstable : (prefixWord ++ tailWord_1335648).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335648).length < 2 ^ (prefixWord ++ tailWord_1335648).sum := by decide
  have hdescent : baseEnd_1335648 < baseStart_1335648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335651 : List Nat := [1, 1, 1, 5, 2, 1, 4, 2, 4]
def baseStart_1335651 : Nat := 118140960795 + 1335651 * 2 ^ 59
def prefixEnd_1335651 : Nat := 4983230072969 + 3 ^ 40 * 1335651 * 2
def baseEnd_1335651 : Nat := 304813755403759552453315

theorem tailTrace_1335651 : CollatzResearch.WordTrace tailWord_1335651 prefixEnd_1335651 304813755403759552453315 := by
  unfold tailWord_1335651
  simp only [CollatzResearch.WordTrace]
  refine ⟨48715194084172012875062807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32476796056114675250041871 48715194084172012875062807)
  ·
    refine ⟨73072791126258019312594211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48715194084172012875062807 73072791126258019312594211)
    ·
      refine ⟨109609186689387028968891317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73072791126258019312594211 109609186689387028968891317)
      ·
        refine ⟨10275861252130033965833561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 109609186689387028968891317 10275861252130033965833561)
        ·
          refine ⟨7706895939097525474375171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10275861252130033965833561 7706895939097525474375171)
          ·
            refine ⟨11560343908646288211562757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7706895939097525474375171 11560343908646288211562757)
            ·
              refine ⟨2167564482871179039668017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11560343908646288211562757 2167564482871179039668017)
              ·
                refine ⟨1625673362153384279751013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2167564482871179039668017 1625673362153384279751013)
                ·
                  refine ⟨304813755403759552453315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1625673362153384279751013 304813755403759552453315)
                  ·
                    rfl

theorem cell21_1335651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 2, 4].length) (baseStart_1335651 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1335651 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1335651 prefixEnd_1335651 := by exact prefixLift 1335651
  have htrace : WordTrace (prefixWord ++ tailWord_1335651) baseStart_1335651 baseEnd_1335651 := by
    simpa [prefixWord, tailWord_1335651, baseEnd_1335651] using wordTrace_append hprefix tailTrace_1335651
  have hstable : (prefixWord ++ tailWord_1335651).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335651).length < 2 ^ (prefixWord ++ tailWord_1335651).sum := by decide
  have hdescent : baseEnd_1335651 < baseStart_1335651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335679 : List Nat := [1, 1, 2, 2, 1, 1, 2, 6, 5]
def baseStart_1335679 : Nat := 118140960795 + 1335679 * 2 ^ 59
def prefixEnd_1335679 : Nat := 4983230072969 + 3 ^ 40 * 1335679 * 2
def baseEnd_1335679 : Nat := 304820145385237725986591

theorem tailTrace_1335679 : CollatzResearch.WordTrace tailWord_1335679 prefixEnd_1335679 304820145385237725986591 := by
  unfold tailWord_1335679
  simp only [CollatzResearch.WordTrace]
  refine ⟨48716215328070573657082091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32477476885380382438054727 48716215328070573657082091)
  ·
    refine ⟨73074322992105860485623137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48716215328070573657082091 73074322992105860485623137)
    ·
      refine ⟨54805742244079395364217353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73074322992105860485623137 54805742244079395364217353)
      ·
        refine ⟨41104306683059546523163015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54805742244079395364217353 41104306683059546523163015)
        ·
          refine ⟨61656460024589319784744523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41104306683059546523163015 61656460024589319784744523)
          ·
            refine ⟨92484690036883979677116785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61656460024589319784744523 92484690036883979677116785)
            ·
              refine ⟨69363517527662984757837589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92484690036883979677116785 69363517527662984757837589)
              ·
                refine ⟨3251414884109202410523637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 69363517527662984757837589 3251414884109202410523637)
                ·
                  refine ⟨304820145385237725986591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3251414884109202410523637 304820145385237725986591)
                  ·
                    rfl

theorem cell21_1335679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 6, 5].length) (baseStart_1335679 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1335679 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1335679 prefixEnd_1335679 := by exact prefixLift 1335679
  have htrace : WordTrace (prefixWord ++ tailWord_1335679) baseStart_1335679 baseEnd_1335679 := by
    simpa [prefixWord, tailWord_1335679, baseEnd_1335679] using wordTrace_append hprefix tailTrace_1335679
  have hstable : (prefixWord ++ tailWord_1335679).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335679).length < 2 ^ (prefixWord ++ tailWord_1335679).sum := by decide
  have hdescent : baseEnd_1335679 < baseStart_1335679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335702 : List Nat := [5, 3, 1, 2, 1, 1, 1, 1, 6]
def baseStart_1335702 : Nat := 118140960795 + 1335702 * 2 ^ 59
def prefixEnd_1335702 : Nat := 4983230072969 + 3 ^ 40 * 1335702 * 2
def baseEnd_1335702 : Nat := 304825394298594797103211

theorem tailTrace_1335702 : CollatzResearch.WordTrace tailWord_1335702 prefixEnd_1335702 304825394298594797103211 := by
  unfold tailWord_1335702
  simp only [CollatzResearch.WordTrace]
  refine ⟨3044815887936703036573085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32478036137991499056779573 3044815887936703036573085)
  ·
    refine ⟨1141805957976263638714907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3044815887936703036573085 1141805957976263638714907)
    ·
      refine ⟨1712708936964395458072361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1141805957976263638714907 1712708936964395458072361)
      ·
        refine ⟨1284531702723296593554271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1712708936964395458072361 1284531702723296593554271)
        ·
          refine ⟨1926797554084944890331407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1284531702723296593554271 1926797554084944890331407)
          ·
            refine ⟨2890196331127417335497111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1926797554084944890331407 2890196331127417335497111)
            ·
              refine ⟨4335294496691126003245667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2890196331127417335497111 4335294496691126003245667)
              ·
                refine ⟨6502941745036689004868501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4335294496691126003245667 6502941745036689004868501)
                ·
                  refine ⟨304825394298594797103211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6502941745036689004868501 304825394298594797103211)
                  ·
                    rfl

theorem cell21_1335702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_1335702 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1335702 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1335702 prefixEnd_1335702 := by exact prefixLift 1335702
  have htrace : WordTrace (prefixWord ++ tailWord_1335702) baseStart_1335702 baseEnd_1335702 := by
    simpa [prefixWord, tailWord_1335702, baseEnd_1335702] using wordTrace_append hprefix tailTrace_1335702
  have hstable : (prefixWord ++ tailWord_1335702).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335702).length < 2 ^ (prefixWord ++ tailWord_1335702).sum := by decide
  have hdescent : baseEnd_1335702 < baseStart_1335702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335724 : List Nat := [2, 2, 1, 1, 1, 1, 3, 10]
def baseStart_1335724 : Nat := 118140960795 + 1335724 * 2 ^ 59
def prefixEnd_1335724 : Nat := 4983230072969 + 3 ^ 40 * 1335724 * 2
def baseEnd_1335724 : Nat := 101610138332775882578833

theorem tailTrace_1335724 : CollatzResearch.WordTrace tailWord_1335724 prefixEnd_1335724 101610138332775882578833 := by
  unfold tailWord_1335724
  simp only [CollatzResearch.WordTrace]
  refine ⟨24358928306453773171235113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32478571075271697561646817 24358928306453773171235113)
  ·
    refine ⟨18269196229840329878426335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24358928306453773171235113 18269196229840329878426335)
    ·
      refine ⟨27403794344760494817639503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18269196229840329878426335 27403794344760494817639503)
      ·
        refine ⟨41105691517140742226459255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27403794344760494817639503 41105691517140742226459255)
        ·
          refine ⟨61658537275711113339688883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41105691517140742226459255 61658537275711113339688883)
          ·
            refine ⟨92487805913566670009533325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61658537275711113339688883 92487805913566670009533325)
            ·
              refine ⟨34682927217587501253574997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92487805913566670009533325 34682927217587501253574997)
              ·
                refine ⟨101610138332775882578833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 34682927217587501253574997 101610138332775882578833)
                ·
                  rfl

theorem cell21_1335724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 10].length) (baseStart_1335724 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1335724 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1335724 prefixEnd_1335724 := by exact prefixLift 1335724
  have htrace : WordTrace (prefixWord ++ tailWord_1335724) baseStart_1335724 baseEnd_1335724 := by
    simpa [prefixWord, tailWord_1335724, baseEnd_1335724] using wordTrace_append hprefix tailTrace_1335724
  have hstable : (prefixWord ++ tailWord_1335724).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335724).length < 2 ^ (prefixWord ++ tailWord_1335724).sum := by decide
  have hdescent : baseEnd_1335724 < baseStart_1335724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335741 : List Nat := [1, 4, 1, 2, 2, 3, 1, 7]
def baseStart_1335741 : Nat := 118140960795 + 1335741 * 2 ^ 59
def prefixEnd_1335741 : Nat := 4983230072969 + 3 ^ 40 * 1335741 * 2
def baseEnd_1335741 : Nat := 101611431543313131984377

theorem tailTrace_1335741 : CollatzResearch.WordTrace tailWord_1335741 prefixEnd_1335741 101611431543313131984377 := by
  unfold tailWord_1335741
  simp only [CollatzResearch.WordTrace]
  refine ⟨48718476653845958245839077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32478984435897305497226051 48718476653845958245839077)
  ·
    refine ⟨9134714372596117171094827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48718476653845958245839077 9134714372596117171094827)
    ·
      refine ⟨13702071558894175756642241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9134714372596117171094827 13702071558894175756642241)
      ·
        refine ⟨10276553669170631817481681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13702071558894175756642241 10276553669170631817481681)
        ·
          refine ⟨7707415251877973863111261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10276553669170631817481681 7707415251877973863111261)
          ·
            refine ⟨2890280719454240198666723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7707415251877973863111261 2890280719454240198666723)
            ·
              refine ⟨4335421079181360298000085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2890280719454240198666723 4335421079181360298000085)
              ·
                refine ⟨101611431543313131984377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4335421079181360298000085 101611431543313131984377)
                ·
                  rfl

theorem cell21_1335741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 7].length) (baseStart_1335741 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1335741 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1335741 prefixEnd_1335741 := by exact prefixLift 1335741
  have htrace : WordTrace (prefixWord ++ tailWord_1335741) baseStart_1335741 baseEnd_1335741 := by
    simpa [prefixWord, tailWord_1335741, baseEnd_1335741] using wordTrace_append hprefix tailTrace_1335741
  have hstable : (prefixWord ++ tailWord_1335741).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335741).length < 2 ^ (prefixWord ++ tailWord_1335741).sum := by decide
  have hdescent : baseEnd_1335741 < baseStart_1335741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335800 : List Nat := [2, 1, 2, 1, 1, 4, 1, 9]
def baseStart_1335800 : Nat := 118140960795 + 1335800 * 2 ^ 59
def prefixEnd_1335800 : Nat := 4983230072969 + 3 ^ 40 * 1335800 * 2
def baseEnd_1335800 : Nat := 101615919744589468156559

theorem tailTrace_1335800 : CollatzResearch.WordTrace tailWord_1335800 prefixEnd_1335800 101615919744589468156559 := by
  unfold tailWord_1335800
  simp only [CollatzResearch.WordTrace]
  refine ⟨24360314280316105661118427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32480419040421474214824569 24360314280316105661118427)
  ·
    refine ⟨36540471420474158491677641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24360314280316105661118427 36540471420474158491677641)
    ·
      refine ⟨27405353565355618868758231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36540471420474158491677641 27405353565355618868758231)
      ·
        refine ⟨41108030348033428303137347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27405353565355618868758231 41108030348033428303137347)
        ·
          refine ⟨61662045522050142454706021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41108030348033428303137347 61662045522050142454706021)
          ·
            refine ⟨11561633535384401710257379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61662045522050142454706021 11561633535384401710257379)
            ·
              refine ⟨17342450303076602565386069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11561633535384401710257379 17342450303076602565386069)
              ·
                refine ⟨101615919744589468156559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17342450303076602565386069 101615919744589468156559)
                ·
                  rfl

theorem cell21_1335800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 9].length) (baseStart_1335800 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1335800 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1335800 prefixEnd_1335800 := by exact prefixLift 1335800
  have htrace : WordTrace (prefixWord ++ tailWord_1335800) baseStart_1335800 baseEnd_1335800 := by
    simpa [prefixWord, tailWord_1335800, baseEnd_1335800] using wordTrace_append hprefix tailTrace_1335800
  have hstable : (prefixWord ++ tailWord_1335800).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335800).length < 2 ^ (prefixWord ++ tailWord_1335800).sum := by decide
  have hdescent : baseEnd_1335800 < baseStart_1335800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335848 : List Nat := [2, 1, 5, 2, 1, 1, 1, 1, 7]
def baseStart_1335848 : Nat := 118140960795 + 1335848 * 2 ^ 59
def prefixEnd_1335848 : Nat := 4983230072969 + 3 ^ 40 * 1335848 * 2
def baseEnd_1335848 : Nat := 304858713487730987669579

theorem tailTrace_1335848 : CollatzResearch.WordTrace tailWord_1335848 prefixEnd_1335848 304858713487730987669579 := by
  unfold tailWord_1335848
  simp only [CollatzResearch.WordTrace]
  refine ⟨24361189632229157759992099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32481586176305543679989465 24361189632229157759992099)
  ·
    refine ⟨36541784448343736639988149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24361189632229157759992099 36541784448343736639988149)
    ·
      refine ⟨3425792292032225309998889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36541784448343736639988149 3425792292032225309998889)
      ·
        refine ⟨2569344219024168982499167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3425792292032225309998889 2569344219024168982499167)
        ·
          refine ⟨3854016328536253473748751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2569344219024168982499167 3854016328536253473748751)
          ·
            refine ⟨5781024492804380210623127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3854016328536253473748751 5781024492804380210623127)
            ·
              refine ⟨8671536739206570315934691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5781024492804380210623127 8671536739206570315934691)
              ·
                refine ⟨13007305108809855473902037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8671536739206570315934691 13007305108809855473902037)
                ·
                  refine ⟨304858713487730987669579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13007305108809855473902037 304858713487730987669579)
                  ·
                    rfl

theorem cell21_1335848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 7].length) (baseStart_1335848 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1335848 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1335848 prefixEnd_1335848 := by exact prefixLift 1335848
  have htrace : WordTrace (prefixWord ++ tailWord_1335848) baseStart_1335848 baseEnd_1335848 := by
    simpa [prefixWord, tailWord_1335848, baseEnd_1335848] using wordTrace_append hprefix tailTrace_1335848
  have hstable : (prefixWord ++ tailWord_1335848).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335848).length < 2 ^ (prefixWord ++ tailWord_1335848).sum := by decide
  have hdescent : baseEnd_1335848 < baseStart_1335848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335865 : List Nat := [1, 2, 1, 5, 1, 1, 4, 3, 3]
def baseStart_1335865 : Nat := 118140960795 + 1335865 * 2 ^ 59
def prefixEnd_1335865 : Nat := 4983230072969 + 3 ^ 40 * 1335865 * 2
def baseEnd_1335865 : Nat := 304862593119342735886211

theorem tailTrace_1335865 : CollatzResearch.WordTrace tailWord_1335865 prefixEnd_1335865 304862593119342735886211 := by
  unfold tailWord_1335865
  simp only [CollatzResearch.WordTrace]
  refine ⟨48722999305396727423353049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32481999536931151615568699 48722999305396727423353049)
  ·
    refine ⟨36542249479047545567514787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48722999305396727423353049 36542249479047545567514787)
    ·
      refine ⟨54813374218571318351272181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36542249479047545567514787 54813374218571318351272181)
      ·
        refine ⟨5138753832991061095431767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54813374218571318351272181 5138753832991061095431767)
        ·
          refine ⟨7708130749486591643147651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5138753832991061095431767 7708130749486591643147651)
          ·
            refine ⟨11562196124229887464721477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7708130749486591643147651 11562196124229887464721477)
            ·
              refine ⟨2167911773293103899635277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11562196124229887464721477 2167911773293103899635277)
              ·
                refine ⟨812966914984913962363229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2167911773293103899635277 812966914984913962363229)
                ·
                  refine ⟨304862593119342735886211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 812966914984913962363229 304862593119342735886211)
                  ·
                    rfl

theorem cell21_1335865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 3, 3].length) (baseStart_1335865 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1335865 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1335865 prefixEnd_1335865 := by exact prefixLift 1335865
  have htrace : WordTrace (prefixWord ++ tailWord_1335865) baseStart_1335865 baseEnd_1335865 := by
    simpa [prefixWord, tailWord_1335865, baseEnd_1335865] using wordTrace_append hprefix tailTrace_1335865
  have hstable : (prefixWord ++ tailWord_1335865).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335865).length < 2 ^ (prefixWord ++ tailWord_1335865).sum := by decide
  have hdescent : baseEnd_1335865 < baseStart_1335865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335879 : List Nat := [1, 1, 4, 1, 4, 1, 3, 2, 4]
def baseStart_1335879 : Nat := 118140960795 + 1335879 * 2 ^ 59
def prefixEnd_1335879 : Nat := 4983230072969 + 3 ^ 40 * 1335879 * 2
def baseEnd_1335879 : Nat := 304865788110081822652849

theorem tailTrace_1335879 : CollatzResearch.WordTrace tailWord_1335879 prefixEnd_1335879 304865788110081822652849 := by
  unfold tailWord_1335879
  simp only [CollatzResearch.WordTrace]
  refine ⟨48723509927346007814362691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32482339951564005209575127 48723509927346007814362691)
  ·
    refine ⟨73085264891019011721544037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48723509927346007814362691 73085264891019011721544037)
    ·
      refine ⟨13703487167066064697789507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73085264891019011721544037 13703487167066064697789507)
      ·
        refine ⟨20555230750599097046684261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13703487167066064697789507 20555230750599097046684261)
        ·
          refine ⟨3854105765737330696253299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20555230750599097046684261 3854105765737330696253299)
          ·
            refine ⟨5781158648605996044379949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3854105765737330696253299 5781158648605996044379949)
            ·
              refine ⟨2167934493227248516642481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5781158648605996044379949 2167934493227248516642481)
              ·
                refine ⟨1625950869920436387481861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2167934493227248516642481 1625950869920436387481861)
                ·
                  refine ⟨304865788110081822652849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1625950869920436387481861 304865788110081822652849)
                  ·
                    rfl

theorem cell21_1335879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 2, 4].length) (baseStart_1335879 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1335879 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1335879 prefixEnd_1335879 := by exact prefixLift 1335879
  have htrace : WordTrace (prefixWord ++ tailWord_1335879) baseStart_1335879 baseEnd_1335879 := by
    simpa [prefixWord, tailWord_1335879, baseEnd_1335879] using wordTrace_append hprefix tailTrace_1335879
  have hstable : (prefixWord ++ tailWord_1335879).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335879).length < 2 ^ (prefixWord ++ tailWord_1335879).sum := by decide
  have hdescent : baseEnd_1335879 < baseStart_1335879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335902 : List Nat := [4, 4, 1, 2, 2, 1, 2, 5]
def baseStart_1335902 : Nat := 118140960795 + 1335902 * 2 ^ 59
def prefixEnd_1335902 : Nat := 4983230072969 + 3 ^ 40 * 1335902 * 2
def baseEnd_1335902 : Nat := 101623679007812964589823

theorem tailTrace_1335902 : CollatzResearch.WordTrace tailWord_1335902 prefixEnd_1335902 101623679007812964589823 := by
  unfold tailWord_1335902
  simp only [CollatzResearch.WordTrace]
  refine ⟨6090543600782835342806245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32482899204175121828299973 6090543600782835342806245)
  ·
    refine ⟨1141976925146781626776171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6090543600782835342806245 1141976925146781626776171)
    ·
      refine ⟨1712965387720172440164257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1141976925146781626776171 1712965387720172440164257)
      ·
        refine ⟨1284724040790129330123193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1712965387720172440164257 1284724040790129330123193)
        ·
          refine ⟨963543030592596997592395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1284724040790129330123193 963543030592596997592395)
          ·
            refine ⟨1445314545888895496388593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 963543030592596997592395 1445314545888895496388593)
            ·
              refine ⟨1083985909416671622291445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1445314545888895496388593 1083985909416671622291445)
              ·
                refine ⟨101623679007812964589823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1083985909416671622291445 101623679007812964589823)
                ·
                  rfl

theorem cell21_1335902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 2, 5].length) (baseStart_1335902 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1335902 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1335902 prefixEnd_1335902 := by exact prefixLift 1335902
  have htrace : WordTrace (prefixWord ++ tailWord_1335902) baseStart_1335902 baseEnd_1335902 := by
    simpa [prefixWord, tailWord_1335902, baseEnd_1335902] using wordTrace_append hprefix tailTrace_1335902
  have hstable : (prefixWord ++ tailWord_1335902).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335902).length < 2 ^ (prefixWord ++ tailWord_1335902).sum := by decide
  have hdescent : baseEnd_1335902 < baseStart_1335902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1335907 : List Nat := [1, 1, 1, 5, 1, 2, 1, 4, 5]
def baseStart_1335907 : Nat := 118140960795 + 1335907 * 2 ^ 59
def prefixEnd_1335907 : Nat := 4983230072969 + 3 ^ 40 * 1335907 * 2
def baseEnd_1335907 : Nat := 304872178091559996186125

theorem tailTrace_1335907 : CollatzResearch.WordTrace tailWord_1335907 prefixEnd_1335907 304872178091559996186125 := by
  unfold tailWord_1335907
  simp only [CollatzResearch.WordTrace]
  refine ⟨48724531171244568596381975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32483020780829712397587983 48724531171244568596381975)
  ·
    refine ⟨73086796756866852894572963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48724531171244568596381975 73086796756866852894572963)
    ·
      refine ⟨109630195135300279341859445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73086796756866852894572963 109630195135300279341859445)
      ·
        refine ⟨10277830793934401188299323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 109630195135300279341859445 10277830793934401188299323)
        ·
          refine ⟨15416746190901601782448985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10277830793934401188299323 15416746190901601782448985)
          ·
            refine ⟨11562559643176201336836739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15416746190901601782448985 11562559643176201336836739)
            ·
              refine ⟨17343839464764302005255109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11562559643176201336836739 17343839464764302005255109)
              ·
                refine ⟨3251969899643306625985333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17343839464764302005255109 3251969899643306625985333)
                ·
                  refine ⟨304872178091559996186125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3251969899643306625985333 304872178091559996186125)
                  ·
                    rfl

theorem cell21_1335907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 4, 5].length) (baseStart_1335907 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1335907 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1335907 prefixEnd_1335907 := by exact prefixLift 1335907
  have htrace : WordTrace (prefixWord ++ tailWord_1335907) baseStart_1335907 baseEnd_1335907 := by
    simpa [prefixWord, tailWord_1335907, baseEnd_1335907] using wordTrace_append hprefix tailTrace_1335907
  have hstable : (prefixWord ++ tailWord_1335907).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1335907).length < 2 ^ (prefixWord ++ tailWord_1335907).sum := by decide
  have hdescent : baseEnd_1335907 < baseStart_1335907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1335907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336197 : List Nat := [1, 3, 1, 1, 3, 4, 3, 5]
def baseStart_1336197 : Nat := 118140960795 + 1336197 * 2 ^ 59
def prefixEnd_1336197 : Nat := 4983230072969 + 3 ^ 40 * 1336197 * 2
def baseEnd_1336197 : Nat := 101646120014194645450733

theorem tailTrace_1336197 : CollatzResearch.WordTrace tailWord_1336197 prefixEnd_1336197 101646120014194645450733 := by
  unfold tailWord_1336197
  simp only [CollatzResearch.WordTrace]
  refine ⟨48735108340193948124438845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32490072226795965416292563 48735108340193948124438845)
  ·
    refine ⟨18275665627572730546664567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48735108340193948124438845 18275665627572730546664567)
    ·
      refine ⟨27413498441359095819996851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18275665627572730546664567 27413498441359095819996851)
      ·
        refine ⟨41120247662038643729995277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27413498441359095819996851 41120247662038643729995277)
        ·
          refine ⟨15420092873264491398748229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41120247662038643729995277 15420092873264491398748229)
          ·
            refine ⟨2891267413737092137265293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15420092873264491398748229 2891267413737092137265293)
            ·
              refine ⟨1084225280151409551474485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2891267413737092137265293 1084225280151409551474485)
              ·
                refine ⟨101646120014194645450733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1084225280151409551474485 101646120014194645450733)
                ·
                  rfl

theorem cell21_1336197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 3, 5].length) (baseStart_1336197 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1336197 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1336197 prefixEnd_1336197 := by exact prefixLift 1336197
  have htrace : WordTrace (prefixWord ++ tailWord_1336197) baseStart_1336197 baseEnd_1336197 := by
    simpa [prefixWord, tailWord_1336197, baseEnd_1336197] using wordTrace_append hprefix tailTrace_1336197
  have hstable : (prefixWord ++ tailWord_1336197).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336197).length < 2 ^ (prefixWord ++ tailWord_1336197).sum := by decide
  have hdescent : baseEnd_1336197 < baseStart_1336197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336228 : List Nat := [2, 3, 1, 2, 1, 2, 1, 6, 3]
def baseStart_1336228 : Nat := 118140960795 + 1336228 * 2 ^ 59
def prefixEnd_1336228 : Nat := 4983230072969 + 3 ^ 40 * 1336228 * 2
def baseEnd_1336228 : Nat := 304945434664934771335469

theorem tailTrace_1336228 : CollatzResearch.WordTrace tailWord_1336228 prefixEnd_1336228 304945434664934771335469 := by
  unfold tailWord_1336228
  simp only [CollatzResearch.WordTrace]
  refine ⟨24368119501540820209408669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32490826002054426945878225 24368119501540820209408669)
  ·
    refine ⟨9138044813077807578528251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24368119501540820209408669 9138044813077807578528251)
    ·
      refine ⟨13707067219616711367792377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9138044813077807578528251 13707067219616711367792377)
      ·
        refine ⟨10280300414712533525844283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13707067219616711367792377 10280300414712533525844283)
        ·
          refine ⟨15420450622068800288766425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10280300414712533525844283 15420450622068800288766425)
          ·
            refine ⟨11565337966551600216574819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15420450622068800288766425 11565337966551600216574819)
            ·
              refine ⟨17348006949827400324862229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11565337966551600216574819 17348006949827400324862229)
              ·
                refine ⟨813187825773159390227917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17348006949827400324862229 813187825773159390227917)
                ·
                  refine ⟨304945434664934771335469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 813187825773159390227917 304945434664934771335469)
                  ·
                    rfl

theorem cell21_1336228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 6, 3].length) (baseStart_1336228 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1336228 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1336228 prefixEnd_1336228 := by exact prefixLift 1336228
  have htrace : WordTrace (prefixWord ++ tailWord_1336228) baseStart_1336228 baseEnd_1336228 := by
    simpa [prefixWord, tailWord_1336228, baseEnd_1336228] using wordTrace_append hprefix tailTrace_1336228
  have hstable : (prefixWord ++ tailWord_1336228).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336228).length < 2 ^ (prefixWord ++ tailWord_1336228).sum := by decide
  have hdescent : baseEnd_1336228 < baseStart_1336228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336256 : List Nat := [2, 1, 1, 2, 3, 4, 1, 7]
def baseStart_1336256 : Nat := 118140960795 + 1336256 * 2 ^ 59
def prefixEnd_1336256 : Nat := 4983230072969 + 3 ^ 40 * 1336256 * 2
def baseEnd_1336256 : Nat := 101650608215470981622915

theorem tailTrace_1336256 : CollatzResearch.WordTrace tailWord_1336256 prefixEnd_1336256 101650608215470981622915 := by
  unfold tailWord_1336256
  simp only [CollatzResearch.WordTrace]
  refine ⟨24368630123490100600418311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32491506831320134133891081 24368630123490100600418311)
  ·
    refine ⟨36552945185235150900627467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24368630123490100600418311 36552945185235150900627467)
    ·
      refine ⟨54829417777852726350941201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36552945185235150900627467 54829417777852726350941201)
      ·
        refine ⟨41122063333389544763205901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54829417777852726350941201 41122063333389544763205901)
        ·
          refine ⟨15420773750021079286202213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41122063333389544763205901 15420773750021079286202213)
          ·
            refine ⟨2891395078128952366162915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15420773750021079286202213 2891395078128952366162915)
            ·
              refine ⟨4337092617193428549244373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2891395078128952366162915 4337092617193428549244373)
              ·
                refine ⟨101650608215470981622915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4337092617193428549244373 101650608215470981622915)
                ·
                  rfl

theorem cell21_1336256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 7].length) (baseStart_1336256 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1336256 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1336256 prefixEnd_1336256 := by exact prefixLift 1336256
  have htrace : WordTrace (prefixWord ++ tailWord_1336256) baseStart_1336256 baseEnd_1336256 := by
    simpa [prefixWord, tailWord_1336256, baseEnd_1336256] using wordTrace_append hprefix tailTrace_1336256
  have hstable : (prefixWord ++ tailWord_1336256).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336256).length < 2 ^ (prefixWord ++ tailWord_1336256).sum := by decide
  have hdescent : baseEnd_1336256 < baseStart_1336256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336290 : List Nat := [3, 3, 3, 1, 1, 2, 2, 6]
def baseStart_1336290 : Nat := 118140960795 + 1336290 * 2 ^ 59
def prefixEnd_1336290 : Nat := 4983230072969 + 3 ^ 40 * 1336290 * 2
def baseEnd_1336290 : Nat := 101653194636545480434003

theorem tailTrace_1336290 : CollatzResearch.WordTrace tailWord_1336290 prefixEnd_1336290 101653194636545480434003 := by
  unfold tailWord_1336290
  simp only [CollatzResearch.WordTrace]
  refine ⟨12184625082214256251893581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32492333552571350005049549 12184625082214256251893581)
  ·
    refine ⟨4569234405830346094460093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12184625082214256251893581 4569234405830346094460093)
    ·
      refine ⟨1713462902186379785422535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4569234405830346094460093 1713462902186379785422535)
      ·
        refine ⟨2570194353279569678133803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1713462902186379785422535 2570194353279569678133803)
        ·
          refine ⟨3855291529919354517200705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2570194353279569678133803 3855291529919354517200705)
          ·
            refine ⟨2891468647439515887900529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3855291529919354517200705 2891468647439515887900529)
            ·
              refine ⟨2168601485579636915925397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2891468647439515887900529 2168601485579636915925397)
              ·
                refine ⟨101653194636545480434003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2168601485579636915925397 101653194636545480434003)
                ·
                  rfl

theorem cell21_1336290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 6].length) (baseStart_1336290 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1336290 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1336290 prefixEnd_1336290 := by exact prefixLift 1336290
  have htrace : WordTrace (prefixWord ++ tailWord_1336290) baseStart_1336290 baseEnd_1336290 := by
    simpa [prefixWord, tailWord_1336290, baseEnd_1336290] using wordTrace_append hprefix tailTrace_1336290
  have hstable : (prefixWord ++ tailWord_1336290).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336290).length < 2 ^ (prefixWord ++ tailWord_1336290).sum := by decide
  have hdescent : baseEnd_1336290 < baseStart_1336290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336293 : List Nat := [1, 3, 1, 6, 1, 2, 2, 1, 4]
def baseStart_1336293 : Nat := 118140960795 + 1336293 * 2 ^ 59
def prefixEnd_1336293 : Nat := 4983230072969 + 3 ^ 40 * 1336293 * 2
def baseEnd_1336293 : Nat := 304960268550509102752003

theorem tailTrace_1336293 : CollatzResearch.WordTrace tailWord_1336293 prefixEnd_1336293 304960268550509102752003 := by
  unfold tailWord_1336293
  simp only [CollatzResearch.WordTrace]
  refine ⟨48738609747846156519933533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32492406498564104346622355 48738609747846156519933533)
  ·
    refine ⟨18276978655442308694975075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48738609747846156519933533 18276978655442308694975075)
    ·
      refine ⟨27415467983163463042462613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18276978655442308694975075 27415467983163463042462613)
      ·
        refine ⟨1285100061710787330115435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 27415467983163463042462613 1285100061710787330115435)
        ·
          refine ⟨1927650092566180995173153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1285100061710787330115435 1927650092566180995173153)
          ·
            refine ⟨1445737569424635746379865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1927650092566180995173153 1445737569424635746379865)
            ·
              refine ⟨1084303177068476809784899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1445737569424635746379865 1084303177068476809784899)
              ·
                refine ⟨1626454765602715214677349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1084303177068476809784899 1626454765602715214677349)
                ·
                  refine ⟨304960268550509102752003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1626454765602715214677349 304960268550509102752003)
                  ·
                    rfl

theorem cell21_1336293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 2, 1, 4].length) (baseStart_1336293 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1336293 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1336293 prefixEnd_1336293 := by exact prefixLift 1336293
  have htrace : WordTrace (prefixWord ++ tailWord_1336293) baseStart_1336293 baseEnd_1336293 := by
    simpa [prefixWord, tailWord_1336293, baseEnd_1336293] using wordTrace_append hprefix tailTrace_1336293
  have hstable : (prefixWord ++ tailWord_1336293).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336293).length < 2 ^ (prefixWord ++ tailWord_1336293).sum := by decide
  have hdescent : baseEnd_1336293 < baseStart_1336293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336380 : List Nat := [2, 2, 2, 2, 2, 2, 1, 5, 3]
def baseStart_1336380 : Nat := 118140960795 + 1336380 * 2 ^ 59
def prefixEnd_1336380 : Nat := 4983230072969 + 3 ^ 40 * 1336380 * 2
def baseEnd_1336380 : Nat := 304980123135816284801825

theorem tailTrace_1336380 : CollatzResearch.WordTrace tailWord_1336380 prefixEnd_1336380 304980123135816284801825 := by
  unfold tailWord_1336380
  simp only [CollatzResearch.WordTrace]
  refine ⟨24370891449265485189175297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32494521932353980252233729 24370891449265485189175297)
  ·
    refine ⟨18278168586949113891881473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24370891449265485189175297 18278168586949113891881473)
    ·
      refine ⟨13708626440211835418911105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18278168586949113891881473 13708626440211835418911105)
      ·
        refine ⟨10281469830158876564183329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13708626440211835418911105 10281469830158876564183329)
        ·
          refine ⟨7711102372619157423137497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10281469830158876564183329 7711102372619157423137497)
          ·
            refine ⟨5783326779464368067353123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7711102372619157423137497 5783326779464368067353123)
            ·
              refine ⟨8674990169196552101029685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5783326779464368067353123 8674990169196552101029685)
              ·
                refine ⟨813280328362176759471533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8674990169196552101029685 813280328362176759471533)
                ·
                  refine ⟨304980123135816284801825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 813280328362176759471533 304980123135816284801825)
                  ·
                    rfl

theorem cell21_1336380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 5, 3].length) (baseStart_1336380 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1336380 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1336380 prefixEnd_1336380 := by exact prefixLift 1336380
  have htrace : WordTrace (prefixWord ++ tailWord_1336380) baseStart_1336380 baseEnd_1336380 := by
    simpa [prefixWord, tailWord_1336380, baseEnd_1336380] using wordTrace_append hprefix tailTrace_1336380
  have hstable : (prefixWord ++ tailWord_1336380).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336380).length < 2 ^ (prefixWord ++ tailWord_1336380).sum := by decide
  have hdescent : baseEnd_1336380 < baseStart_1336380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336394 : List Nat := [3, 1, 2, 1, 1, 2, 5, 2, 4]
def baseStart_1336394 : Nat := 118140960795 + 1336394 * 2 ^ 59
def prefixEnd_1336394 : Nat := 4983230072969 + 3 ^ 40 * 1336394 * 2
def baseEnd_1336394 : Nat := 304983318126555371568463

theorem tailTrace_1336394 : CollatzResearch.WordTrace tailWord_1336394 prefixEnd_1336394 304983318126555371568463 := by
  unfold tailWord_1336394
  simp only [CollatzResearch.WordTrace]
  refine ⟨12185573380120062692340059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32494862346986833846240157 12185573380120062692340059)
  ·
    refine ⟨18278360070180094038510089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12185573380120062692340059 18278360070180094038510089)
    ·
      refine ⟨13708770052635070528882567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18278360070180094038510089 13708770052635070528882567)
      ·
        refine ⟨20563155078952605793323851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13708770052635070528882567 20563155078952605793323851)
        ·
          refine ⟨30844732618428908689985777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20563155078952605793323851 30844732618428908689985777)
          ·
            refine ⟨23133549463821681517489333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30844732618428908689985777 23133549463821681517489333)
            ·
              refine ⟨2168770262233282642264625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23133549463821681517489333 2168770262233282642264625)
              ·
                refine ⟨1626577696674961981698469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2168770262233282642264625 1626577696674961981698469)
                ·
                  refine ⟨304983318126555371568463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1626577696674961981698469 304983318126555371568463)
                  ·
                    rfl

theorem cell21_1336394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 2, 4].length) (baseStart_1336394 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1336394 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1336394 prefixEnd_1336394 := by exact prefixLift 1336394
  have htrace : WordTrace (prefixWord ++ tailWord_1336394) baseStart_1336394 baseEnd_1336394 := by
    simpa [prefixWord, tailWord_1336394, baseEnd_1336394] using wordTrace_append hprefix tailTrace_1336394
  have hstable : (prefixWord ++ tailWord_1336394).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336394).length < 2 ^ (prefixWord ++ tailWord_1336394).sum := by decide
  have hdescent : baseEnd_1336394 < baseStart_1336394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336397 : List Nat := [1, 6, 1, 1, 1, 2, 2, 4, 3]
def baseStart_1336397 : Nat := 118140960795 + 1336397 * 2 ^ 59
def prefixEnd_1336397 : Nat := 4983230072969 + 3 ^ 40 * 1336397 * 2
def baseEnd_1336397 : Nat := 304984002767428033018457

theorem tailTrace_1336397 : CollatzResearch.WordTrace tailWord_1336397 prefixEnd_1336397 304984002767428033018457 := by
  unfold tailWord_1336397
  simp only [CollatzResearch.WordTrace]
  refine ⟨48742402939469382281719445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32494935292979588187812963 48742402939469382281719445)
  ·
    refine ⟨2284800137787627294455599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 48742402939469382281719445 2284800137787627294455599)
    ·
      refine ⟨3427200206681440941683399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2284800137787627294455599 3427200206681440941683399)
      ·
        refine ⟨5140800310022161412525099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3427200206681440941683399 5140800310022161412525099)
        ·
          refine ⟨7711200465033242118787649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5140800310022161412525099 7711200465033242118787649)
          ·
            refine ⟨5783400348774931589090737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7711200465033242118787649 5783400348774931589090737)
            ·
              refine ⟨4337550261581198691818053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5783400348774931589090737 4337550261581198691818053)
              ·
                refine ⟨813290674046474754715885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4337550261581198691818053 813290674046474754715885)
                ·
                  refine ⟨304984002767428033018457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 813290674046474754715885 304984002767428033018457)
                  ·
                    rfl

theorem cell21_1336397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_1336397 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1336397 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1336397 prefixEnd_1336397 := by exact prefixLift 1336397
  have htrace : WordTrace (prefixWord ++ tailWord_1336397) baseStart_1336397 baseEnd_1336397 := by
    simpa [prefixWord, tailWord_1336397, baseEnd_1336397] using wordTrace_append hprefix tailTrace_1336397
  have hstable : (prefixWord ++ tailWord_1336397).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336397).length < 2 ^ (prefixWord ++ tailWord_1336397).sum := by decide
  have hdescent : baseEnd_1336397 < baseStart_1336397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336425 : List Nat := [1, 2, 1, 1, 1, 8, 2, 5]
def baseStart_1336425 : Nat := 118140960795 + 1336425 * 2 ^ 59
def prefixEnd_1336425 : Nat := 4983230072969 + 3 ^ 40 * 1336425 * 2
def baseEnd_1336425 : Nat := 101663464249635402183911

theorem tailTrace_1336425 : CollatzResearch.WordTrace tailWord_1336425 prefixEnd_1336425 101663464249635402183911 := by
  unfold tailWord_1336425
  simp only [CollatzResearch.WordTrace]
  refine ⟨48743424183367943063738729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32495616122245295375825819 48743424183367943063738729)
  ·
    refine ⟨36557568137525957297804047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48743424183367943063738729 36557568137525957297804047)
    ·
      refine ⟨54836352206288935946706071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36557568137525957297804047 54836352206288935946706071)
      ·
        refine ⟨82254528309433403920059107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54836352206288935946706071 82254528309433403920059107)
        ·
          refine ⟨123381792464150105880088661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82254528309433403920059107 123381792464150105880088661)
          ·
            refine ⟨1445880380439259053282289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 123381792464150105880088661 1445880380439259053282289)
            ·
              refine ⟨1084410285329444289961717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1445880380439259053282289 1084410285329444289961717)
              ·
                refine ⟨101663464249635402183911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1084410285329444289961717 101663464249635402183911)
                ·
                  rfl

theorem cell21_1336425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 2, 5].length) (baseStart_1336425 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1336425 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1336425 prefixEnd_1336425 := by exact prefixLift 1336425
  have htrace : WordTrace (prefixWord ++ tailWord_1336425) baseStart_1336425 baseEnd_1336425 := by
    simpa [prefixWord, tailWord_1336425, baseEnd_1336425] using wordTrace_append hprefix tailTrace_1336425
  have hstable : (prefixWord ++ tailWord_1336425).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336425).length < 2 ^ (prefixWord ++ tailWord_1336425).sum := by decide
  have hdescent : baseEnd_1336425 < baseStart_1336425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336467 : List Nat := [1, 1, 1, 2, 1, 2, 5, 8]
def baseStart_1336467 : Nat := 118140960795 + 1336467 * 2 ^ 59
def prefixEnd_1336467 : Nat := 4983230072969 + 3 ^ 40 * 1336467 * 2
def baseEnd_1336467 : Nat := 101666659240374488950549

theorem tailTrace_1336467 : CollatzResearch.WordTrace tailWord_1336467 prefixEnd_1336467 101666659240374488950549 := by
  unfold tailWord_1336467
  simp only [CollatzResearch.WordTrace]
  refine ⟨48744956049215784236767655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32496637366143856157845103 48744956049215784236767655)
  ·
    refine ⟨73117434073823676355151483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48744956049215784236767655 73117434073823676355151483)
    ·
      refine ⟨109676151110735514532727225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73117434073823676355151483 109676151110735514532727225)
      ·
        refine ⟨82257113333051635899545419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109676151110735514532727225 82257113333051635899545419)
        ·
          refine ⟨123385669999577453849318129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82257113333051635899545419 123385669999577453849318129)
          ·
            refine ⟨92539252499683090386988597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123385669999577453849318129 92539252499683090386988597)
            ·
              refine ⟨8675554921845289723780181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 92539252499683090386988597 8675554921845289723780181)
              ·
                refine ⟨101666659240374488950549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8675554921845289723780181 101666659240374488950549)
                ·
                  rfl

theorem cell21_1336467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 8].length) (baseStart_1336467 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1336467 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1336467 prefixEnd_1336467 := by exact prefixLift 1336467
  have htrace : WordTrace (prefixWord ++ tailWord_1336467) baseStart_1336467 baseEnd_1336467 := by
    simpa [prefixWord, tailWord_1336467, baseEnd_1336467] using wordTrace_append hprefix tailTrace_1336467
  have hstable : (prefixWord ++ tailWord_1336467).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336467).length < 2 ^ (prefixWord ++ tailWord_1336467).sum := by decide
  have hdescent : baseEnd_1336467 < baseStart_1336467 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336484 : List Nat := [2, 3, 1, 2, 3, 1, 2, 7]
def baseStart_1336484 : Nat := 118140960795 + 1336484 * 2 ^ 59
def prefixEnd_1336484 : Nat := 4983230072969 + 3 ^ 40 * 1336484 * 2
def baseEnd_1336484 : Nat := 101667952450911738356093

theorem tailTrace_1336484 : CollatzResearch.WordTrace tailWord_1336484 prefixEnd_1336484 101667952450911738356093 := by
  unfold tailWord_1336484
  simp only [CollatzResearch.WordTrace]
  refine ⟨24372788045077098070068253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32497050726769464093424337 24372788045077098070068253)
  ·
    refine ⟨9139795516903911776275595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24372788045077098070068253 9139795516903911776275595)
    ·
      refine ⟨13709693275355867664413393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9139795516903911776275595 13709693275355867664413393)
      ·
        refine ⟨10282269956516900748310045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13709693275355867664413393 10282269956516900748310045)
        ·
          refine ⟨3855851233693837780616267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10282269956516900748310045 3855851233693837780616267)
          ·
            refine ⟨5783776850540756670924401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3855851233693837780616267 5783776850540756670924401)
            ·
              refine ⟨4337832637905567503193301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5783776850540756670924401 4337832637905567503193301)
              ·
                refine ⟨101667952450911738356093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4337832637905567503193301 101667952450911738356093)
                ·
                  rfl

theorem cell21_1336484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 7].length) (baseStart_1336484 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1336484 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1336484 prefixEnd_1336484 := by exact prefixLift 1336484
  have htrace : WordTrace (prefixWord ++ tailWord_1336484) baseStart_1336484 baseEnd_1336484 := by
    simpa [prefixWord, tailWord_1336484, baseEnd_1336484] using wordTrace_append hprefix tailTrace_1336484
  have hstable : (prefixWord ++ tailWord_1336484).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336484).length < 2 ^ (prefixWord ++ tailWord_1336484).sum := by decide
  have hdescent : baseEnd_1336484 < baseStart_1336484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336543 : List Nat := [1, 1, 2, 3, 2, 1, 2, 9]
def baseStart_1336543 : Nat := 118140960795 + 1336543 * 2 ^ 59
def prefixEnd_1336543 : Nat := 4983230072969 + 3 ^ 40 * 1336543 * 2
def baseEnd_1336543 : Nat := 101672440652188074528275

theorem tailTrace_1336543 : CollatzResearch.WordTrace tailWord_1336543 prefixEnd_1336543 101672440652188074528275 := by
  unfold tailWord_1336543
  simp only [CollatzResearch.WordTrace]
  refine ⟨48747727996940449216534283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32498485331293632811022855 48747727996940449216534283)
  ·
    refine ⟨73121591995410673824801425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48747727996940449216534283 73121591995410673824801425)
    ·
      refine ⟨54841193996558005368601069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73121591995410673824801425 54841193996558005368601069)
      ·
        refine ⟨20565447748709252013225401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54841193996558005368601069 20565447748709252013225401)
        ·
          refine ⟨15424085811531939009919051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20565447748709252013225401 15424085811531939009919051)
          ·
            refine ⟨23136128717297908514878577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15424085811531939009919051 23136128717297908514878577)
            ·
              refine ⟨17352096537973431386158933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23136128717297908514878577 17352096537973431386158933)
              ·
                refine ⟨101672440652188074528275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17352096537973431386158933 101672440652188074528275)
                ·
                  rfl

theorem cell21_1336543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 9].length) (baseStart_1336543 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1336543 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1336543 prefixEnd_1336543 := by exact prefixLift 1336543
  have htrace : WordTrace (prefixWord ++ tailWord_1336543) baseStart_1336543 baseEnd_1336543 := by
    simpa [prefixWord, tailWord_1336543, baseEnd_1336543] using wordTrace_append hprefix tailTrace_1336543
  have hstable : (prefixWord ++ tailWord_1336543).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336543).length < 2 ^ (prefixWord ++ tailWord_1336543).sum := by decide
  have hdescent : baseEnd_1336543 < baseStart_1336543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336549 : List Nat := [1, 3, 1, 4, 3, 1, 2, 3, 3]
def baseStart_1336549 : Nat := 118140960795 + 1336549 * 2 ^ 59
def prefixEnd_1336549 : Nat := 4983230072969 + 3 ^ 40 * 1336549 * 2
def baseEnd_1336549 : Nat := 305018691238309546484813

theorem tailTrace_1336549 : CollatzResearch.WordTrace tailWord_1336549 prefixEnd_1336549 305018691238309546484813 := by
  unfold tailWord_1336549
  simp only [CollatzResearch.WordTrace]
  refine ⟨48747946834918712241252701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32498631223279141494168467 48747946834918712241252701)
  ·
    refine ⟨18280480063094517090469763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48747946834918712241252701 18280480063094517090469763)
    ·
      refine ⟨27420720094641775635704645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18280480063094517090469763 27420720094641775635704645)
      ·
        refine ⟨5141385017745332931694621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27420720094641775635704645 5141385017745332931694621)
        ·
          refine ⟨1928019381654499849385483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5141385017745332931694621 1928019381654499849385483)
          ·
            refine ⟨2892029072481749774078225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1928019381654499849385483 2892029072481749774078225)
            ·
              refine ⟨2169021804361312330558669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2892029072481749774078225 2169021804361312330558669)
              ·
                refine ⟨813383176635492123959501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2169021804361312330558669 813383176635492123959501)
                ·
                  refine ⟨305018691238309546484813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 813383176635492123959501 305018691238309546484813)
                  ·
                    rfl

theorem cell21_1336549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 3, 3].length) (baseStart_1336549 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1336549 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1336549 prefixEnd_1336549 := by exact prefixLift 1336549
  have htrace : WordTrace (prefixWord ++ tailWord_1336549) baseStart_1336549 baseEnd_1336549 := by
    simpa [prefixWord, tailWord_1336549, baseEnd_1336549] using wordTrace_append hprefix tailTrace_1336549
  have hstable : (prefixWord ++ tailWord_1336549).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336549).length < 2 ^ (prefixWord ++ tailWord_1336549).sum := by decide
  have hdescent : baseEnd_1336549 < baseStart_1336549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336594 : List Nat := [3, 2, 4, 2, 1, 1, 1, 7]
def baseStart_1336594 : Nat := 118140960795 + 1336594 * 2 ^ 59
def prefixEnd_1336594 : Nat := 4983230072969 + 3 ^ 40 * 1336594 * 2
def baseEnd_1336594 : Nat := 101676320283799822744907

theorem tailTrace_1336594 : CollatzResearch.WordTrace tailWord_1336594 prefixEnd_1336594 101676320283799822744907 := by
  unfold tailWord_1336594
  simp only [CollatzResearch.WordTrace]
  refine ⟨12187397029938921231660209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32499725413170456617760557 12187397029938921231660209)
  ·
    refine ⟨9140547772454190923745157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12187397029938921231660209 9140547772454190923745157)
    ·
      refine ⟨1713852707335160798202217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9140547772454190923745157 1713852707335160798202217)
      ·
        refine ⟨1285389530501370598651663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1713852707335160798202217 1285389530501370598651663)
        ·
          refine ⟨1928084295752055897977495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1285389530501370598651663 1928084295752055897977495)
          ·
            refine ⟨2892126443628083846966243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1928084295752055897977495 2892126443628083846966243)
            ·
              refine ⟨4338189665442125770449365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2892126443628083846966243 4338189665442125770449365)
              ·
                refine ⟨101676320283799822744907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4338189665442125770449365 101676320283799822744907)
                ·
                  rfl

theorem cell21_1336594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 7].length) (baseStart_1336594 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1336594 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1336594 prefixEnd_1336594 := by exact prefixLift 1336594
  have htrace : WordTrace (prefixWord ++ tailWord_1336594) baseStart_1336594 baseEnd_1336594 := by
    simpa [prefixWord, tailWord_1336594, baseEnd_1336594] using wordTrace_append hprefix tailTrace_1336594
  have hstable : (prefixWord ++ tailWord_1336594).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336594).length < 2 ^ (prefixWord ++ tailWord_1336594).sum := by decide
  have hdescent : baseEnd_1336594 < baseStart_1336594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
