import V185TrunkScan23Chunk0399

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2364896 : List Nat := [2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 4]
def baseStart_2364896 : Nat := 118140960795 + 2364896 * 2 ^ 59
def prefixEnd_2364896 : Nat := 4983230072969 + 3 ^ 40 * 2364896 * 2
def baseEnd_2364896 : Nat := 1214328345895284567224047

theorem tailTrace_2364896 : CollatzResearch.WordTrace tailWord_2364896 prefixEnd_2364896 1214328345895284567224047 := by
  unfold tailWord_2364896
  simp only [CollatzResearch.WordTrace]
  refine ⟨43127421620196579463209271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57503228826928772617612361 43127421620196579463209271)
  ·
    refine ⟨64691132430294869194813907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43127421620196579463209271 64691132430294869194813907)
    ·
      refine ⟨97036698645442303792220861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64691132430294869194813907 97036698645442303792220861)
      ·
        refine ⟨36388761992040863922082823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97036698645442303792220861 36388761992040863922082823)
        ·
          refine ⟨54583142988061295883124235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36388761992040863922082823 54583142988061295883124235)
          ·
            refine ⟨81874714482091943824686353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54583142988061295883124235 81874714482091943824686353)
            ·
              refine ⟨61406035861568957868514765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81874714482091943824686353 61406035861568957868514765)
              ·
                refine ⟨23027263448088359200693037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61406035861568957868514765 23027263448088359200693037)
                ·
                  refine ⟨8635223793033134700259889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23027263448088359200693037 8635223793033134700259889)
                  ·
                    refine ⟨6476417844774851025194917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8635223793033134700259889 6476417844774851025194917)
                    ·
                      refine ⟨1214328345895284567224047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6476417844774851025194917 1214328345895284567224047)
                      ·
                        rfl

theorem cell23_2364896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 4].length) (baseStart_2364896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2364896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2364896 prefixEnd_2364896 := by exact prefixLift 2364896
  have htrace : WordTrace (prefixWord ++ tailWord_2364896) baseStart_2364896 baseEnd_2364896 := by
    simpa [prefixWord, tailWord_2364896, baseEnd_2364896] using wordTrace_append hprefix tailTrace_2364896
  have hstable : (prefixWord ++ tailWord_2364896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364896).length < 2 ^ (prefixWord ++ tailWord_2364896).sum := by decide
  have hdescent : baseEnd_2364896 < baseStart_2364896 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364930 : List Nat := [3, 4, 1, 2, 1, 2, 1, 1, 1, 1, 6]
def baseStart_2364930 : Nat := 118140960795 + 2364930 * 2 ^ 59
def prefixEnd_2364930 : Nat := 4983230072969 + 3 ^ 40 * 2364930 * 2
def baseEnd_2364930 : Nat := 1214345804237537434198891

theorem tailTrace_2364930 : CollatzResearch.WordTrace tailWord_2364930 prefixEnd_2364930 1214345804237537434198891 := by
  unfold tailWord_2364930
  simp only [CollatzResearch.WordTrace]
  refine ⟨21564020830567495683289061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57504055548179988488770829 21564020830567495683289061)
  ·
    refine ⟨4043253905731405440616699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21564020830567495683289061 4043253905731405440616699)
    ·
      refine ⟨6064880858597108160925049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4043253905731405440616699 6064880858597108160925049)
      ·
        refine ⟨4548660643947831120693787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6064880858597108160925049 4548660643947831120693787)
        ·
          refine ⟨6822990965921746681040681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4548660643947831120693787 6822990965921746681040681)
          ·
            refine ⟨5117243224441310010780511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6822990965921746681040681 5117243224441310010780511)
            ·
              refine ⟨7675864836661965016170767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5117243224441310010780511 7675864836661965016170767)
              ·
                refine ⟨11513797254992947524256151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7675864836661965016170767 11513797254992947524256151)
                ·
                  refine ⟨17270695882489421286384227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11513797254992947524256151 17270695882489421286384227)
                  ·
                    refine ⟨25906043823734131929576341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17270695882489421286384227 25906043823734131929576341)
                    ·
                      refine ⟨1214345804237537434198891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25906043823734131929576341 1214345804237537434198891)
                      ·
                        rfl

theorem cell23_2364930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_2364930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2364930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2364930 prefixEnd_2364930 := by exact prefixLift 2364930
  have htrace : WordTrace (prefixWord ++ tailWord_2364930) baseStart_2364930 baseEnd_2364930 := by
    simpa [prefixWord, tailWord_2364930, baseEnd_2364930] using wordTrace_append hprefix tailTrace_2364930
  have hstable : (prefixWord ++ tailWord_2364930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364930).length < 2 ^ (prefixWord ++ tailWord_2364930).sum := by decide
  have hdescent : baseEnd_2364930 < baseStart_2364930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364936 : List Nat := [2, 1, 3, 2, 1, 1, 2, 2, 2, 7]
def baseStart_2364936 : Nat := 118140960795 + 2364936 * 2 ^ 59
def prefixEnd_2364936 : Nat := 4983230072969 + 3 ^ 40 * 2364936 * 2
def baseEnd_2364936 : Nat := 404782961707154803574621

theorem tailTrace_2364936 : CollatzResearch.WordTrace tailWord_2364936 prefixEnd_2364936 404782961707154803574621 := by
  unfold tailWord_2364936
  simp only [CollatzResearch.WordTrace]
  refine ⟨43128151080124122878937331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57504201440165497171916441 43128151080124122878937331)
  ·
    refine ⟨64692226620186184318405997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43128151080124122878937331 64692226620186184318405997)
    ·
      refine ⟨24259584982569819119402249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64692226620186184318405997 24259584982569819119402249)
      ·
        refine ⟨18194688736927364339551687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24259584982569819119402249 18194688736927364339551687)
        ·
          refine ⟨27292033105391046509327531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18194688736927364339551687 27292033105391046509327531)
          ·
            refine ⟨40938049658086569763991297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27292033105391046509327531 40938049658086569763991297)
            ·
              refine ⟨30703537243564927322993473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40938049658086569763991297 30703537243564927322993473)
              ·
                refine ⟨23027652932673695492245105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30703537243564927322993473 23027652932673695492245105)
                ·
                  refine ⟨17270739699505271619183829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23027652932673695492245105 17270739699505271619183829)
                  ·
                    refine ⟨404782961707154803574621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17270739699505271619183829 404782961707154803574621)
                    ·
                      rfl

theorem cell23_2364936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 2, 7].length) (baseStart_2364936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2364936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2364936 prefixEnd_2364936 := by exact prefixLift 2364936
  have htrace : WordTrace (prefixWord ++ tailWord_2364936) baseStart_2364936 baseEnd_2364936 := by
    simpa [prefixWord, tailWord_2364936, baseEnd_2364936] using wordTrace_append hprefix tailTrace_2364936
  have hstable : (prefixWord ++ tailWord_2364936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364936).length < 2 ^ (prefixWord ++ tailWord_2364936).sum := by decide
  have hdescent : baseEnd_2364936 < baseStart_2364936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364940 : List Nat := [2, 2, 1, 2, 5, 2, 2, 7]
def baseStart_2364940 : Nat := 118140960795 + 2364940 * 2 ^ 59
def prefixEnd_2364940 : Nat := 4983230072969 + 3 ^ 40 * 2364940 * 2
def baseEnd_2364940 : Nat := 44975960705336385002735

theorem tailTrace_2364940 : CollatzResearch.WordTrace tailWord_2364940 prefixEnd_2364940 44975960705336385002735 := by
  unfold tailWord_2364940
  simp only [CollatzResearch.WordTrace]
  refine ⟨43128224026116877220510137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57504298701489169627346849 43128224026116877220510137)
  ·
    refine ⟨32346168019587657915382603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43128224026116877220510137 32346168019587657915382603)
    ·
      refine ⟨48519252029381486873073905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32346168019587657915382603 48519252029381486873073905)
      ·
        refine ⟨36389439022036115154805429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48519252029381486873073905 36389439022036115154805429)
        ·
          refine ⟨3411509908315885795763009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36389439022036115154805429 3411509908315885795763009)
          ·
            refine ⟨2558632431236914346822257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3411509908315885795763009 2558632431236914346822257)
            ·
              refine ⟨1918974323427685760116693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2558632431236914346822257 1918974323427685760116693)
              ·
                refine ⟨44975960705336385002735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1918974323427685760116693 44975960705336385002735)
                ·
                  rfl

theorem cell23_2364940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 2, 7].length) (baseStart_2364940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2364940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2364940 prefixEnd_2364940 := by exact prefixLift 2364940
  have htrace : WordTrace (prefixWord ++ tailWord_2364940) baseStart_2364940 baseEnd_2364940 := by
    simpa [prefixWord, tailWord_2364940, baseEnd_2364940] using wordTrace_append hprefix tailTrace_2364940
  have hstable : (prefixWord ++ tailWord_2364940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364940).length < 2 ^ (prefixWord ++ tailWord_2364940).sum := by decide
  have hdescent : baseEnd_2364940 < baseStart_2364940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364968 : List Nat := [2, 1, 5, 2, 2, 1, 3, 2, 1, 2, 2]
def baseStart_2364968 : Nat := 118140960795 + 2364968 * 2 ^ 59
def prefixEnd_2364968 : Nat := 4983230072969 + 3 ^ 40 * 2364968 * 2
def baseEnd_2364968 : Nat := 1214365316502408285523717

theorem tailTrace_2364968 : CollatzResearch.WordTrace tailWord_2364968 prefixEnd_2364968 1214365316502408285523717 := by
  unfold tailWord_2364968
  simp only [CollatzResearch.WordTrace]
  refine ⟨43128734648066157611519779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57504979530754876815359705 43128734648066157611519779)
  ·
    refine ⟨64693101972099236417279669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43128734648066157611519779 64693101972099236417279669)
    ·
      refine ⟨6064978309884303414119969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 64693101972099236417279669 6064978309884303414119969)
      ·
        refine ⟨4548733732413227560589977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6064978309884303414119969 4548733732413227560589977)
        ·
          refine ⟨3411550299309920670442483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4548733732413227560589977 3411550299309920670442483)
          ·
            refine ⟨5117325448964881005663725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3411550299309920670442483 5117325448964881005663725)
            ·
              refine ⟨1918997043361830377123897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5117325448964881005663725 1918997043361830377123897)
              ·
                refine ⟨1439247782521372782842923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1918997043361830377123897 1439247782521372782842923)
                ·
                  refine ⟨2158871673782059174264385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1439247782521372782842923 2158871673782059174264385)
                  ·
                    refine ⟨1619153755336544380698289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2158871673782059174264385 1619153755336544380698289)
                    ·
                      refine ⟨1214365316502408285523717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1619153755336544380698289 1214365316502408285523717)
                      ·
                        rfl

theorem cell23_2364968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_2364968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2364968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2364968 prefixEnd_2364968 := by exact prefixLift 2364968
  have htrace : WordTrace (prefixWord ++ tailWord_2364968) baseStart_2364968 baseEnd_2364968 := by
    simpa [prefixWord, tailWord_2364968, baseEnd_2364968] using wordTrace_append hprefix tailTrace_2364968
  have hstable : (prefixWord ++ tailWord_2364968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364968).length < 2 ^ (prefixWord ++ tailWord_2364968).sum := by decide
  have hdescent : baseEnd_2364968 < baseStart_2364968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364976 : List Nat := [2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 5]
def baseStart_2364976 : Nat := 118140960795 + 2364976 * 2 ^ 59
def prefixEnd_2364976 : Nat := 4983230072969 + 3 ^ 40 * 2364976 * 2
def baseEnd_2364976 : Nat := 1214369424347644254223679

theorem tailTrace_2364976 : CollatzResearch.WordTrace tailWord_2364976 prefixEnd_2364976 1214369424347644254223679 := by
  unfold tailWord_2364976
  simp only [CollatzResearch.WordTrace]
  refine ⟨43128880540051666294665391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57505174053402221726220521 43128880540051666294665391)
  ·
    refine ⟨64693320810077499441998087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43128880540051666294665391 64693320810077499441998087)
    ·
      refine ⟨97039981215116249162997131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64693320810077499441998087 97039981215116249162997131)
      ·
        refine ⟨145559971822674373744495697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97039981215116249162997131 145559971822674373744495697)
        ·
          refine ⟨109169978867005780308371773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145559971822674373744495697 109169978867005780308371773)
          ·
            refine ⟨40938742075127167615639415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109169978867005780308371773 40938742075127167615639415)
            ·
              refine ⟨61408113112690751423459123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40938742075127167615639415 61408113112690751423459123)
              ·
                refine ⟨92112169669036127135188685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61408113112690751423459123 92112169669036127135188685)
                ·
                  refine ⟨34542063625888547675695757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 92112169669036127135188685 34542063625888547675695757)
                  ·
                    refine ⟨12953273859708205378385909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34542063625888547675695757 12953273859708205378385909)
                    ·
                      refine ⟨1214369424347644254223679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12953273859708205378385909 1214369424347644254223679)
                      ·
                        rfl

theorem cell23_2364976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 5].length) (baseStart_2364976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2364976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2364976 prefixEnd_2364976 := by exact prefixLift 2364976
  have htrace : WordTrace (prefixWord ++ tailWord_2364976) baseStart_2364976 baseEnd_2364976 := by
    simpa [prefixWord, tailWord_2364976, baseEnd_2364976] using wordTrace_append hprefix tailTrace_2364976
  have hstable : (prefixWord ++ tailWord_2364976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364976).length < 2 ^ (prefixWord ++ tailWord_2364976).sum := by decide
  have hdescent : baseEnd_2364976 < baseStart_2364976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364984 : List Nat := [2, 1, 2, 1, 4, 4, 2, 1, 2, 1, 3]
def baseStart_2364984 : Nat := 118140960795 + 2364984 * 2 ^ 59
def prefixEnd_2364984 : Nat := 4983230072969 + 3 ^ 40 * 2364984 * 2
def baseEnd_2364984 : Nat := 1214373532192880222923643

theorem tailTrace_2364984 : CollatzResearch.WordTrace tailWord_2364984 prefixEnd_2364984 1214373532192880222923643 := by
  unfold tailWord_2364984
  simp only [CollatzResearch.WordTrace]
  refine ⟨43129026432037174977811003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57505368576049566637081337 43129026432037174977811003)
  ·
    refine ⟨64693539648055762466716505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43129026432037174977811003 64693539648055762466716505)
    ·
      refine ⟨48520154736041821850037379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64693539648055762466716505 48520154736041821850037379)
      ·
        refine ⟨72780232104062732775056069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48520154736041821850037379 72780232104062732775056069)
        ·
          refine ⟨13646293519511762395323013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72780232104062732775056069 13646293519511762395323013)
          ·
            refine ⟨2558680034908455449123065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13646293519511762395323013 2558680034908455449123065)
            ·
              refine ⟨1919010026181341586842299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2558680034908455449123065 1919010026181341586842299)
              ·
                refine ⟨2878515039272012380263449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1919010026181341586842299 2878515039272012380263449)
                ·
                  refine ⟨2158886279454009285197587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2878515039272012380263449 2158886279454009285197587)
                  ·
                    refine ⟨3238329419181013927796381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2158886279454009285197587 3238329419181013927796381)
                    ·
                      refine ⟨1214373532192880222923643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3238329419181013927796381 1214373532192880222923643)
                      ·
                        rfl

theorem cell23_2364984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 2, 1, 2, 1, 3].length) (baseStart_2364984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2364984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2364984 prefixEnd_2364984 := by exact prefixLift 2364984
  have htrace : WordTrace (prefixWord ++ tailWord_2364984) baseStart_2364984 baseEnd_2364984 := by
    simpa [prefixWord, tailWord_2364984, baseEnd_2364984] using wordTrace_append hprefix tailTrace_2364984
  have hstable : (prefixWord ++ tailWord_2364984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364984).length < 2 ^ (prefixWord ++ tailWord_2364984).sum := by decide
  have hdescent : baseEnd_2364984 < baseStart_2364984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364993 : List Nat := [1, 2, 5, 1, 1, 1, 1, 1, 4, 1, 5]
def baseStart_2364993 : Nat := 118140960795 + 2364993 * 2 ^ 59
def prefixEnd_2364993 : Nat := 4983230072969 + 3 ^ 40 * 2364993 * 2
def baseEnd_2364993 : Nat := 1214378153518770687711101

theorem tailTrace_2364993 : CollatzResearch.WordTrace tailWord_2364993 prefixEnd_2364993 1214378153518770687711101 := by
  unfold tailWord_2364993
  simp only [CollatzResearch.WordTrace]
  refine ⟨86258381121041744492699633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57505587414027829661799755 86258381121041744492699633)
  ·
    refine ⟨64693785840781308369524725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86258381121041744492699633 64693785840781308369524725)
    ·
      refine ⟨6065042422573247659642943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 64693785840781308369524725 6065042422573247659642943)
      ·
        refine ⟨9097563633859871489464415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6065042422573247659642943 9097563633859871489464415)
        ·
          refine ⟨13646345450789807234196623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9097563633859871489464415 13646345450789807234196623)
          ·
            refine ⟨20469518176184710851294935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13646345450789807234196623 20469518176184710851294935)
            ·
              refine ⟨30704277264277066276942403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20469518176184710851294935 30704277264277066276942403)
              ·
                refine ⟨46056415896415599415413605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30704277264277066276942403 46056415896415599415413605)
                ·
                  refine ⟨8635577980577924890390051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46056415896415599415413605 8635577980577924890390051)
                  ·
                    refine ⟨12953366970866887335585077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8635577980577924890390051 12953366970866887335585077)
                    ·
                      refine ⟨1214378153518770687711101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12953366970866887335585077 1214378153518770687711101)
                      ·
                        rfl

theorem cell23_2364993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_2364993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2364993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2364993 prefixEnd_2364993 := by exact prefixLift 2364993
  have htrace : WordTrace (prefixWord ++ tailWord_2364993) baseStart_2364993 baseEnd_2364993 := by
    simpa [prefixWord, tailWord_2364993, baseEnd_2364993] using wordTrace_append hprefix tailTrace_2364993
  have hstable : (prefixWord ++ tailWord_2364993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364993).length < 2 ^ (prefixWord ++ tailWord_2364993).sum := by decide
  have hdescent : baseEnd_2364993 < baseStart_2364993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2365040 : List Nat := [2, 1, 1, 1, 6, 2, 1, 1, 2, 3, 3]
def baseStart_2365040 : Nat := 118140960795 + 2365040 * 2 ^ 59
def prefixEnd_2365040 : Nat := 4983230072969 + 3 ^ 40 * 2365040 * 2
def baseEnd_2365040 : Nat := 1214402287109532003823385

theorem tailTrace_2365040 : CollatzResearch.WordTrace tailWord_2365040 prefixEnd_2365040 1214402287109532003823385 := by
  unfold tailWord_2365040
  simp only [CollatzResearch.WordTrace]
  refine ⟨43130047675935735759830287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57506730234580981013107049 43130047675935735759830287)
  ·
    refine ⟨64695071513903603639745431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43130047675935735759830287 64695071513903603639745431)
    ·
      refine ⟨97042607270855405459618147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64695071513903603639745431 97042607270855405459618147)
      ·
        refine ⟨145563910906283108189427221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97042607270855405459618147 145563910906283108189427221)
        ·
          refine ⟨6823308323732020696379401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 145563910906283108189427221 6823308323732020696379401)
          ·
            refine ⟨5117481242799015522284551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6823308323732020696379401 5117481242799015522284551)
            ·
              refine ⟨7676221864198523283426827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5117481242799015522284551 7676221864198523283426827)
              ·
                refine ⟨11514332796297784925140241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7676221864198523283426827 11514332796297784925140241)
                ·
                  refine ⟨8635749597223338693855181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11514332796297784925140241 8635749597223338693855181)
                  ·
                    refine ⟨3238406098958752010195693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8635749597223338693855181 3238406098958752010195693)
                    ·
                      refine ⟨1214402287109532003823385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3238406098958752010195693 1214402287109532003823385)
                      ·
                        rfl

theorem cell23_2365040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 1, 2, 3, 3].length) (baseStart_2365040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2365040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2365040 prefixEnd_2365040 := by exact prefixLift 2365040
  have htrace : WordTrace (prefixWord ++ tailWord_2365040) baseStart_2365040 baseEnd_2365040 := by
    simpa [prefixWord, tailWord_2365040, baseEnd_2365040] using wordTrace_append hprefix tailTrace_2365040
  have hstable : (prefixWord ++ tailWord_2365040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2365040).length < 2 ^ (prefixWord ++ tailWord_2365040).sum := by decide
  have hdescent : baseEnd_2365040 < baseStart_2365040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2365040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2365060 : List Nat := [2, 3, 2, 1, 4, 1, 1, 1, 1, 7]
def baseStart_2365060 : Nat := 118140960795 + 2365060 * 2 ^ 59
def prefixEnd_2365060 : Nat := 4983230072969 + 3 ^ 40 * 2365060 * 2
def baseEnd_2365060 : Nat := 404804185574207308524431

theorem tailTrace_2365060 : CollatzResearch.WordTrace tailWord_2365060 prefixEnd_2365060 404804185574207308524431 := by
  unfold tailWord_2365060
  simp only [CollatzResearch.WordTrace]
  refine ⟨43130412405899507467694317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57507216541199343290259089 43130412405899507467694317)
  ·
    refine ⟨16173904652212315300385369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43130412405899507467694317 16173904652212315300385369)
    ·
      refine ⟨12130428489159236475289027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16173904652212315300385369 12130428489159236475289027)
      ·
        refine ⟨18195642733738854712933541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12130428489159236475289027 18195642733738854712933541)
        ·
          refine ⟨3411683012576035258675039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18195642733738854712933541 3411683012576035258675039)
          ·
            refine ⟨5117524518864052888012559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3411683012576035258675039 5117524518864052888012559)
            ·
              refine ⟨7676286778296079332018839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5117524518864052888012559 7676286778296079332018839)
              ·
                refine ⟨11514430167444118998028259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7676286778296079332018839 11514430167444118998028259)
                ·
                  refine ⟨17271645251166178497042389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11514430167444118998028259 17271645251166178497042389)
                  ·
                    refine ⟨404804185574207308524431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17271645251166178497042389 404804185574207308524431)
                    ·
                      rfl

theorem cell23_2365060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 1, 1, 7].length) (baseStart_2365060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2365060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2365060 prefixEnd_2365060 := by exact prefixLift 2365060
  have htrace : WordTrace (prefixWord ++ tailWord_2365060) baseStart_2365060 baseEnd_2365060 := by
    simpa [prefixWord, tailWord_2365060, baseEnd_2365060] using wordTrace_append hprefix tailTrace_2365060
  have hstable : (prefixWord ++ tailWord_2365060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2365060).length < 2 ^ (prefixWord ++ tailWord_2365060).sum := by decide
  have hdescent : baseEnd_2365060 < baseStart_2365060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2365060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2365064 : List Nat := [2, 1, 3, 5, 1, 1, 2, 3, 5]
def baseStart_2365064 : Nat := 118140960795 + 2365064 * 2 ^ 59
def prefixEnd_2365064 : Nat := 4983230072969 + 3 ^ 40 * 2365064 * 2
def baseEnd_2365064 : Nat := 134934956738359989991475

theorem tailTrace_2365064 : CollatzResearch.WordTrace tailWord_2365064 prefixEnd_2365064 134934956738359989991475 := by
  unfold tailWord_2365064
  simp only [CollatzResearch.WordTrace]
  refine ⟨43130485351892261809267123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57507313802523015745689497 43130485351892261809267123)
  ·
    refine ⟨64695728027838392713900685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43130485351892261809267123 64695728027838392713900685)
    ·
      refine ⟨24260898010439397267712757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64695728027838392713900685 24260898010439397267712757)
      ·
        refine ⟨2274459188478693493848071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24260898010439397267712757 2274459188478693493848071)
        ·
          refine ⟨3411688782718040240772107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2274459188478693493848071 3411688782718040240772107)
          ·
            refine ⟨5117533174077060361158161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3411688782718040240772107 5117533174077060361158161)
            ·
              refine ⟨3838149880557795270868621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5117533174077060361158161 3838149880557795270868621)
              ·
                refine ⟨1439306205209173226575733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3838149880557795270868621 1439306205209173226575733)
                ·
                  refine ⟨134934956738359989991475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1439306205209173226575733 134934956738359989991475)
                  ·
                    rfl

theorem cell23_2365064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 3, 5].length) (baseStart_2365064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2365064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2365064 prefixEnd_2365064 := by exact prefixLift 2365064
  have htrace : WordTrace (prefixWord ++ tailWord_2365064) baseStart_2365064 baseEnd_2365064 := by
    simpa [prefixWord, tailWord_2365064, baseEnd_2365064] using wordTrace_append hprefix tailTrace_2365064
  have hstable : (prefixWord ++ tailWord_2365064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2365064).length < 2 ^ (prefixWord ++ tailWord_2365064).sum := by decide
  have hdescent : baseEnd_2365064 < baseStart_2365064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2365064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2365157 : List Nat := [1, 3, 1, 4, 1, 1, 1, 2, 4, 3, 2]
def baseStart_2365157 : Nat := 118140960795 + 2365157 * 2 ^ 59
def prefixEnd_2365157 : Nat := 4983230072969 + 3 ^ 40 * 2365157 * 2
def baseEnd_2365157 : Nat := 1214462364346108046060347

theorem tailTrace_2365157 : CollatzResearch.WordTrace tailWord_2365157 prefixEnd_2365157 1214462364346108046060347 := by
  unfold tailWord_2365157
  simp only [CollatzResearch.WordTrace]
  refine ⟨86264362692447600501669725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57509575128298400334446483 86264362692447600501669725)
  ·
    refine ⟨32349136009667850188126147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86264362692447600501669725 32349136009667850188126147)
    ·
      refine ⟨48523704014501775282189221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32349136009667850188126147 48523704014501775282189221)
      ·
        refine ⟨9098194502719082865410479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48523704014501775282189221 9098194502719082865410479)
        ·
          refine ⟨13647291754078624298115719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9098194502719082865410479 13647291754078624298115719)
          ·
            refine ⟨20470937631117936447173579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13647291754078624298115719 20470937631117936447173579)
            ·
              refine ⟨30706406446676904670760369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20470937631117936447173579 30706406446676904670760369)
              ·
                refine ⟨23029804835007678503070277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30706406446676904670760369 23029804835007678503070277)
                ·
                  refine ⟨4318088406563939719325677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23029804835007678503070277 4318088406563939719325677)
                  ·
                    refine ⟨1619283152461477394747129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4318088406563939719325677 1619283152461477394747129)
                    ·
                      refine ⟨1214462364346108046060347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1619283152461477394747129 1214462364346108046060347)
                      ·
                        rfl

theorem cell23_2365157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 4, 3, 2].length) (baseStart_2365157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2365157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2365157 prefixEnd_2365157 := by exact prefixLift 2365157
  have htrace : WordTrace (prefixWord ++ tailWord_2365157) baseStart_2365157 baseEnd_2365157 := by
    simpa [prefixWord, tailWord_2365157, baseEnd_2365157] using wordTrace_append hprefix tailTrace_2365157
  have hstable : (prefixWord ++ tailWord_2365157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2365157).length < 2 ^ (prefixWord ++ tailWord_2365157).sum := by decide
  have hdescent : baseEnd_2365157 < baseStart_2365157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2365157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2365174 : List Nat := [5, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2]
def baseStart_2365174 : Nat := 118140960795 + 2365174 * 2 ^ 59
def prefixEnd_2365174 : Nat := 4983230072969 + 3 ^ 40 * 2365174 * 2
def baseEnd_2365174 : Nat := 1214471093517234479547769

theorem tailTrace_2365174 : CollatzResearch.WordTrace tailWord_2365174 prefixEnd_2365174 1214471093517234479547769 := by
  unfold tailWord_2365174
  simp only [CollatzResearch.WordTrace]
  refine ⟨5391561420836625775314911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57509988488924008270025717 5391561420836625775314911)
  ·
    refine ⟨8087342131254938662972367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5391561420836625775314911 8087342131254938662972367)
    ·
      refine ⟨12131013196882407994458551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8087342131254938662972367 12131013196882407994458551)
      ·
        refine ⟨18196519795323611991687827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12131013196882407994458551 18196519795323611991687827)
        ·
          refine ⟨27294779692985417987531741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18196519795323611991687827 27294779692985417987531741)
          ·
            refine ⟨10235542384869531745324403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27294779692985417987531741 10235542384869531745324403)
            ·
              refine ⟨15353313577304297617986605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10235542384869531745324403 15353313577304297617986605)
              ·
                refine ⟨5757492591489111606744977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15353313577304297617986605 5757492591489111606744977)
                ·
                  refine ⟨4318119443616833705058733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5757492591489111606744977 4318119443616833705058733)
                  ·
                    refine ⟨1619294791356312639397025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4318119443616833705058733 1619294791356312639397025)
                    ·
                      refine ⟨1214471093517234479547769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1619294791356312639397025 1214471093517234479547769)
                      ·
                        rfl

theorem cell23_2365174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2].length) (baseStart_2365174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2365174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2365174 prefixEnd_2365174 := by exact prefixLift 2365174
  have htrace : WordTrace (prefixWord ++ tailWord_2365174) baseStart_2365174 baseEnd_2365174 := by
    simpa [prefixWord, tailWord_2365174, baseEnd_2365174] using wordTrace_append hprefix tailTrace_2365174
  have hstable : (prefixWord ++ tailWord_2365174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2365174).length < 2 ^ (prefixWord ++ tailWord_2365174).sum := by decide
  have hdescent : baseEnd_2365174 < baseStart_2365174 := by decide
  rcases family_descends (prefixWord ++ tailWord_2365174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2365180 : List Nat := [2, 2, 2, 1, 3, 1, 3, 2, 1, 6]
def baseStart_2365180 : Nat := 118140960795 + 2365180 * 2 ^ 59
def prefixEnd_2365180 : Nat := 4983230072969 + 3 ^ 40 * 2365180 * 2
def baseEnd_2365180 : Nat := 404824724800387152024247

theorem tailTrace_2365180 : CollatzResearch.WordTrace tailWord_2365180 prefixEnd_2365180 404824724800387152024247 := by
  unfold tailWord_2365180
  simp only [CollatzResearch.WordTrace]
  refine ⟨43132600785682137714878497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57510134380909516953171329 43132600785682137714878497)
  ·
    refine ⟨32349450589261603286158873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43132600785682137714878497 32349450589261603286158873)
    ·
      refine ⟨24262087941946202464619155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32349450589261603286158873 24262087941946202464619155)
      ·
        refine ⟨36393131912919303696928733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24262087941946202464619155 36393131912919303696928733)
        ·
          refine ⟨13647424467344738886348275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36393131912919303696928733 13647424467344738886348275)
          ·
            refine ⟨20471136701017108329522413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13647424467344738886348275 20471136701017108329522413)
            ·
              refine ⟨7676676262881415623570905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20471136701017108329522413 7676676262881415623570905)
              ·
                refine ⟨5757507197161061717678179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7676676262881415623570905 5757507197161061717678179)
                ·
                  refine ⟨8636260795741592576517269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5757507197161061717678179 8636260795741592576517269)
                  ·
                    refine ⟨404824724800387152024247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8636260795741592576517269 404824724800387152024247)
                    ·
                      rfl

theorem cell23_2365180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 2, 1, 6].length) (baseStart_2365180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2365180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2365180 prefixEnd_2365180 := by exact prefixLift 2365180
  have htrace : WordTrace (prefixWord ++ tailWord_2365180) baseStart_2365180 baseEnd_2365180 := by
    simpa [prefixWord, tailWord_2365180, baseEnd_2365180] using wordTrace_append hprefix tailTrace_2365180
  have hstable : (prefixWord ++ tailWord_2365180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2365180).length < 2 ^ (prefixWord ++ tailWord_2365180).sum := by decide
  have hdescent : baseEnd_2365180 < baseStart_2365180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2365180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2365203 : List Nat := [1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 7]
def baseStart_2365203 : Nat := 118140960795 + 2365203 * 2 ^ 59
def prefixEnd_2365203 : Nat := 4983230072969 + 3 ^ 40 * 2365203 * 2
def baseEnd_2365203 : Nat := 1214485984456214866085135

theorem tailTrace_2365203 : CollatzResearch.WordTrace tailWord_2365203 prefixEnd_2365203 1214485984456214866085135 := by
  unfold tailWord_2365203
  simp only [CollatzResearch.WordTrace]
  refine ⟨86266040450280950357844263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57510693633520633571896175 86266040450280950357844263)
  ·
    refine ⟨129399060675421425536766395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86266040450280950357844263 129399060675421425536766395)
    ·
      refine ⟨194098591013132138305149593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129399060675421425536766395 194098591013132138305149593)
      ·
        refine ⟨145573943259849103728862195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194098591013132138305149593 145573943259849103728862195)
        ·
          refine ⟨218360914889773655593293293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145573943259849103728862195 218360914889773655593293293)
          ·
            refine ⟨81885343083665120847484985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 218360914889773655593293293 81885343083665120847484985)
            ·
              refine ⟨61414007312748840635613739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81885343083665120847484985 61414007312748840635613739)
              ·
                refine ⟨92121010969123260953420609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61414007312748840635613739 92121010969123260953420609)
                ·
                  refine ⟨69090758226842445715065457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 92121010969123260953420609 69090758226842445715065457)
                  ·
                    refine ⟨51818068670131834286299093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 69090758226842445715065457 51818068670131834286299093)
                    ·
                      refine ⟨1214485984456214866085135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 51818068670131834286299093 1214485984456214866085135)
                      ·
                        rfl

theorem cell23_2365203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 7].length) (baseStart_2365203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2365203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2365203 prefixEnd_2365203 := by exact prefixLift 2365203
  have htrace : WordTrace (prefixWord ++ tailWord_2365203) baseStart_2365203 baseEnd_2365203 := by
    simpa [prefixWord, tailWord_2365203, baseEnd_2365203] using wordTrace_append hprefix tailTrace_2365203
  have hstable : (prefixWord ++ tailWord_2365203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2365203).length < 2 ^ (prefixWord ++ tailWord_2365203).sum := by decide
  have hdescent : baseEnd_2365203 < baseStart_2365203 := by decide
  rcases family_descends (prefixWord ++ tailWord_2365203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2365207 : List Nat := [1, 1, 3, 4, 2, 1, 1, 2, 3, 2, 3]
def baseStart_2365207 : Nat := 118140960795 + 2365207 * 2 ^ 59
def prefixEnd_2365207 : Nat := 4983230072969 + 3 ^ 40 * 2365207 * 2
def baseEnd_2365207 : Nat := 1214488038378832850435117

theorem tailTrace_2365207 : CollatzResearch.WordTrace tailWord_2365207 prefixEnd_2365207 1214488038378832850435117 := by
  unfold tailWord_2365207
  simp only [CollatzResearch.WordTrace]
  refine ⟨86266186342266459040989875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57510790894844306027326583 86266186342266459040989875)
  ·
    refine ⟨129399279513399688561484813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86266186342266459040989875 129399279513399688561484813)
    ·
      refine ⟨48524729817524883210556805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129399279513399688561484813 48524729817524883210556805)
      ·
        refine ⟨9098386840785915601979401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48524729817524883210556805 9098386840785915601979401)
        ·
          refine ⟨6823790130589436701484551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9098386840785915601979401 6823790130589436701484551)
          ·
            refine ⟨10235685195884155052226827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6823790130589436701484551 10235685195884155052226827)
            ·
              refine ⟨15353527793826232578340241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10235685195884155052226827 15353527793826232578340241)
              ·
                refine ⟨11515145845369674433755181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15353527793826232578340241 11515145845369674433755181)
                ·
                  refine ⟨4318179692013627912658193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11515145845369674433755181 4318179692013627912658193)
                  ·
                    refine ⟨3238634769010220934493645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4318179692013627912658193 3238634769010220934493645)
                    ·
                      refine ⟨1214488038378832850435117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3238634769010220934493645 1214488038378832850435117)
                      ·
                        rfl

theorem cell23_2365207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_2365207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2365207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2365207 prefixEnd_2365207 := by exact prefixLift 2365207
  have htrace : WordTrace (prefixWord ++ tailWord_2365207) baseStart_2365207 baseEnd_2365207 := by
    simpa [prefixWord, tailWord_2365207, baseEnd_2365207] using wordTrace_append hprefix tailTrace_2365207
  have hstable : (prefixWord ++ tailWord_2365207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2365207).length < 2 ^ (prefixWord ++ tailWord_2365207).sum := by decide
  have hdescent : baseEnd_2365207 < baseStart_2365207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2365207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2365210 : List Nat := [3, 1, 1, 3, 2, 2, 3, 8]
def baseStart_2365210 : Nat := 118140960795 + 2365210 * 2 ^ 59
def prefixEnd_2365210 : Nat := 4983230072969 + 3 ^ 40 * 2365210 * 2
def baseEnd_2365210 : Nat := 44981095511881345877689

theorem tailTrace_2365210 : CollatzResearch.WordTrace tailWord_2365210 prefixEnd_2365210 44981095511881345877689 := by
  unfold tailWord_2365210
  simp only [CollatzResearch.WordTrace]
  refine ⟨21566573940313897638337271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57510863840837060368899389 21566573940313897638337271)
  ·
    refine ⟨32349860910470846457505907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21566573940313897638337271 32349860910470846457505907)
    ·
      refine ⟨48524791365706269686258861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32349860910470846457505907 48524791365706269686258861)
      ·
        refine ⟨18196796762139851132347073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48524791365706269686258861 18196796762139851132347073)
        ·
          refine ⟨13647597571604888349260305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18196796762139851132347073 13647597571604888349260305)
          ·
            refine ⟨10235698178703666261945229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13647597571604888349260305 10235698178703666261945229)
            ·
              refine ⟨3838386817013874848229461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10235698178703666261945229 3838386817013874848229461)
              ·
                refine ⟨44981095511881345877689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3838386817013874848229461 44981095511881345877689)
                ·
                  rfl

theorem cell23_2365210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 8].length) (baseStart_2365210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2365210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2365210 prefixEnd_2365210 := by exact prefixLift 2365210
  have htrace : WordTrace (prefixWord ++ tailWord_2365210) baseStart_2365210 baseEnd_2365210 := by
    simpa [prefixWord, tailWord_2365210, baseEnd_2365210] using wordTrace_append hprefix tailTrace_2365210
  have hstable : (prefixWord ++ tailWord_2365210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2365210).length < 2 ^ (prefixWord ++ tailWord_2365210).sum := by decide
  have hdescent : baseEnd_2365210 < baseStart_2365210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2365210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2365217 : List Nat := [1, 2, 3, 2, 1, 4, 2, 1, 1, 2, 4]
def baseStart_2365217 : Nat := 118140960795 + 2365217 * 2 ^ 59
def prefixEnd_2365217 : Nat := 4983230072969 + 3 ^ 40 * 2365217 * 2
def baseEnd_2365217 : Nat := 1214493173185377811310071

theorem tailTrace_2365217 : CollatzResearch.WordTrace tailWord_2365217 prefixEnd_2365217 1214493173185377811310071 := by
  unfold tailWord_2365217
  simp only [CollatzResearch.WordTrace]
  refine ⟨86266551072230230748853905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57511034048153487165902603 86266551072230230748853905)
  ·
    refine ⟨64699913304172673061640429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86266551072230230748853905 64699913304172673061640429)
    ·
      refine ⟨24262467489064752398115161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64699913304172673061640429 24262467489064752398115161)
      ·
        refine ⟨18196850616798564298586371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24262467489064752398115161 18196850616798564298586371)
        ·
          refine ⟨27295275925197846447879557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18196850616798564298586371 27295275925197846447879557)
          ·
            refine ⟨5117864235974596208977417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27295275925197846447879557 5117864235974596208977417)
            ·
              refine ⟨3838398176980947156733063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5117864235974596208977417 3838398176980947156733063)
              ·
                refine ⟨5757597265471420735099595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3838398176980947156733063 5757597265471420735099595)
                ·
                  refine ⟨8636395898207131102649393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5757597265471420735099595 8636395898207131102649393)
                  ·
                    refine ⟨6477296923655348326987045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8636395898207131102649393 6477296923655348326987045)
                    ·
                      refine ⟨1214493173185377811310071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6477296923655348326987045 1214493173185377811310071)
                      ·
                        rfl

theorem cell23_2365217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 1, 1, 2, 4].length) (baseStart_2365217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2365217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2365217 prefixEnd_2365217 := by exact prefixLift 2365217
  have htrace : WordTrace (prefixWord ++ tailWord_2365217) baseStart_2365217 baseEnd_2365217 := by
    simpa [prefixWord, tailWord_2365217, baseEnd_2365217] using wordTrace_append hprefix tailTrace_2365217
  have hstable : (prefixWord ++ tailWord_2365217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2365217).length < 2 ^ (prefixWord ++ tailWord_2365217).sum := by decide
  have hdescent : baseEnd_2365217 < baseStart_2365217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2365217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2365238 : List Nat := [5, 1, 2, 2, 1, 3, 2, 1, 1, 1, 4]
def baseStart_2365238 : Nat := 118140960795 + 2365238 * 2 ^ 59
def prefixEnd_2365238 : Nat := 4983230072969 + 3 ^ 40 * 2365238 * 2
def baseEnd_2365238 : Nat := 1214503956279122229147475

theorem tailTrace_2365238 : CollatzResearch.WordTrace tailWord_2365238 prefixEnd_2365238 1214503956279122229147475 := by
  unfold tailWord_2365238
  simp only [CollatzResearch.WordTrace]
  refine ⟨5391707312822134458460523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57511544670102767556912245 5391707312822134458460523)
  ·
    refine ⟨8087560969233201687690785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5391707312822134458460523 8087560969233201687690785)
    ·
      refine ⟨6065670726924901265768089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8087560969233201687690785 6065670726924901265768089)
      ·
        refine ⟨4549253045193675949326067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6065670726924901265768089 4549253045193675949326067)
        ·
          refine ⟨6823879567790513923989101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4549253045193675949326067 6823879567790513923989101)
          ·
            refine ⟨2558954837921442721495913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6823879567790513923989101 2558954837921442721495913)
            ·
              refine ⟨1919216128441082041121935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2558954837921442721495913 1919216128441082041121935)
              ·
                refine ⟨2878824192661623061682903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1919216128441082041121935 2878824192661623061682903)
                ·
                  refine ⟨4318236288992434592524355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2878824192661623061682903 4318236288992434592524355)
                  ·
                    refine ⟨6477354433488651888786533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4318236288992434592524355 6477354433488651888786533)
                    ·
                      refine ⟨1214503956279122229147475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6477354433488651888786533 1214503956279122229147475)
                      ·
                        rfl

theorem cell23_2365238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_2365238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2365238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2365238 prefixEnd_2365238 := by exact prefixLift 2365238
  have htrace : WordTrace (prefixWord ++ tailWord_2365238) baseStart_2365238 baseEnd_2365238 := by
    simpa [prefixWord, tailWord_2365238, baseEnd_2365238] using wordTrace_append hprefix tailTrace_2365238
  have hstable : (prefixWord ++ tailWord_2365238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2365238).length < 2 ^ (prefixWord ++ tailWord_2365238).sum := by decide
  have hdescent : baseEnd_2365238 < baseStart_2365238 := by decide
  rcases family_descends (prefixWord ++ tailWord_2365238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2365241 : List Nat := [1, 2, 1, 7, 1, 1, 1, 3, 1, 2, 3]
def baseStart_2365241 : Nat := 118140960795 + 2365241 * 2 ^ 59
def prefixEnd_2365241 : Nat := 4983230072969 + 3 ^ 40 * 2365241 * 2
def baseEnd_2365241 : Nat := 1214505496721085717409961

theorem tailTrace_2365241 : CollatzResearch.WordTrace tailWord_2365241 prefixEnd_2365241 1214505496721085717409961 := by
  unfold tailWord_2365241
  simp only [CollatzResearch.WordTrace]
  refine ⟨86267426424143282847727577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57511617616095521898485051 86267426424143282847727577)
  ·
    refine ⟨64700569818107462135795683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86267426424143282847727577 64700569818107462135795683)
    ·
      refine ⟨97050854727161193203693525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64700569818107462135795683 97050854727161193203693525)
      ·
        refine ⟨2274629407667840465711567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 97050854727161193203693525 2274629407667840465711567)
        ·
          refine ⟨3411944111501760698567351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2274629407667840465711567 3411944111501760698567351)
          ·
            refine ⟨5117916167252641047851027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3411944111501760698567351 5117916167252641047851027)
            ·
              refine ⟨7676874250878961571776541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5117916167252641047851027 7676874250878961571776541)
              ·
                refine ⟨2878827844079610589416203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7676874250878961571776541 2878827844079610589416203)
                ·
                  refine ⟨4318241766119415884124305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2878827844079610589416203 4318241766119415884124305)
                  ·
                    refine ⟨3238681324589561913093229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4318241766119415884124305 3238681324589561913093229)
                    ·
                      refine ⟨1214505496721085717409961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3238681324589561913093229 1214505496721085717409961)
                      ·
                        rfl

theorem cell23_2365241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_2365241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2365241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2365241 prefixEnd_2365241 := by exact prefixLift 2365241
  have htrace : WordTrace (prefixWord ++ tailWord_2365241) baseStart_2365241 baseEnd_2365241 := by
    simpa [prefixWord, tailWord_2365241, baseEnd_2365241] using wordTrace_append hprefix tailTrace_2365241
  have hstable : (prefixWord ++ tailWord_2365241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2365241).length < 2 ^ (prefixWord ++ tailWord_2365241).sum := by decide
  have hdescent : baseEnd_2365241 < baseStart_2365241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2365241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2365271 : List Nat := [1, 1, 3, 2, 6, 1, 1, 1, 1, 3, 3]
def baseStart_2365271 : Nat := 118140960795 + 2365271 * 2 ^ 59
def prefixEnd_2365271 : Nat := 4983230072969 + 3 ^ 40 * 2365271 * 2
def baseEnd_2365271 : Nat := 1214520901140720600034823

theorem tailTrace_2365271 : CollatzResearch.WordTrace tailWord_2365271 prefixEnd_2365271 1214520901140720600034823 := by
  unfold tailWord_2365271
  simp only [CollatzResearch.WordTrace]
  refine ⟨86268520614034597971319667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57512347076023065314213111 86268520614034597971319667)
  ·
    refine ⟨129402780921051896956979501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86268520614034597971319667 129402780921051896956979501)
    ·
      refine ⟨48526042845394461358867313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129402780921051896956979501 48526042845394461358867313)
      ·
        refine ⟨36394532134045846019150485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48526042845394461358867313 36394532134045846019150485)
        ·
          refine ⟨1705993693783399032147679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 36394532134045846019150485 1705993693783399032147679)
          ·
            refine ⟨2558990540675098548221519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1705993693783399032147679 2558990540675098548221519)
            ·
              refine ⟨3838485811012647822332279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2558990540675098548221519 3838485811012647822332279)
              ·
                refine ⟨5757728716518971733498419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3838485811012647822332279 5757728716518971733498419)
                ·
                  refine ⟨8636593074778457600247629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5757728716518971733498419 8636593074778457600247629)
                  ·
                    refine ⟨3238722403041921600092861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8636593074778457600247629 3238722403041921600092861)
                    ·
                      refine ⟨1214520901140720600034823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3238722403041921600092861 1214520901140720600034823)
                      ·
                        rfl

theorem cell23_2365271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 1, 1, 3, 3].length) (baseStart_2365271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2365271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2365271 prefixEnd_2365271 := by exact prefixLift 2365271
  have htrace : WordTrace (prefixWord ++ tailWord_2365271) baseStart_2365271 baseEnd_2365271 := by
    simpa [prefixWord, tailWord_2365271, baseEnd_2365271] using wordTrace_append hprefix tailTrace_2365271
  have hstable : (prefixWord ++ tailWord_2365271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2365271).length < 2 ^ (prefixWord ++ tailWord_2365271).sum := by decide
  have hdescent : baseEnd_2365271 < baseStart_2365271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2365271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2365384 : List Nat := [2, 1, 3, 1, 4, 1, 1, 1, 1, 6, 2]
def baseStart_2365384 : Nat := 118140960795 + 2365384 * 2 ^ 59
def prefixEnd_2365384 : Nat := 4983230072969 + 3 ^ 40 * 2365384 * 2
def baseEnd_2365384 : Nat := 1214578924454678657921803

theorem tailTrace_2365384 : CollatzResearch.WordTrace tailWord_2365384 prefixEnd_2365384 1214578924454678657921803 := by
  unfold tailWord_2365384
  simp only [CollatzResearch.WordTrace]
  refine ⟨43136321031312609135091603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57515094708416812180122137 43136321031312609135091603)
  ·
    refine ⟨64704481546968913702637405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43136321031312609135091603 64704481546968913702637405)
    ·
      refine ⟨24264180580113342638489027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64704481546968913702637405 24264180580113342638489027)
      ·
        refine ⟨36396270870170013957733541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24264180580113342638489027 36396270870170013957733541)
        ·
          refine ⟨6824300788156877617075039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36396270870170013957733541 6824300788156877617075039)
          ·
            refine ⟨10236451182235316425612559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6824300788156877617075039 10236451182235316425612559)
            ·
              refine ⟨15354676773352974638418839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10236451182235316425612559 15354676773352974638418839)
              ·
                refine ⟨23032015160029461957628259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15354676773352974638418839 23032015160029461957628259)
                ·
                  refine ⟨34548022740044192936442389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23032015160029461957628259 34548022740044192936442389)
                  ·
                    refine ⟨1619438565939571543895737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 34548022740044192936442389 1619438565939571543895737)
                    ·
                      refine ⟨1214578924454678657921803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1619438565939571543895737 1214578924454678657921803)
                      ·
                        rfl

theorem cell23_2365384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 1, 6, 2].length) (baseStart_2365384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2365384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2365384 prefixEnd_2365384 := by exact prefixLift 2365384
  have htrace : WordTrace (prefixWord ++ tailWord_2365384) baseStart_2365384 baseEnd_2365384 := by
    simpa [prefixWord, tailWord_2365384, baseEnd_2365384] using wordTrace_append hprefix tailTrace_2365384
  have hstable : (prefixWord ++ tailWord_2365384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2365384).length < 2 ^ (prefixWord ++ tailWord_2365384).sum := by decide
  have hdescent : baseEnd_2365384 < baseStart_2365384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2365384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2365387 : List Nat := [1, 1, 1, 1, 3, 4, 2, 2, 1, 4, 3]
def baseStart_2365387 : Nat := 118140960795 + 2365387 * 2 ^ 59
def prefixEnd_2365387 : Nat := 4983230072969 + 3 ^ 40 * 2365387 * 2
def baseEnd_2365387 : Nat := 1214580464896642146184289

theorem tailTrace_2365387 : CollatzResearch.WordTrace tailWord_2365387 prefixEnd_2365387 1214580464896642146184289 := by
  unfold tailWord_2365387
  simp only [CollatzResearch.WordTrace]
  refine ⟨86272751481614349782542415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57515167654409566521694943 86272751481614349782542415)
  ·
    refine ⟨129409127222421524673813623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86272751481614349782542415 129409127222421524673813623)
    ·
      refine ⟨194113690833632287010720435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129409127222421524673813623 194113690833632287010720435)
      ·
        refine ⟨291170536250448430516080653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194113690833632287010720435 291170536250448430516080653)
        ·
          refine ⟨109188951093918161443530245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 291170536250448430516080653 109188951093918161443530245)
          ·
            refine ⟨20472928330109655270661921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 109188951093918161443530245 20472928330109655270661921)
            ·
              refine ⟨15354696247582241452996441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20472928330109655270661921 15354696247582241452996441)
              ·
                refine ⟨11516022185686681089747331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15354696247582241452996441 11516022185686681089747331)
                ·
                  refine ⟨17274033278530021634620997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11516022185686681089747331 17274033278530021634620997)
                  ·
                    refine ⟨3238881239724379056491437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17274033278530021634620997 3238881239724379056491437)
                    ·
                      refine ⟨1214580464896642146184289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3238881239724379056491437 1214580464896642146184289)
                      ·
                        rfl

theorem cell23_2365387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2, 1, 4, 3].length) (baseStart_2365387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2365387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2365387 prefixEnd_2365387 := by exact prefixLift 2365387
  have htrace : WordTrace (prefixWord ++ tailWord_2365387) baseStart_2365387 baseEnd_2365387 := by
    simpa [prefixWord, tailWord_2365387, baseEnd_2365387] using wordTrace_append hprefix tailTrace_2365387
  have hstable : (prefixWord ++ tailWord_2365387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2365387).length < 2 ^ (prefixWord ++ tailWord_2365387).sum := by decide
  have hdescent : baseEnd_2365387 < baseStart_2365387 := by decide
  rcases family_descends (prefixWord ++ tailWord_2365387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2365398 : List Nat := [5, 2, 1, 1, 3, 2, 1, 1, 2, 5]
def baseStart_2365398 : Nat := 118140960795 + 2365398 * 2 ^ 59
def prefixEnd_2365398 : Nat := 4983230072969 + 3 ^ 40 * 2365398 * 2
def baseEnd_2365398 : Nat := 404862037727947201048913

theorem tailTrace_2365398 : CollatzResearch.WordTrace tailWord_2365398 prefixEnd_2365398 404862037727947201048913 := by
  unfold tailWord_2365398
  simp only [CollatzResearch.WordTrace]
  refine ⟨5392072042785906166324553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57515435123049665774128565 5392072042785906166324553)
  ·
    refine ⟨4044054032089429624743415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5392072042785906166324553 4044054032089429624743415)
    ·
      refine ⟨6066081048134144437115123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4044054032089429624743415 6066081048134144437115123)
      ·
        refine ⟨9099121572201216655672685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6066081048134144437115123 9099121572201216655672685)
        ·
          refine ⟨3412170589575456245877257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9099121572201216655672685 3412170589575456245877257)
          ·
            refine ⟨2559127942181592184407943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3412170589575456245877257 2559127942181592184407943)
            ·
              refine ⟨3838691913272388276611915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2559127942181592184407943 3838691913272388276611915)
              ·
                refine ⟨5758037869908582414917873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3838691913272388276611915 5758037869908582414917873)
                ·
                  refine ⟨4318528402431436811188405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5758037869908582414917873 4318528402431436811188405)
                  ·
                    refine ⟨404862037727947201048913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4318528402431436811188405 404862037727947201048913)
                    ·
                      rfl

theorem cell23_2365398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_2365398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2365398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2365398 prefixEnd_2365398 := by exact prefixLift 2365398
  have htrace : WordTrace (prefixWord ++ tailWord_2365398) baseStart_2365398 baseEnd_2365398 := by
    simpa [prefixWord, tailWord_2365398, baseEnd_2365398] using wordTrace_append hprefix tailTrace_2365398
  have hstable : (prefixWord ++ tailWord_2365398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2365398).length < 2 ^ (prefixWord ++ tailWord_2365398).sum := by decide
  have hdescent : baseEnd_2365398 < baseStart_2365398 := by decide
  rcases family_descends (prefixWord ++ tailWord_2365398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2365401 : List Nat := [1, 2, 1, 2, 6, 2, 1, 1, 2, 1, 4]
def baseStart_2365401 : Nat := 118140960795 + 2365401 * 2 ^ 59
def prefixEnd_2365401 : Nat := 4983230072969 + 3 ^ 40 * 2365401 * 2
def baseEnd_2365401 : Nat := 1214587653625805091409225

theorem tailTrace_2365401 : CollatzResearch.WordTrace tailWord_2365401 prefixEnd_2365401 1214587653625805091409225 := by
  unfold tailWord_2365401
  simp only [CollatzResearch.WordTrace]
  refine ⟨86273262103563630173552057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57515508069042420115701371 86273262103563630173552057)
  ·
    refine ⟨64704946577672722630164043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86273262103563630173552057 64704946577672722630164043)
    ·
      refine ⟨97057419866509083945246065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64704946577672722630164043 97057419866509083945246065)
      ·
        refine ⟨72793064899881812958934549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97057419866509083945246065 72793064899881812958934549)
        ·
          refine ⟨3412174917181959982450057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 72793064899881812958934549 3412174917181959982450057)
          ·
            refine ⟨2559131187886469986837543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3412174917181959982450057 2559131187886469986837543)
            ·
              refine ⟨3838696781829704980256315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2559131187886469986837543 3838696781829704980256315)
              ·
                refine ⟨5758045172744557470384473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3838696781829704980256315 5758045172744557470384473)
                ·
                  refine ⟨4318533879558418102788355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5758045172744557470384473 4318533879558418102788355)
                  ·
                    refine ⟨6477800819337627154182533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4318533879558418102788355 6477800819337627154182533)
                    ·
                      refine ⟨1214587653625805091409225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6477800819337627154182533 1214587653625805091409225)
                      ·
                        rfl

theorem cell23_2365401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 1, 2, 1, 4].length) (baseStart_2365401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2365401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2365401 prefixEnd_2365401 := by exact prefixLift 2365401
  have htrace : WordTrace (prefixWord ++ tailWord_2365401) baseStart_2365401 baseEnd_2365401 := by
    simpa [prefixWord, tailWord_2365401, baseEnd_2365401] using wordTrace_append hprefix tailTrace_2365401
  have hstable : (prefixWord ++ tailWord_2365401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2365401).length < 2 ^ (prefixWord ++ tailWord_2365401).sum := by decide
  have hdescent : baseEnd_2365401 < baseStart_2365401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2365401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2365411 : List Nat := [1, 1, 1, 6, 1, 2, 1, 5, 1, 4]
def baseStart_2365411 : Nat := 118140960795 + 2365411 * 2 ^ 59
def prefixEnd_2365411 : Nat := 4983230072969 + 3 ^ 40 * 2365411 * 2
def baseEnd_2365411 : Nat := 404864262810783350761393

theorem tailTrace_2365411 : CollatzResearch.WordTrace tailWord_2365411 prefixEnd_2365411 404864262810783350761393 := by
  unfold tailWord_2365411
  simp only [CollatzResearch.WordTrace]
  refine ⟨86273626833527401881416087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57515751222351601254277391 86273626833527401881416087)
  ·
    refine ⟨129410440250291102822124131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86273626833527401881416087 129410440250291102822124131)
    ·
      refine ⟨194115660375436654233186197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129410440250291102822124131 194115660375436654233186197)
      ·
        refine ⟨9099171580098593167180603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 194115660375436654233186197 9099171580098593167180603)
        ·
          refine ⟨13648757370147889750770905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9099171580098593167180603 13648757370147889750770905)
          ·
            refine ⟨10236568027610917313078179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13648757370147889750770905 10236568027610917313078179)
            ·
              refine ⟨15354852041416375969617269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10236568027610917313078179 15354852041416375969617269)
              ·
                refine ⟨1439517378882785247151619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15354852041416375969617269 1439517378882785247151619)
                ·
                  refine ⟨2159276068324177870727429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1439517378882785247151619 2159276068324177870727429)
                  ·
                    refine ⟨404864262810783350761393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2159276068324177870727429 404864262810783350761393)
                    ·
                      rfl

theorem cell23_2365411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 5, 1, 4].length) (baseStart_2365411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2365411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2365411 prefixEnd_2365411 := by exact prefixLift 2365411
  have htrace : WordTrace (prefixWord ++ tailWord_2365411) baseStart_2365411 baseEnd_2365411 := by
    simpa [prefixWord, tailWord_2365411, baseEnd_2365411] using wordTrace_append hprefix tailTrace_2365411
  have hstable : (prefixWord ++ tailWord_2365411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2365411).length < 2 ^ (prefixWord ++ tailWord_2365411).sum := by decide
  have hdescent : baseEnd_2365411 < baseStart_2365411 := by decide
  rcases family_descends (prefixWord ++ tailWord_2365411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2365437 : List Nat := [1, 4, 1, 1, 1, 2, 2, 1, 5, 5]
def baseStart_2365437 : Nat := 118140960795 + 2365437 * 2 ^ 59
def prefixEnd_2365437 : Nat := 4983230072969 + 3 ^ 40 * 2365437 * 2
def baseEnd_2365437 : Nat := 404868712976455650186353

theorem tailTrace_2365437 : CollatzResearch.WordTrace tailWord_2365437 prefixEnd_2365437 404868712976455650186353 := by
  unfold tailWord_2365437
  simp only [CollatzResearch.WordTrace]
  refine ⟨86274575131433208321862565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57516383420955472214575043 86274575131433208321862565)
  ·
    refine ⟨16176482837143726560349231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86274575131433208321862565 16176482837143726560349231)
    ·
      refine ⟨24264724255715589840523847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16176482837143726560349231 24264724255715589840523847)
      ·
        refine ⟨36397086383573384760785771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24264724255715589840523847 36397086383573384760785771)
        ·
          refine ⟨54595629575360077141178657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36397086383573384760785771 54595629575360077141178657)
          ·
            refine ⟨40946722181520057855883993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54595629575360077141178657 40946722181520057855883993)
            ·
              refine ⟨30710041636140043391912995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40946722181520057855883993 30710041636140043391912995)
              ·
                refine ⟨46065062454210065087869493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30710041636140043391912995 46065062454210065087869493)
                ·
                  refine ⟨4318599605082193601987765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46065062454210065087869493 4318599605082193601987765)
                  ·
                    refine ⟨404868712976455650186353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4318599605082193601987765 404868712976455650186353)
                    ·
                      rfl

theorem cell23_2365437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 5, 5].length) (baseStart_2365437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2365437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2365437 prefixEnd_2365437 := by exact prefixLift 2365437
  have htrace : WordTrace (prefixWord ++ tailWord_2365437) baseStart_2365437 baseEnd_2365437 := by
    simpa [prefixWord, tailWord_2365437, baseEnd_2365437] using wordTrace_append hprefix tailTrace_2365437
  have hstable : (prefixWord ++ tailWord_2365437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2365437).length < 2 ^ (prefixWord ++ tailWord_2365437).sum := by decide
  have hdescent : baseEnd_2365437 < baseStart_2365437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2365437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2365487 : List Nat := [1, 1, 2, 1, 2, 1, 1, 3, 5, 2, 4]
def baseStart_2365487 : Nat := 118140960795 + 2365487 * 2 ^ 59
def prefixEnd_2365487 : Nat := 4983230072969 + 3 ^ 40 * 2365487 * 2
def baseEnd_2365487 : Nat := 1214631812962091754933829

theorem tailTrace_2365487 : CollatzResearch.WordTrace tailWord_2365487 prefixEnd_2365487 1214631812962091754933829 := by
  unfold tailWord_2365487
  simp only [CollatzResearch.WordTrace]
  refine ⟨86276398781252066861182715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57517599187501377907455143 86276398781252066861182715)
  ·
    refine ⟨129414598171878100291774073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86276398781252066861182715 129414598171878100291774073)
    ·
      refine ⟨97060948628908575218830555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129414598171878100291774073 97060948628908575218830555)
      ·
        refine ⟨145591422943362862828245833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97060948628908575218830555 145591422943362862828245833)
        ·
          refine ⟨109193567207522147121184375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145591422943362862828245833 109193567207522147121184375)
          ·
            refine ⟨163790350811283220681776563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109193567207522147121184375 163790350811283220681776563)
            ·
              refine ⟨245685526216924831022664845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163790350811283220681776563 245685526216924831022664845)
              ·
                refine ⟨92132072331346811633499317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 245685526216924831022664845 92132072331346811633499317)
                ·
                  refine ⟨8637381781063763590640561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 92132072331346811633499317 8637381781063763590640561)
                  ·
                    refine ⟨6478036335797822692980421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8637381781063763590640561 6478036335797822692980421)
                    ·
                      refine ⟨1214631812962091754933829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6478036335797822692980421 1214631812962091754933829)
                      ·
                        rfl

theorem cell23_2365487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 5, 2, 4].length) (baseStart_2365487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2365487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2365487 prefixEnd_2365487 := by exact prefixLift 2365487
  have htrace : WordTrace (prefixWord ++ tailWord_2365487) baseStart_2365487 baseEnd_2365487 := by
    simpa [prefixWord, tailWord_2365487, baseEnd_2365487] using wordTrace_append hprefix tailTrace_2365487
  have hstable : (prefixWord ++ tailWord_2365487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2365487).length < 2 ^ (prefixWord ++ tailWord_2365487).sum := by decide
  have hdescent : baseEnd_2365487 < baseStart_2365487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2365487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2365501 : List Nat := [1, 4, 1, 3, 1, 1, 3, 3, 2, 4]
def baseStart_2365501 : Nat := 118140960795 + 2365501 * 2 ^ 59
def prefixEnd_2365501 : Nat := 4983230072969 + 3 ^ 40 * 2365501 * 2
def baseEnd_2365501 : Nat := 404879667230418233386255

theorem tailTrace_2365501 : CollatzResearch.WordTrace tailWord_2365501 prefixEnd_2365501 404879667230418233386255 := by
  unfold tailWord_2365501
  simp only [CollatzResearch.WordTrace]
  refine ⟨86276909403201347252192357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57517939602134231501461571 86276909403201347252192357)
  ·
    refine ⟨16176920513100252609786067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86276909403201347252192357 16176920513100252609786067)
    ·
      refine ⟨24265380769650378914679101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16176920513100252609786067 24265380769650378914679101)
      ·
        refine ⟨9099517788618892093004663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24265380769650378914679101 9099517788618892093004663)
        ·
          refine ⟨13649276682928338139506995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9099517788618892093004663 13649276682928338139506995)
          ·
            refine ⟨20473915024392507209260493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13649276682928338139506995 20473915024392507209260493)
            ·
              refine ⟨7677718134147190203472685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20473915024392507209260493 7677718134147190203472685)
              ·
                refine ⟨2879144300305196326302257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7677718134147190203472685 2879144300305196326302257)
                ·
                  refine ⟨2159358225228897244726693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2879144300305196326302257 2159358225228897244726693)
                  ·
                    refine ⟨404879667230418233386255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2159358225228897244726693 404879667230418233386255)
                    ·
                      rfl

theorem cell23_2365501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 3, 2, 4].length) (baseStart_2365501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2365501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2365501 prefixEnd_2365501 := by exact prefixLift 2365501
  have htrace : WordTrace (prefixWord ++ tailWord_2365501) baseStart_2365501 baseEnd_2365501 := by
    simpa [prefixWord, tailWord_2365501, baseEnd_2365501] using wordTrace_append hprefix tailTrace_2365501
  have hstable : (prefixWord ++ tailWord_2365501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2365501).length < 2 ^ (prefixWord ++ tailWord_2365501).sum := by decide
  have hdescent : baseEnd_2365501 < baseStart_2365501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2365501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2365528 : List Nat := [2, 1, 2, 2, 1, 5, 3, 1, 1, 2, 3]
def baseStart_2365528 : Nat := 118140960795 + 2365528 * 2 ^ 59
def prefixEnd_2365528 : Nat := 4983230072969 + 3 ^ 40 * 2365528 * 2
def baseEnd_2365528 : Nat := 1214652865668926094521141

theorem tailTrace_2365528 : CollatzResearch.WordTrace tailWord_2365528 prefixEnd_2365528 1214652865668926094521141 := by
  unfold tailWord_2365528
  simp only [CollatzResearch.WordTrace]
  refine ⟨43138947087051765431712619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57518596116069020575616825 43138947087051765431712619)
  ·
    refine ⟨64708420630577648147568929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43138947087051765431712619 64708420630577648147568929)
    ·
      refine ⟨48531315472933236110676697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64708420630577648147568929 48531315472933236110676697)
      ·
        refine ⟨36398486604699927083007523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48531315472933236110676697 36398486604699927083007523)
        ·
          refine ⟨54597729907049890624511285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36398486604699927083007523 54597729907049890624511285)
          ·
            refine ⟨5118537178785927246047933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54597729907049890624511285 5118537178785927246047933)
            ·
              refine ⟨1919451442044722717267975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5118537178785927246047933 1919451442044722717267975)
              ·
                refine ⟨2879177163067084075901963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1919451442044722717267975 2879177163067084075901963)
                ·
                  refine ⟨4318765744600626113852945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2879177163067084075901963 4318765744600626113852945)
                  ·
                    refine ⟨3239074308450469585389709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4318765744600626113852945 3239074308450469585389709)
                    ·
                      refine ⟨1214652865668926094521141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3239074308450469585389709 1214652865668926094521141)
                      ·
                        rfl

theorem cell23_2365528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 3, 1, 1, 2, 3].length) (baseStart_2365528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2365528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2365528 prefixEnd_2365528 := by exact prefixLift 2365528
  have htrace : WordTrace (prefixWord ++ tailWord_2365528) baseStart_2365528 baseEnd_2365528 := by
    simpa [prefixWord, tailWord_2365528, baseEnd_2365528] using wordTrace_append hprefix tailTrace_2365528
  have hstable : (prefixWord ++ tailWord_2365528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2365528).length < 2 ^ (prefixWord ++ tailWord_2365528).sum := by decide
  have hdescent : baseEnd_2365528 < baseStart_2365528 := by decide
  rcases family_descends (prefixWord ++ tailWord_2365528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2365551 : List Nat := [1, 1, 2, 1, 3, 4, 1, 2, 3, 3, 2]
def baseStart_2365551 : Nat := 118140960795 + 2365551 * 2 ^ 59
def prefixEnd_2365551 : Nat := 4983230072969 + 3 ^ 40 * 2365551 * 2
def baseEnd_2365551 : Nat := 1214664675723979504533535

theorem tailTrace_2365551 : CollatzResearch.WordTrace tailWord_2365551 prefixEnd_2365551 1214664675723979504533535 := by
  unfold tailWord_2365551
  simp only [CollatzResearch.WordTrace]
  refine ⟨86278733053020205791512507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57519155368680137194341671 86278733053020205791512507)
  ·
    refine ⟨129418099579530308687268761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86278733053020205791512507 129418099579530308687268761)
    ·
      refine ⟨97063574684647731515451571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129418099579530308687268761 97063574684647731515451571)
      ·
        refine ⟨145595362026971597273177357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97063574684647731515451571 145595362026971597273177357)
        ·
          refine ⟨54598260760114348977441509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 145595362026971597273177357 54598260760114348977441509)
          ·
            refine ⟨10237173892521440433270283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54598260760114348977441509 10237173892521440433270283)
            ·
              refine ⟨15355760838782160649905425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10237173892521440433270283 15355760838782160649905425)
              ·
                refine ⟨11516820629086620487429069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15355760838782160649905425 11516820629086620487429069)
                ·
                  refine ⟨4318807735907482682785901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11516820629086620487429069 4318807735907482682785901)
                  ·
                    refine ⟨1619552900965306006044713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4318807735907482682785901 1619552900965306006044713)
                    ·
                      refine ⟨1214664675723979504533535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1619552900965306006044713 1214664675723979504533535)
                      ·
                        rfl

theorem cell23_2365551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 2, 3, 3, 2].length) (baseStart_2365551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2365551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2365551 prefixEnd_2365551 := by exact prefixLift 2365551
  have htrace : WordTrace (prefixWord ++ tailWord_2365551) baseStart_2365551 baseEnd_2365551 := by
    simpa [prefixWord, tailWord_2365551, baseEnd_2365551] using wordTrace_append hprefix tailTrace_2365551
  have hstable : (prefixWord ++ tailWord_2365551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2365551).length < 2 ^ (prefixWord ++ tailWord_2365551).sum := by decide
  have hdescent : baseEnd_2365551 < baseStart_2365551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2365551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2365558 : List Nat := [5, 1, 1, 2, 1, 3, 2, 1, 1, 3, 3]
def baseStart_2365558 : Nat := 118140960795 + 2365558 * 2 ^ 59
def prefixEnd_2365558 : Nat := 4983230072969 + 3 ^ 40 * 2365558 * 2
def baseEnd_2365558 : Nat := 1214668270088560977146003

theorem tailTrace_2365558 : CollatzResearch.WordTrace tailWord_2365558 prefixEnd_2365558 1214668270088560977146003 := by
  unfold tailWord_2365558
  simp only [CollatzResearch.WordTrace]
  refine ⟨5392436772749677874188583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57519325575996563991344885 5392436772749677874188583)
  ·
    refine ⟨8088655159124516811282875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5392436772749677874188583 8088655159124516811282875)
    ·
      refine ⟨12132982738686775216924313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8088655159124516811282875 12132982738686775216924313)
      ·
        refine ⟨9099737054015081412693235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12132982738686775216924313 9099737054015081412693235)
        ·
          refine ⟨13649605581022622119039853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9099737054015081412693235 13649605581022622119039853)
          ·
            refine ⟨5118602092883483294639945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13649605581022622119039853 5118602092883483294639945)
            ·
              refine ⟨3838951569662612470979959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5118602092883483294639945 3838951569662612470979959)
              ·
                refine ⟨5758427354493918706469939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3838951569662612470979959 5758427354493918706469939)
                ·
                  refine ⟨8637641031740878059704909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5758427354493918706469939 8637641031740878059704909)
                  ·
                    refine ⟨3239115386902829272389341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8637641031740878059704909 3239115386902829272389341)
                    ·
                      refine ⟨1214668270088560977146003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3239115386902829272389341 1214668270088560977146003)
                      ·
                        rfl

theorem cell23_2365558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_2365558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2365558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2365558 prefixEnd_2365558 := by exact prefixLift 2365558
  have htrace : WordTrace (prefixWord ++ tailWord_2365558) baseStart_2365558 baseEnd_2365558 := by
    simpa [prefixWord, tailWord_2365558, baseEnd_2365558] using wordTrace_append hprefix tailTrace_2365558
  have hstable : (prefixWord ++ tailWord_2365558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2365558).length < 2 ^ (prefixWord ++ tailWord_2365558).sum := by decide
  have hdescent : baseEnd_2365558 < baseStart_2365558 := by decide
  rcases family_descends (prefixWord ++ tailWord_2365558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2365587 : List Nat := [1, 1, 1, 2, 1, 2, 3, 1, 11]
def baseStart_2365587 : Nat := 118140960795 + 2365587 * 2 ^ 59
def prefixEnd_2365587 : Nat := 4983230072969 + 3 ^ 40 * 2365587 * 2
def baseEnd_2365587 : Nat := 134964795669726818187041

theorem tailTrace_2365587 : CollatzResearch.WordTrace tailWord_2365587 prefixEnd_2365587 134964795669726818187041 := by
  unfold tailWord_2365587
  simp only [CollatzResearch.WordTrace]
  refine ⟨86280046080889783939823015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57520030720593189293215343 86280046080889783939823015)
  ·
    refine ⟨129420069121334675909734523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86280046080889783939823015 129420069121334675909734523)
    ·
      refine ⟨194130103682002013864601785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129420069121334675909734523 194130103682002013864601785)
      ·
        refine ⟨145597577761501510398451339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194130103682002013864601785 145597577761501510398451339)
        ·
          refine ⟨218396366642252265597677009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145597577761501510398451339 218396366642252265597677009)
          ·
            refine ⟨163797274981689199198257757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 218396366642252265597677009 163797274981689199198257757)
            ·
              refine ⟨61423978118133449699346659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 163797274981689199198257757 61423978118133449699346659)
              ·
                refine ⟨92135967177200174549019989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61423978118133449699346659 92135967177200174549019989)
                ·
                  refine ⟨134964795669726818187041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 92135967177200174549019989 134964795669726818187041)
                  ·
                    rfl

theorem cell23_2365587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 11].length) (baseStart_2365587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2365587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2365587 prefixEnd_2365587 := by exact prefixLift 2365587
  have htrace : WordTrace (prefixWord ++ tailWord_2365587) baseStart_2365587 baseEnd_2365587 := by
    simpa [prefixWord, tailWord_2365587, baseEnd_2365587] using wordTrace_append hprefix tailTrace_2365587
  have hstable : (prefixWord ++ tailWord_2365587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2365587).length < 2 ^ (prefixWord ++ tailWord_2365587).sum := by decide
  have hdescent : baseEnd_2365587 < baseStart_2365587 := by decide
  rcases family_descends (prefixWord ++ tailWord_2365587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2365592 : List Nat := [2, 1, 2, 4, 4, 1, 1, 2, 2, 1, 3]
def baseStart_2365592 : Nat := 118140960795 + 2365592 * 2 ^ 59
def prefixEnd_2365592 : Nat := 4983230072969 + 3 ^ 40 * 2365592 * 2
def baseEnd_2365592 : Nat := 1214685728430813844120847

theorem tailTrace_2365592 : CollatzResearch.WordTrace tailWord_2365592 prefixEnd_2365592 1214685728430813844120847 := by
  unfold tailWord_2365592
  simp only [CollatzResearch.WordTrace]
  refine ⟨43140114222935834896877515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57520152297247779862503353 43140114222935834896877515)
  ·
    refine ⟨64710171334403752345316273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43140114222935834896877515 64710171334403752345316273)
    ·
      refine ⟨48532628500802814258987205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64710171334403752345316273 48532628500802814258987205)
      ·
        refine ⟨9099867843900527673560101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48532628500802814258987205 9099867843900527673560101)
        ·
          refine ⟨1706225220731348938792519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9099867843900527673560101 1706225220731348938792519)
          ·
            refine ⟨2559337831097023408188779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1706225220731348938792519 2559337831097023408188779)
            ·
              refine ⟨3839006746645535112283169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2559337831097023408188779 3839006746645535112283169)
              ·
                refine ⟨2879255059984151334212377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3839006746645535112283169 2879255059984151334212377)
                ·
                  refine ⟨2159441294988113500659283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2879255059984151334212377 2159441294988113500659283)
                  ·
                    refine ⟨3239161942482170250988925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2159441294988113500659283 3239161942482170250988925)
                    ·
                      refine ⟨1214685728430813844120847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3239161942482170250988925 1214685728430813844120847)
                      ·
                        rfl

theorem cell23_2365592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 2, 2, 1, 3].length) (baseStart_2365592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2365592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2365592 prefixEnd_2365592 := by exact prefixLift 2365592
  have htrace : WordTrace (prefixWord ++ tailWord_2365592) baseStart_2365592 baseEnd_2365592 := by
    simpa [prefixWord, tailWord_2365592, baseEnd_2365592] using wordTrace_append hprefix tailTrace_2365592
  have hstable : (prefixWord ++ tailWord_2365592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2365592).length < 2 ^ (prefixWord ++ tailWord_2365592).sum := by decide
  have hdescent : baseEnd_2365592 < baseStart_2365592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2365592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2365661 : List Nat := [1, 4, 3, 2, 1, 1, 1, 1, 1, 1, 7]
def baseStart_2365661 : Nat := 118140960795 + 2365661 * 2 ^ 59
def prefixEnd_2365661 : Nat := 4983230072969 + 3 ^ 40 * 2365661 * 2
def baseEnd_2365661 : Nat := 1214721158595974074158029

theorem tailTrace_2365661 : CollatzResearch.WordTrace tailWord_2365661 prefixEnd_2365661 1214721158595974074158029 := by
  unfold tailWord_2365661
  simp only [CollatzResearch.WordTrace]
  refine ⟨86282745082621694578016837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57521830055081129718677891 86282745082621694578016837)
  ·
    refine ⟨16178014702991567733378157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86282745082621694578016837 16178014702991567733378157)
    ·
      refine ⟨6066755513621837900016809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16178014702991567733378157 6066755513621837900016809)
      ·
        refine ⟨4550066635216378425012607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6066755513621837900016809 4550066635216378425012607)
        ·
          refine ⟨6825099952824567637518911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4550066635216378425012607 6825099952824567637518911)
          ·
            refine ⟨10237649929236851456278367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6825099952824567637518911 10237649929236851456278367)
            ·
              refine ⟨15356474893855277184417551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10237649929236851456278367 15356474893855277184417551)
              ·
                refine ⟨23034712340782915776626327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15356474893855277184417551 23034712340782915776626327)
                ·
                  refine ⟨34552068511174373664939491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23034712340782915776626327 34552068511174373664939491)
                  ·
                    refine ⟨51828102766761560497409237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34552068511174373664939491 51828102766761560497409237)
                    ·
                      refine ⟨1214721158595974074158029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 51828102766761560497409237 1214721158595974074158029)
                      ·
                        rfl

theorem cell23_2365661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_2365661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2365661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2365661 prefixEnd_2365661 := by exact prefixLift 2365661
  have htrace : WordTrace (prefixWord ++ tailWord_2365661) baseStart_2365661 baseEnd_2365661 := by
    simpa [prefixWord, tailWord_2365661, baseEnd_2365661] using wordTrace_append hprefix tailTrace_2365661
  have hstable : (prefixWord ++ tailWord_2365661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2365661).length < 2 ^ (prefixWord ++ tailWord_2365661).sum := by decide
  have hdescent : baseEnd_2365661 < baseStart_2365661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2365661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2365666 : List Nat := [3, 3, 4, 1, 1, 1, 1, 3, 2, 2, 2]
def baseStart_2365666 : Nat := 118140960795 + 2365666 * 2 ^ 59
def prefixEnd_2365666 : Nat := 4983230072969 + 3 ^ 40 * 2365666 * 2
def baseEnd_2365666 : Nat := 1214723725999246554595507

theorem tailTrace_2365666 : CollatzResearch.WordTrace tailWord_2365666 prefixEnd_2365666 1214723725999246554595507 := by
  unfold tailWord_2365666
  simp only [CollatzResearch.WordTrace]
  refine ⟨21570731861900895107987213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57521951631735720287965901 21570731861900895107987213)
  ·
    refine ⟨8089024448212835665495205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21570731861900895107987213 8089024448212835665495205)
    ·
      refine ⟨1516692084039906687280351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8089024448212835665495205 1516692084039906687280351)
      ·
        refine ⟨2275038126059860030920527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1516692084039906687280351 2275038126059860030920527)
        ·
          refine ⟨3412557189089790046380791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2275038126059860030920527 3412557189089790046380791)
          ·
            refine ⟨5118835783634685069571187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3412557189089790046380791 5118835783634685069571187)
            ·
              refine ⟨7678253675452027604356781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5118835783634685069571187 7678253675452027604356781)
              ·
                refine ⟨2879345128294510351633793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7678253675452027604356781 2879345128294510351633793)
                ·
                  refine ⟨2159508846220882763725345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2879345128294510351633793 2159508846220882763725345)
                  ·
                    refine ⟨1619631634665662072794009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2159508846220882763725345 1619631634665662072794009)
                    ·
                      refine ⟨1214723725999246554595507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1619631634665662072794009 1214723725999246554595507)
                      ·
                        rfl

theorem cell23_2365666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_2365666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2365666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2365666 prefixEnd_2365666 := by exact prefixLift 2365666
  have htrace : WordTrace (prefixWord ++ tailWord_2365666) baseStart_2365666 baseEnd_2365666 := by
    simpa [prefixWord, tailWord_2365666, baseEnd_2365666] using wordTrace_append hprefix tailTrace_2365666
  have hstable : (prefixWord ++ tailWord_2365666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2365666).length < 2 ^ (prefixWord ++ tailWord_2365666).sum := by decide
  have hdescent : baseEnd_2365666 < baseStart_2365666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2365666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2365681 : List Nat := [1, 2, 2, 2, 2, 1, 2, 4, 3, 4]
def baseStart_2365681 : Nat := 118140960795 + 2365681 * 2 ^ 59
def prefixEnd_2365681 : Nat := 4983230072969 + 3 ^ 40 * 2365681 * 2
def baseEnd_2365681 : Nat := 404910476069687998635979

theorem tailTrace_2365681 : CollatzResearch.WordTrace tailWord_2365681 prefixEnd_2365681 404910476069687998635979 := by
  unfold tailWord_2365681
  simp only [CollatzResearch.WordTrace]
  refine ⟨86283474542549237993744897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57522316361699491995829931 86283474542549237993744897)
  ·
    refine ⟨64712605906911928495308673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86283474542549237993744897 64712605906911928495308673)
    ·
      refine ⟨48534454430183946371481505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64712605906911928495308673 48534454430183946371481505)
      ·
        refine ⟨36400840822637959778611129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48534454430183946371481505 36400840822637959778611129)
        ·
          refine ⟨27300630616978469833958347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36400840822637959778611129 27300630616978469833958347)
          ·
            refine ⟨40950945925467704750937521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27300630616978469833958347 40950945925467704750937521)
            ·
              refine ⟨30713209444100778563203141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40950945925467704750937521 30713209444100778563203141)
              ·
                refine ⟨5758726770768895980600589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30713209444100778563203141 5758726770768895980600589)
                ·
                  refine ⟨2159522539038335992725221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5758726770768895980600589 2159522539038335992725221)
                  ·
                    refine ⟨404910476069687998635979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2159522539038335992725221 404910476069687998635979)
                    ·
                      rfl

theorem cell23_2365681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 4, 3, 4].length) (baseStart_2365681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2365681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2365681 prefixEnd_2365681 := by exact prefixLift 2365681
  have htrace : WordTrace (prefixWord ++ tailWord_2365681) baseStart_2365681 baseEnd_2365681 := by
    simpa [prefixWord, tailWord_2365681, baseEnd_2365681] using wordTrace_append hprefix tailTrace_2365681
  have hstable : (prefixWord ++ tailWord_2365681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2365681).length < 2 ^ (prefixWord ++ tailWord_2365681).sum := by decide
  have hdescent : baseEnd_2365681 < baseStart_2365681 := by decide
  rcases family_descends (prefixWord ++ tailWord_2365681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2365795 : List Nat := [1, 1, 1, 5, 2, 1, 1, 4, 3, 2, 2]
def baseStart_2365795 : Nat := 118140960795 + 2365795 * 2 ^ 59
def prefixEnd_2365795 : Nat := 4983230072969 + 3 ^ 40 * 2365795 * 2
def baseEnd_2365795 : Nat := 1214789965003676549882413

theorem tailTrace_2365795 : CollatzResearch.WordTrace tailWord_2365795 prefixEnd_2365795 1214789965003676549882413 := by
  unfold tailWord_2365795
  simp only [CollatzResearch.WordTrace]
  refine ⟨86287632464136235463394839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57525088309424156975596559 86287632464136235463394839)
  ·
    refine ⟨129431448696204353195092259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86287632464136235463394839 129431448696204353195092259)
    ·
      refine ⟨194147173044306529792638389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129431448696204353195092259 194147173044306529792638389)
      ·
        refine ⟨18201297472903737168059849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 194147173044306529792638389 18201297472903737168059849)
        ·
          refine ⟨13650973104677802876044887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18201297472903737168059849 13650973104677802876044887)
          ·
            refine ⟨20476459657016704314067331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13650973104677802876044887 20476459657016704314067331)
            ·
              refine ⟨30714689485525056471100997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20476459657016704314067331 30714689485525056471100997)
              ·
                refine ⟨5759004278535948088331437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30714689485525056471100997 5759004278535948088331437)
                ·
                  refine ⟨2159626604450980533124289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5759004278535948088331437 2159626604450980533124289)
                  ·
                    refine ⟨1619719953338235399843217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2159626604450980533124289 1619719953338235399843217)
                    ·
                      refine ⟨1214789965003676549882413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1619719953338235399843217 1214789965003676549882413)
                      ·
                        rfl

theorem cell23_2365795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 4, 3, 2, 2].length) (baseStart_2365795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2365795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2365795 prefixEnd_2365795 := by exact prefixLift 2365795
  have htrace : WordTrace (prefixWord ++ tailWord_2365795) baseStart_2365795 baseEnd_2365795 := by
    simpa [prefixWord, tailWord_2365795, baseEnd_2365795] using wordTrace_append hprefix tailTrace_2365795
  have hstable : (prefixWord ++ tailWord_2365795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2365795).length < 2 ^ (prefixWord ++ tailWord_2365795).sum := by decide
  have hdescent : baseEnd_2365795 < baseStart_2365795 := by decide
  rcases family_descends (prefixWord ++ tailWord_2365795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2365831 : List Nat := [1, 1, 4, 2, 2, 1, 2, 1, 2, 7]
def baseStart_2365831 : Nat := 118140960795 + 2365831 * 2 ^ 59
def prefixEnd_2365831 : Nat := 4983230072969 + 3 ^ 40 * 2365831 * 2
def baseEnd_2365831 : Nat := 404936150102412803010749

theorem tailTrace_2365831 : CollatzResearch.WordTrace tailWord_2365831 prefixEnd_2365831 404936150102412803010749 := by
  unfold tailWord_2365831
  simp only [CollatzResearch.WordTrace]
  refine ⟨86288945492005813611705347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57525963661337209074470231 86288945492005813611705347)
  ·
    refine ⟨129433418238008720417558021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86288945492005813611705347 129433418238008720417558021)
    ·
      refine ⟨24268765919626635078292129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 129433418238008720417558021 24268765919626635078292129)
      ·
        refine ⟨18201574439719976308719097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24268765919626635078292129 18201574439719976308719097)
        ·
          refine ⟨13651180829789982231539323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18201574439719976308719097 13651180829789982231539323)
          ·
            refine ⟨20476771244684973347308985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13651180829789982231539323 20476771244684973347308985)
            ·
              refine ⟨15357578433513730010481739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20476771244684973347308985 15357578433513730010481739)
              ·
                refine ⟨23036367650270595015722609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15357578433513730010481739 23036367650270595015722609)
                ·
                  refine ⟨17277275737702946261791957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23036367650270595015722609 17277275737702946261791957)
                  ·
                    refine ⟨404936150102412803010749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17277275737702946261791957 404936150102412803010749)
                    ·
                      rfl

theorem cell23_2365831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 2, 7].length) (baseStart_2365831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2365831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2365831 prefixEnd_2365831 := by exact prefixLift 2365831
  have htrace : WordTrace (prefixWord ++ tailWord_2365831) baseStart_2365831 baseEnd_2365831 := by
    simpa [prefixWord, tailWord_2365831, baseEnd_2365831] using wordTrace_append hprefix tailTrace_2365831
  have hstable : (prefixWord ++ tailWord_2365831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2365831).length < 2 ^ (prefixWord ++ tailWord_2365831).sum := by decide
  have hdescent : baseEnd_2365831 < baseStart_2365831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2365831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2365855 : List Nat := [1, 1, 2, 5, 1, 1, 3, 1, 3, 3, 2]
def baseStart_2365855 : Nat := 118140960795 + 2365855 * 2 ^ 59
def prefixEnd_2365855 : Nat := 4983230072969 + 3 ^ 40 * 2365855 * 2
def baseEnd_2365855 : Nat := 1214820773842946315132137

theorem tailTrace_2365855 : CollatzResearch.WordTrace tailWord_2365855 prefixEnd_2365855 1214820773842946315132137 := by
  unfold tailWord_2365855
  simp only [CollatzResearch.WordTrace]
  refine ⟨86289820843918865710579019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57526547229279243807052679 86289820843918865710579019)
  ·
    refine ⟨129434731265878298565868529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86289820843918865710579019 129434731265878298565868529)
    ·
      refine ⟨97076048449408723924401397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129434731265878298565868529 97076048449408723924401397)
      ·
        refine ⟨9100879542132067867912631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 97076048449408723924401397 9100879542132067867912631)
        ·
          refine ⟨13651319313198101801868947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9100879542132067867912631 13651319313198101801868947)
          ·
            refine ⟨20476978969797152702803421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13651319313198101801868947 20476978969797152702803421)
            ·
              refine ⟨7678867113673932263551283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20476978969797152702803421 7678867113673932263551283)
              ·
                refine ⟨11518300670510898395326925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7678867113673932263551283 11518300670510898395326925)
                ·
                  refine ⟨4319362751441586898247597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11518300670510898395326925 4319362751441586898247597)
                  ·
                    refine ⟨1619761031790595086842849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4319362751441586898247597 1619761031790595086842849)
                    ·
                      refine ⟨1214820773842946315132137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1619761031790595086842849 1214820773842946315132137)
                      ·
                        rfl

theorem cell23_2365855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 1, 3, 3, 2].length) (baseStart_2365855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2365855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2365855 prefixEnd_2365855 := by exact prefixLift 2365855
  have htrace : WordTrace (prefixWord ++ tailWord_2365855) baseStart_2365855 baseEnd_2365855 := by
    simpa [prefixWord, tailWord_2365855, baseEnd_2365855] using wordTrace_append hprefix tailTrace_2365855
  have hstable : (prefixWord ++ tailWord_2365855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2365855).length < 2 ^ (prefixWord ++ tailWord_2365855).sum := by decide
  have hdescent : baseEnd_2365855 < baseStart_2365855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2365855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2365866 : List Nat := [3, 1, 6, 1, 2, 1, 1, 1, 1, 1, 5]
def baseStart_2365866 : Nat := 118140960795 + 2365866 * 2 ^ 59
def prefixEnd_2365866 : Nat := 4983230072969 + 3 ^ 40 * 2365866 * 2
def baseEnd_2365866 : Nat := 1214826422130145772094587

theorem tailTrace_2365866 : CollatzResearch.WordTrace tailWord_2365866 prefixEnd_2365866 1214826422130145772094587 := by
  unfold tailWord_2365866
  simp only [CollatzResearch.WordTrace]
  refine ⟨21572555511719753647307363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57526814697919343059486301 21572555511719753647307363)
  ·
    refine ⟨32358833267579630470961045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21572555511719753647307363 32358833267579630470961045)
    ·
      refine ⟨1516820309417795178326299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 32358833267579630470961045 1516820309417795178326299)
      ·
        refine ⟨2275230464126692767489449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1516820309417795178326299 2275230464126692767489449)
        ·
          refine ⟨1706422848095019575617087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2275230464126692767489449 1706422848095019575617087)
          ·
            refine ⟨2559634272142529363425631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1706422848095019575617087 2559634272142529363425631)
            ·
              refine ⟨3839451408213794045138447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2559634272142529363425631 3839451408213794045138447)
              ·
                refine ⟨5759177112320691067707671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3839451408213794045138447 5759177112320691067707671)
                ·
                  refine ⟨8638765668481036601561507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5759177112320691067707671 8638765668481036601561507)
                  ·
                    refine ⟨12958148502721554902342261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8638765668481036601561507 12958148502721554902342261)
                    ·
                      refine ⟨1214826422130145772094587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12958148502721554902342261 1214826422130145772094587)
                      ·
                        rfl

theorem cell23_2365866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_2365866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2365866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2365866 prefixEnd_2365866 := by exact prefixLift 2365866
  have htrace : WordTrace (prefixWord ++ tailWord_2365866) baseStart_2365866 baseEnd_2365866 := by
    simpa [prefixWord, tailWord_2365866, baseEnd_2365866] using wordTrace_append hprefix tailTrace_2365866
  have hstable : (prefixWord ++ tailWord_2365866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2365866).length < 2 ^ (prefixWord ++ tailWord_2365866).sum := by decide
  have hdescent : baseEnd_2365866 < baseStart_2365866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2365866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2365891 : List Nat := [1, 1, 1, 3, 1, 1, 3, 5, 7]
def baseStart_2365891 : Nat := 118140960795 + 2365891 * 2 ^ 59
def prefixEnd_2365891 : Nat := 4983230072969 + 3 ^ 40 * 2365891 * 2
def baseEnd_2365891 : Nat := 134982139905167574920219

theorem tailTrace_2365891 : CollatzResearch.WordTrace tailWord_2365891 prefixEnd_2365891 134982139905167574920219 := by
  unfold tailWord_2365891
  simp only [CollatzResearch.WordTrace]
  refine ⟨86291133871788443858889527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57527422581192295905926351 86291133871788443858889527)
  ·
    refine ⟨129436700807682665788334291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86291133871788443858889527 129436700807682665788334291)
    ·
      refine ⟨194155051211523998682501437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129436700807682665788334291 194155051211523998682501437)
      ·
        refine ⟨72808144204321499505938039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 194155051211523998682501437 72808144204321499505938039)
        ·
          refine ⟨109212216306482249258907059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72808144204321499505938039 109212216306482249258907059)
          ·
            refine ⟨163818324459723373888360589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109212216306482249258907059 163818324459723373888360589)
            ·
              refine ⟨61431871672396265208135221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 163818324459723373888360589 61431871672396265208135221)
              ·
                refine ⟨5759237969287149863262677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 61431871672396265208135221 5759237969287149863262677)
                ·
                  refine ⟨134982139905167574920219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5759237969287149863262677 134982139905167574920219)
                  ·
                    rfl

theorem cell23_2365891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 5, 7].length) (baseStart_2365891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2365891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2365891 prefixEnd_2365891 := by exact prefixLift 2365891
  have htrace : WordTrace (prefixWord ++ tailWord_2365891) baseStart_2365891 baseEnd_2365891 := by
    simpa [prefixWord, tailWord_2365891, baseEnd_2365891] using wordTrace_append hprefix tailTrace_2365891
  have hstable : (prefixWord ++ tailWord_2365891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2365891).length < 2 ^ (prefixWord ++ tailWord_2365891).sum := by decide
  have hdescent : baseEnd_2365891 < baseStart_2365891 := by decide
  rcases family_descends (prefixWord ++ tailWord_2365891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2365898 : List Nat := [3, 1, 2, 1, 2, 2, 3, 1, 2, 2, 4]
def baseStart_2365898 : Nat := 118140960795 + 2365898 * 2 ^ 59
def prefixEnd_2365898 : Nat := 4983230072969 + 3 ^ 40 * 2365898 * 2
def baseEnd_2365898 : Nat := 1214842853511089646894439

theorem tailTrace_2365898 : CollatzResearch.WordTrace tailWord_2365898 prefixEnd_2365898 1214842853511089646894439 := by
  unfold tailWord_2365898
  simp only [CollatzResearch.WordTrace]
  refine ⟨21572847295690771013598587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57527592788508722702929565 21572847295690771013598587)
  ·
    refine ⟨32359270943536156520397881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21572847295690771013598587 32359270943536156520397881)
    ·
      refine ⟨24269453207652117390298411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32359270943536156520397881 24269453207652117390298411)
      ·
        refine ⟨36404179811478176085447617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24269453207652117390298411 36404179811478176085447617)
        ·
          refine ⟨27303134858608632064085713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36404179811478176085447617 27303134858608632064085713)
          ·
            refine ⟨20477351143956474048064285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27303134858608632064085713 20477351143956474048064285)
            ·
              refine ⟨7679006678983677768024107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20477351143956474048064285 7679006678983677768024107)
              ·
                refine ⟨11518510018475516652036161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7679006678983677768024107 11518510018475516652036161)
                ·
                  refine ⟨8638882513856637489027121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11518510018475516652036161 8638882513856637489027121)
                  ·
                    refine ⟨6479161885392478116770341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8638882513856637489027121 6479161885392478116770341)
                    ·
                      refine ⟨1214842853511089646894439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6479161885392478116770341 1214842853511089646894439)
                      ·
                        rfl

theorem cell23_2365898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 1, 2, 2, 4].length) (baseStart_2365898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2365898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2365898 prefixEnd_2365898 := by exact prefixLift 2365898
  have htrace : WordTrace (prefixWord ++ tailWord_2365898) baseStart_2365898 baseEnd_2365898 := by
    simpa [prefixWord, tailWord_2365898, baseEnd_2365898] using wordTrace_append hprefix tailTrace_2365898
  have hstable : (prefixWord ++ tailWord_2365898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2365898).length < 2 ^ (prefixWord ++ tailWord_2365898).sum := by decide
  have hdescent : baseEnd_2365898 < baseStart_2365898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2365898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2365908 : List Nat := [2, 4, 1, 2, 2, 1, 1, 1, 9]
def baseStart_2365908 : Nat := 118140960795 + 2365908 * 2 ^ 59
def prefixEnd_2365908 : Nat := 4983230072969 + 3 ^ 40 * 2365908 * 2
def baseEnd_2365908 : Nat := 134983109813070511974377

theorem tailTrace_2365908 : CollatzResearch.WordTrace tailWord_2365908 prefixEnd_2365908 134983109813070511974377 := by
  unfold tailWord_2365908
  simp only [CollatzResearch.WordTrace]
  refine ⟨43145876956363427881129189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57527835941817903841505585 43145876956363427881129189)
  ·
    refine ⟨8089851929318142727711723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43145876956363427881129189 8089851929318142727711723)
    ·
      refine ⟨12134777893977214091567585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8089851929318142727711723 12134777893977214091567585)
      ·
        refine ⟨9101083420482910568675689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12134777893977214091567585 9101083420482910568675689)
        ·
          refine ⟨6825812565362182926506767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9101083420482910568675689 6825812565362182926506767)
          ·
            refine ⟨10238718848043274389760151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6825812565362182926506767 10238718848043274389760151)
            ·
              refine ⟨15358078272064911584640227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10238718848043274389760151 15358078272064911584640227)
              ·
                refine ⟨23037117408097367376960341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15358078272064911584640227 23037117408097367376960341)
                ·
                  refine ⟨134983109813070511974377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 23037117408097367376960341 134983109813070511974377)
                  ·
                    rfl

theorem cell23_2365908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 9].length) (baseStart_2365908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2365908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2365908 prefixEnd_2365908 := by exact prefixLift 2365908
  have htrace : WordTrace (prefixWord ++ tailWord_2365908) baseStart_2365908 baseEnd_2365908 := by
    simpa [prefixWord, tailWord_2365908, baseEnd_2365908] using wordTrace_append hprefix tailTrace_2365908
  have hstable : (prefixWord ++ tailWord_2365908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2365908).length < 2 ^ (prefixWord ++ tailWord_2365908).sum := by decide
  have hdescent : baseEnd_2365908 < baseStart_2365908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2365908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2365968 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 9, 4]
def baseStart_2365968 : Nat := 118140960795 + 2365968 * 2 ^ 59
def prefixEnd_2365968 : Nat := 4983230072969 + 3 ^ 40 * 2365968 * 2
def baseEnd_2365968 : Nat := 404959599052301457673039

theorem tailTrace_2365968 : CollatzResearch.WordTrace tailWord_2365968 prefixEnd_2365968 404959599052301457673039 := by
  unfold tailWord_2365968
  simp only [CollatzResearch.WordTrace]
  refine ⟨43146971146254743004721279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57529294861672990672961705 43146971146254743004721279)
  ·
    refine ⟨64720456719382114507081919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43146971146254743004721279 64720456719382114507081919)
    ·
      refine ⟨97080685079073171760622879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64720456719382114507081919 97080685079073171760622879)
      ·
        refine ⟨145621027618609757640934319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97080685079073171760622879 145621027618609757640934319)
        ·
          refine ⟨218431541427914636461401479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145621027618609757640934319 218431541427914636461401479)
          ·
            refine ⟨327647312141871954692102219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 218431541427914636461401479 327647312141871954692102219)
            ·
              refine ⟨491470968212807932038153329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 327647312141871954692102219 491470968212807932038153329)
              ·
                refine ⟨368603226159605949028614997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 491470968212807932038153329 368603226159605949028614997)
                ·
                  refine ⟨2159784528278941107589541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 368603226159605949028614997 2159784528278941107589541)
                  ·
                    refine ⟨404959599052301457673039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2159784528278941107589541 404959599052301457673039)
                    ·
                      rfl

theorem cell23_2365968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 9, 4].length) (baseStart_2365968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2365968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2365968 prefixEnd_2365968 := by exact prefixLift 2365968
  have htrace : WordTrace (prefixWord ++ tailWord_2365968) baseStart_2365968 baseEnd_2365968 := by
    simpa [prefixWord, tailWord_2365968, baseEnd_2365968] using wordTrace_append hprefix tailTrace_2365968
  have hstable : (prefixWord ++ tailWord_2365968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2365968).length < 2 ^ (prefixWord ++ tailWord_2365968).sum := by decide
  have hdescent : baseEnd_2365968 < baseStart_2365968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2365968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2365992 : List Nat := [2, 1, 5, 2, 1, 2, 1, 2, 2, 1, 4]
def baseStart_2365992 : Nat := 118140960795 + 2365992 * 2 ^ 59
def prefixEnd_2365992 : Nat := 4983230072969 + 3 ^ 40 * 2365992 * 2
def baseEnd_2365992 : Nat := 1214891120692612279119007

theorem tailTrace_2365992 : CollatzResearch.WordTrace tailWord_2365992 prefixEnd_2365992 1214891120692612279119007 := by
  unfold tailWord_2365992
  simp only [CollatzResearch.WordTrace]
  refine ⟨43147408822211269054158115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57529878429615025405544153 43147408822211269054158115)
  ·
    refine ⟨64721113233316903581237173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43147408822211269054158115 64721113233316903581237173)
    ·
      refine ⟨6067604365623459710740985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 64721113233316903581237173 6067604365623459710740985)
      ·
        refine ⟨4550703274217594783055739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6067604365623459710740985 4550703274217594783055739)
        ·
          refine ⟨6826054911326392174583609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4550703274217594783055739 6826054911326392174583609)
          ·
            refine ⟨5119541183494794130937707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6826054911326392174583609 5119541183494794130937707)
            ·
              refine ⟨7679311775242191196406561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5119541183494794130937707 7679311775242191196406561)
              ·
                refine ⟨5759483831431643397304921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7679311775242191196406561 5759483831431643397304921)
                ·
                  refine ⟨4319612873573732547978691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5759483831431643397304921 4319612873573732547978691)
                  ·
                    refine ⟨6479419310360598821968037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4319612873573732547978691 6479419310360598821968037)
                    ·
                      refine ⟨1214891120692612279119007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6479419310360598821968037 1214891120692612279119007)
                      ·
                        rfl

theorem cell23_2365992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_2365992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2365992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2365992 prefixEnd_2365992 := by exact prefixLift 2365992
  have htrace : WordTrace (prefixWord ++ tailWord_2365992) baseStart_2365992 baseEnd_2365992 := by
    simpa [prefixWord, tailWord_2365992, baseEnd_2365992] using wordTrace_append hprefix tailTrace_2365992
  have hstable : (prefixWord ++ tailWord_2365992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2365992).length < 2 ^ (prefixWord ++ tailWord_2365992).sum := by decide
  have hdescent : baseEnd_2365992 < baseStart_2365992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2365992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2366002 : List Nat := [3, 2, 1, 1, 2, 1, 2, 6, 1, 4]
def baseStart_2366002 : Nat := 118140960795 + 2366002 * 2 ^ 59
def prefixEnd_2366002 : Nat := 4983230072969 + 3 ^ 40 * 2366002 * 2
def baseEnd_2366002 : Nat := 404965418499719079997987

theorem tailTrace_2366002 : CollatzResearch.WordTrace tailWord_2366002 prefixEnd_2366002 404965418499719079997987 := by
  unfold tailWord_2366002
  simp only [CollatzResearch.WordTrace]
  refine ⟨21573795593596577454045065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57530121582924206544120173 21573795593596577454045065)
  ·
    refine ⟨16180346695197433090533799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21573795593596577454045065 16180346695197433090533799)
    ·
      refine ⟨24270520042796149635800699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16180346695197433090533799 24270520042796149635800699)
      ·
        refine ⟨36405780064194224453701049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24270520042796149635800699 36405780064194224453701049)
        ·
          refine ⟨27304335048145668340275787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36405780064194224453701049 27304335048145668340275787)
          ·
            refine ⟨40956502572218502510413681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27304335048145668340275787 40956502572218502510413681)
            ·
              refine ⟨30717376929163876882810261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40956502572218502510413681 30717376929163876882810261)
              ·
                refine ⟨1439877043554556728881731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 30717376929163876882810261 1439877043554556728881731)
                ·
                  refine ⟨2159815565331835093322597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1439877043554556728881731 2159815565331835093322597)
                  ·
                    refine ⟨404965418499719079997987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2159815565331835093322597 404965418499719079997987)
                    ·
                      rfl

theorem cell23_2366002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 6, 1, 4].length) (baseStart_2366002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2366002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2366002 prefixEnd_2366002 := by exact prefixLift 2366002
  have htrace : WordTrace (prefixWord ++ tailWord_2366002) baseStart_2366002 baseEnd_2366002 := by
    simpa [prefixWord, tailWord_2366002, baseEnd_2366002] using wordTrace_append hprefix tailTrace_2366002
  have hstable : (prefixWord ++ tailWord_2366002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2366002).length < 2 ^ (prefixWord ++ tailWord_2366002).sum := by decide
  have hdescent : baseEnd_2366002 < baseStart_2366002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2366002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2366029 : List Nat := [1, 6, 1, 1, 2, 2, 2, 1, 2, 2, 3]
def baseStart_2366029 : Nat := 118140960795 + 2366029 * 2 ^ 59
def prefixEnd_2366029 : Nat := 4983230072969 + 3 ^ 40 * 2366029 * 2
def baseEnd_2366029 : Nat := 1214910119476828634356337

theorem tailTrace_2366029 : CollatzResearch.WordTrace tailWord_2366029 prefixEnd_2366029 1214910119476828634356337 := by
  unfold tailWord_2366029
  simp only [CollatzResearch.WordTrace]
  refine ⟨86296167145288493427413141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57530778096858995618275427 86296167145288493427413141)
  ·
    refine ⟨4045132834935398129409991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 86296167145288493427413141 4045132834935398129409991)
    ·
      refine ⟨6067699252403097194114987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4045132834935398129409991 6067699252403097194114987)
      ·
        refine ⟨9101548878604645791172481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6067699252403097194114987 9101548878604645791172481)
        ·
          refine ⟨6826161658953484343379361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9101548878604645791172481 6826161658953484343379361)
          ·
            refine ⟨5119621244215113257534521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6826161658953484343379361 5119621244215113257534521)
            ·
              refine ⟨3839715933161334943150891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5119621244215113257534521 3839715933161334943150891)
              ·
                refine ⟨5759573899742002414726337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3839715933161334943150891 5759573899742002414726337)
                ·
                  refine ⟨4319680424806501811044753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5759573899742002414726337 4319680424806501811044753)
                  ·
                    refine ⟨3239760318604876358283565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4319680424806501811044753 3239760318604876358283565)
                    ·
                      refine ⟨1214910119476828634356337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3239760318604876358283565 1214910119476828634356337)
                      ·
                        rfl

theorem cell23_2366029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_2366029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2366029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2366029 prefixEnd_2366029 := by exact prefixLift 2366029
  have htrace : WordTrace (prefixWord ++ tailWord_2366029) baseStart_2366029 baseEnd_2366029 := by
    simpa [prefixWord, tailWord_2366029, baseEnd_2366029] using wordTrace_append hprefix tailTrace_2366029
  have hstable : (prefixWord ++ tailWord_2366029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2366029).length < 2 ^ (prefixWord ++ tailWord_2366029).sum := by decide
  have hdescent : baseEnd_2366029 < baseStart_2366029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2366029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2366052 : List Nat := [2, 3, 1, 1, 2, 2, 1, 4, 2, 3, 2]
def baseStart_2366052 : Nat := 118140960795 + 2366052 * 2 ^ 59
def prefixEnd_2366052 : Nat := 4983230072969 + 3 ^ 40 * 2366052 * 2
def baseEnd_2366052 : Nat := 1214921929531882044368731

theorem tailTrace_2366052 : CollatzResearch.WordTrace tailWord_2366052 prefixEnd_2366052 1214921929531882044368731 := by
  unfold tailWord_2366052
  simp only [CollatzResearch.WordTrace]
  refine ⟨43148503012102584177750205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57531337349470112237000273 43148503012102584177750205)
  ·
    refine ⟨16180688629538469066656327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43148503012102584177750205 16180688629538469066656327)
    ·
      refine ⟨24271032944307703599984491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16180688629538469066656327 24271032944307703599984491)
      ·
        refine ⟨36406549416461555399976737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24271032944307703599984491 36406549416461555399976737)
        ·
          refine ⟨27304912062346166549982553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36406549416461555399976737 27304912062346166549982553)
          ·
            refine ⟨20478684046759624912486915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27304912062346166549982553 20478684046759624912486915)
            ·
              refine ⟨30718026070139437368730373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20478684046759624912486915 30718026070139437368730373)
              ·
                refine ⟨5759629888151144506636945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30718026070139437368730373 5759629888151144506636945)
                ·
                  refine ⟨4319722416113358379977709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5759629888151144506636945 4319722416113358379977709)
                  ·
                    refine ⟨1619895906042509392491641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4319722416113358379977709 1619895906042509392491641)
                    ·
                      refine ⟨1214921929531882044368731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1619895906042509392491641 1214921929531882044368731)
                      ·
                        rfl

theorem cell23_2366052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 4, 2, 3, 2].length) (baseStart_2366052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2366052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2366052 prefixEnd_2366052 := by exact prefixLift 2366052
  have htrace : WordTrace (prefixWord ++ tailWord_2366052) baseStart_2366052 baseEnd_2366052 := by
    simpa [prefixWord, tailWord_2366052, baseEnd_2366052] using wordTrace_append hprefix tailTrace_2366052
  have hstable : (prefixWord ++ tailWord_2366052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2366052).length < 2 ^ (prefixWord ++ tailWord_2366052).sum := by decide
  have hdescent : baseEnd_2366052 < baseStart_2366052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2366052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2366053 : List Nat := [1, 3, 1, 3, 5, 1, 2, 2, 1, 4]
def baseStart_2366053 : Nat := 118140960795 + 2366053 * 2 ^ 59
def prefixEnd_2366053 : Nat := 4983230072969 + 3 ^ 40 * 2366053 * 2
def baseEnd_2366053 : Nat := 404974147670845513485409

theorem tailTrace_2366053 : CollatzResearch.WordTrace tailWord_2366053 prefixEnd_2366053 404974147670845513485409 := by
  unfold tailWord_2366053
  simp only [CollatzResearch.WordTrace]
  refine ⟨86297042497201545526286813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57531361664801030350857875 86297042497201545526286813)
  ·
    refine ⟨32361390936450579572357555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86297042497201545526286813 32361390936450579572357555)
    ·
      refine ⟨48542086404675869358536333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32361390936450579572357555 48542086404675869358536333)
      ·
        refine ⟨18203282401753451009451125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48542086404675869358536333 18203282401753451009451125)
        ·
          refine ⟨1706557725164386032136043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18203282401753451009451125 1706557725164386032136043)
          ·
            refine ⟨2559836587746579048204065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1706557725164386032136043 2559836587746579048204065)
            ·
              refine ⟨1919877440809934286153049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2559836587746579048204065 1919877440809934286153049)
              ·
                refine ⟨1439908080607450714614787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1919877440809934286153049 1439908080607450714614787)
                ·
                  refine ⟨2159862120911176071922181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1439908080607450714614787 2159862120911176071922181)
                  ·
                    refine ⟨404974147670845513485409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2159862120911176071922181 404974147670845513485409)
                    ·
                      rfl

theorem cell23_2366053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 2, 2, 1, 4].length) (baseStart_2366053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2366053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2366053 prefixEnd_2366053 := by exact prefixLift 2366053
  have htrace : WordTrace (prefixWord ++ tailWord_2366053) baseStart_2366053 baseEnd_2366053 := by
    simpa [prefixWord, tailWord_2366053, baseEnd_2366053] using wordTrace_append hprefix tailTrace_2366053
  have hstable : (prefixWord ++ tailWord_2366053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2366053).length < 2 ^ (prefixWord ++ tailWord_2366053).sum := by decide
  have hdescent : baseEnd_2366053 < baseStart_2366053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2366053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2366065 : List Nat := [1, 2, 2, 2, 1, 1, 1, 1, 4, 6, 2]
def baseStart_2366065 : Nat := 118140960795 + 2366065 * 2 ^ 59
def prefixEnd_2366065 : Nat := 4983230072969 + 3 ^ 40 * 2366065 * 2
def baseEnd_2366065 : Nat := 1214928604780390493506171

theorem tailTrace_2366065 : CollatzResearch.WordTrace tailWord_2366065 prefixEnd_2366065 1214928604780390493506171 := by
  unfold tailWord_2366065
  simp only [CollatzResearch.WordTrace]
  refine ⟨86297480173158071575723649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57531653448772047717149099 86297480173158071575723649)
  ·
    refine ⟨64723110129868553681792737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86297480173158071575723649 64723110129868553681792737)
    ·
      refine ⟨48542332597401415261344553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64723110129868553681792737 48542332597401415261344553)
      ·
        refine ⟨36406749448051061446008415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48542332597401415261344553 36406749448051061446008415)
        ·
          refine ⟨54610124172076592169012623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36406749448051061446008415 54610124172076592169012623)
          ·
            refine ⟨81915186258114888253518935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54610124172076592169012623 81915186258114888253518935)
            ·
              refine ⟨122872779387172332380278403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81915186258114888253518935 122872779387172332380278403)
              ·
                refine ⟨184309169080758498570417605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122872779387172332380278403 184309169080758498570417605)
                ·
                  refine ⟨34557969202642218481953301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 184309169080758498570417605 34557969202642218481953301)
                  ·
                    refine ⟨1619904806373853991341561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 34557969202642218481953301 1619904806373853991341561)
                    ·
                      refine ⟨1214928604780390493506171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1619904806373853991341561 1214928604780390493506171)
                      ·
                        rfl

theorem cell23_2366065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 6, 2].length) (baseStart_2366065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2366065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2366065 prefixEnd_2366065 := by exact prefixLift 2366065
  have htrace : WordTrace (prefixWord ++ tailWord_2366065) baseStart_2366065 baseEnd_2366065 := by
    simpa [prefixWord, tailWord_2366065, baseEnd_2366065] using wordTrace_append hprefix tailTrace_2366065
  have hstable : (prefixWord ++ tailWord_2366065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2366065).length < 2 ^ (prefixWord ++ tailWord_2366065).sum := by decide
  have hdescent : baseEnd_2366065 < baseStart_2366065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2366065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2366116 : List Nat := [2, 3, 1, 2, 2, 1, 1, 6, 1, 2, 2]
def baseStart_2366116 : Nat := 118140960795 + 2366116 * 2 ^ 59
def prefixEnd_2366116 : Nat := 4983230072969 + 3 ^ 40 * 2366116 * 2
def baseEnd_2366116 : Nat := 1214954792293769793968437

theorem tailTrace_2366116 : CollatzResearch.WordTrace tailWord_2366116 prefixEnd_2366116 1214954792293769793968437 := by
  unfold tailWord_2366116
  simp only [CollatzResearch.WordTrace]
  refine ⟨43149670147986653642915101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57532893530648871523886801 43149670147986653642915101)
  ·
    refine ⟨16181126305494995116093163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43149670147986653642915101 16181126305494995116093163)
    ·
      refine ⟨24271689458242492674139745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16181126305494995116093163 24271689458242492674139745)
      ·
        refine ⟨18203767093681869505604809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24271689458242492674139745 18203767093681869505604809)
        ·
          refine ⟨13652825320261402129203607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18203767093681869505604809 13652825320261402129203607)
          ·
            refine ⟨20479237980392103193805411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13652825320261402129203607 20479237980392103193805411)
            ·
              refine ⟨30718856970588154790708117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20479237980392103193805411 30718856970588154790708117)
              ·
                refine ⟨1439946420496319755814443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 30718856970588154790708117 1439946420496319755814443)
                ·
                  refine ⟨2159919630744479633721665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1439946420496319755814443 2159919630744479633721665)
                  ·
                    refine ⟨1619939723058359725291249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2159919630744479633721665 1619939723058359725291249)
                    ·
                      refine ⟨1214954792293769793968437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1619939723058359725291249 1214954792293769793968437)
                      ·
                        rfl

theorem cell23_2366116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 6, 1, 2, 2].length) (baseStart_2366116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2366116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2366116 prefixEnd_2366116 := by exact prefixLift 2366116
  have htrace : WordTrace (prefixWord ++ tailWord_2366116) baseStart_2366116 baseEnd_2366116 := by
    simpa [prefixWord, tailWord_2366116, baseEnd_2366116] using wordTrace_append hprefix tailTrace_2366116
  have hstable : (prefixWord ++ tailWord_2366116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2366116).length < 2 ^ (prefixWord ++ tailWord_2366116).sum := by decide
  have hdescent : baseEnd_2366116 < baseStart_2366116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2366116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2366119 : List Nat := [1, 1, 6, 3, 1, 1, 1, 2, 1, 1, 5]
def baseStart_2366119 : Nat := 118140960795 + 2366119 * 2 ^ 59
def prefixEnd_2366119 : Nat := 4983230072969 + 3 ^ 40 * 2366119 * 2
def baseEnd_2366119 : Nat := 1214956332735733282230923

theorem tailTrace_2366119 : CollatzResearch.WordTrace tailWord_2366119 prefixEnd_2366119 1214956332735733282230923 := by
  unfold tailWord_2366119
  simp only [CollatzResearch.WordTrace]
  refine ⟨86299449714962438798189411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57532966476641625865459607 86299449714962438798189411)
  ·
    refine ⟨129449174572443658197284117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86299449714962438798189411 129449174572443658197284117)
    ·
      refine ⟨6067930058083296477997693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 129449174572443658197284117 6067930058083296477997693)
      ·
        refine ⟨2275473771781236179249135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6067930058083296477997693 2275473771781236179249135)
        ·
          refine ⟨3413210657671854268873703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2275473771781236179249135 3413210657671854268873703)
          ·
            refine ⟨5119815986507781403310555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3413210657671854268873703 5119815986507781403310555)
            ·
              refine ⟨7679723979761672104965833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5119815986507781403310555 7679723979761672104965833)
              ·
                refine ⟨5759792984821254078724375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7679723979761672104965833 5759792984821254078724375)
                ·
                  refine ⟨8639689477231881118086563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5759792984821254078724375 8639689477231881118086563)
                  ·
                    refine ⟨12959534215847821677129845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8639689477231881118086563 12959534215847821677129845)
                    ·
                      refine ⟨1214956332735733282230923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12959534215847821677129845 1214956332735733282230923)
                      ·
                        rfl

theorem cell23_2366119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_2366119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2366119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2366119 prefixEnd_2366119 := by exact prefixLift 2366119
  have htrace : WordTrace (prefixWord ++ tailWord_2366119) baseStart_2366119 baseEnd_2366119 := by
    simpa [prefixWord, tailWord_2366119, baseEnd_2366119] using wordTrace_append hprefix tailTrace_2366119
  have hstable : (prefixWord ++ tailWord_2366119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2366119).length < 2 ^ (prefixWord ++ tailWord_2366119).sum := by decide
  have hdescent : baseEnd_2366119 < baseStart_2366119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2366119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2366185 : List Nat := [1, 2, 1, 1, 1, 2, 4, 3, 2, 2, 4]
def baseStart_2366185 : Nat := 118140960795 + 2366185 * 2 ^ 59
def prefixEnd_2366185 : Nat := 4983230072969 + 3 ^ 40 * 2366185 * 2
def baseEnd_2366185 : Nat := 1214990222458930024005619

theorem tailTrace_2366185 : CollatzResearch.WordTrace tailWord_2366185 prefixEnd_2366185 1214990222458930024005619 := by
  unfold tailWord_2366185
  simp only [CollatzResearch.WordTrace]
  refine ⟨86301856932723332070092009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57534571288482221380061339 86301856932723332070092009)
  ·
    refine ⟨64726392699542499052569007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86301856932723332070092009 64726392699542499052569007)
    ·
      refine ⟨97089589049313748578853511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64726392699542499052569007 97089589049313748578853511)
      ·
        refine ⟨145634383573970622868280267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97089589049313748578853511 145634383573970622868280267)
        ·
          refine ⟨218451575360955934302420401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145634383573970622868280267 218451575360955934302420401)
          ·
            refine ⟨163838681520716950726815301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 218451575360955934302420401 163838681520716950726815301)
            ·
              refine ⟨30719752785134428261277869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 163838681520716950726815301 30719752785134428261277869)
              ·
                refine ⟨11519907294425410597979201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30719752785134428261277869 11519907294425410597979201)
                ·
                  refine ⟨8639930470819057948484401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11519907294425410597979201 8639930470819057948484401)
                  ·
                    refine ⟨6479947853114293461363301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8639930470819057948484401 6479947853114293461363301)
                    ·
                      refine ⟨1214990222458930024005619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6479947853114293461363301 1214990222458930024005619)
                      ·
                        rfl

theorem cell23_2366185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3, 2, 2, 4].length) (baseStart_2366185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2366185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2366185 prefixEnd_2366185 := by exact prefixLift 2366185
  have htrace : WordTrace (prefixWord ++ tailWord_2366185) baseStart_2366185 baseEnd_2366185 := by
    simpa [prefixWord, tailWord_2366185, baseEnd_2366185] using wordTrace_append hprefix tailTrace_2366185
  have hstable : (prefixWord ++ tailWord_2366185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2366185).length < 2 ^ (prefixWord ++ tailWord_2366185).sum := by decide
  have hdescent : baseEnd_2366185 < baseStart_2366185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2366185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2366189 : List Nat := [1, 5, 1, 2, 1, 1, 2, 3, 1, 4, 2]
def baseStart_2366189 : Nat := 118140960795 + 2366189 * 2 ^ 59
def prefixEnd_2366189 : Nat := 4983230072969 + 3 ^ 40 * 2366189 * 2
def baseEnd_2366189 : Nat := 1214992276381548008355601

theorem tailTrace_2366189 : CollatzResearch.WordTrace tailWord_2366189 prefixEnd_2366189 1214992276381548008355601 := by
  unfold tailWord_2366189
  simp only [CollatzResearch.WordTrace]
  refine ⟨86302002824708840753237621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57534668549805893835491747 86302002824708840753237621)
  ·
    refine ⟨8090812764816453820616027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 86302002824708840753237621 8090812764816453820616027)
    ·
      refine ⟨12136219147224680730924041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8090812764816453820616027 12136219147224680730924041)
      ·
        refine ⟨9102164360418510548193031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12136219147224680730924041 9102164360418510548193031)
        ·
          refine ⟨13653246540627765822289547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9102164360418510548193031 13653246540627765822289547)
          ·
            refine ⟨20479869810941648733434321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13653246540627765822289547 20479869810941648733434321)
            ·
              refine ⟨15359902358206236550075741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20479869810941648733434321 15359902358206236550075741)
              ·
                refine ⟨5759963384327338706278403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15359902358206236550075741 5759963384327338706278403)
                ·
                  refine ⟨8639945076491008059417605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5759963384327338706278403 8639945076491008059417605)
                  ·
                    refine ⟨1619989701842064011140801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8639945076491008059417605 1619989701842064011140801)
                    ·
                      refine ⟨1214992276381548008355601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1619989701842064011140801 1214992276381548008355601)
                      ·
                        rfl

theorem cell23_2366189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 3, 1, 4, 2].length) (baseStart_2366189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2366189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2366189 prefixEnd_2366189 := by exact prefixLift 2366189
  have htrace : WordTrace (prefixWord ++ tailWord_2366189) baseStart_2366189 baseEnd_2366189 := by
    simpa [prefixWord, tailWord_2366189, baseEnd_2366189] using wordTrace_append hprefix tailTrace_2366189
  have hstable : (prefixWord ++ tailWord_2366189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2366189).length < 2 ^ (prefixWord ++ tailWord_2366189).sum := by decide
  have hdescent : baseEnd_2366189 < baseStart_2366189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2366189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2366206 : List Nat := [4, 2, 2, 1, 2, 2, 1, 2, 1, 4, 2]
def baseStart_2366206 : Nat := 118140960795 + 2366206 * 2 ^ 59
def prefixEnd_2366206 : Nat := 4983230072969 + 3 ^ 40 * 2366206 * 2
def baseEnd_2366206 : Nat := 1215001005552674441843023

theorem tailTrace_2366206 : CollatzResearch.WordTrace tailWord_2366206 prefixEnd_2366206 1215001005552674441843023 := by
  unfold tailWord_2366206
  simp only [CollatzResearch.WordTrace]
  refine ⟨10787827858205906582075809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57535081910431501771070981 10787827858205906582075809)
  ·
    refine ⟨8090870893654429936556857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10787827858205906582075809 8090870893654429936556857)
    ·
      refine ⟨6068153170240822452417643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8090870893654429936556857 6068153170240822452417643)
      ·
        refine ⟨9102229755361233678626465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6068153170240822452417643 9102229755361233678626465)
        ·
          refine ⟨6826672316520925258969849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9102229755361233678626465 6826672316520925258969849)
          ·
            refine ⟨5120004237390693944227387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6826672316520925258969849 5120004237390693944227387)
            ·
              refine ⟨7680006356086040916341081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5120004237390693944227387 7680006356086040916341081)
              ·
                refine ⟨5760004767064530687255811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7680006356086040916341081 5760004767064530687255811)
                ·
                  refine ⟨8640007150596796030883717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5760004767064530687255811 8640007150596796030883717)
                  ·
                    refine ⟨1620001340736899255790697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8640007150596796030883717 1620001340736899255790697)
                    ·
                      refine ⟨1215001005552674441843023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1620001340736899255790697 1215001005552674441843023)
                      ·
                        rfl

theorem cell23_2366206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 2, 1, 4, 2].length) (baseStart_2366206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2366206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2366206 prefixEnd_2366206 := by exact prefixLift 2366206
  have htrace : WordTrace (prefixWord ++ tailWord_2366206) baseStart_2366206 baseEnd_2366206 := by
    simpa [prefixWord, tailWord_2366206, baseEnd_2366206] using wordTrace_append hprefix tailTrace_2366206
  have hstable : (prefixWord ++ tailWord_2366206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2366206).length < 2 ^ (prefixWord ++ tailWord_2366206).sum := by decide
  have hdescent : baseEnd_2366206 < baseStart_2366206 := by decide
  rcases family_descends (prefixWord ++ tailWord_2366206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2366222 : List Nat := [4, 1, 1, 2, 1, 1, 1, 4, 2, 3, 3]
def baseStart_2366222 : Nat := 118140960795 + 2366222 * 2 ^ 59
def prefixEnd_2366222 : Nat := 4983230072969 + 3 ^ 40 * 2366222 * 2
def baseEnd_2366222 : Nat := 1215009221243146379242949

theorem tailTrace_2366222 : CollatzResearch.WordTrace tailWord_2366222 prefixEnd_2366222 1215009221243146379242949 := by
  unfold tailWord_2366222
  simp only [CollatzResearch.WordTrace]
  refine ⟨10787900804198660923648615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57535470955726191592792613 10787900804198660923648615)
  ·
    refine ⟨16181851206297991385472923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10787900804198660923648615 16181851206297991385472923)
    ·
      refine ⟨24272776809446987078209385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16181851206297991385472923 24272776809446987078209385)
      ·
        refine ⟨18204582607085240308657039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24272776809446987078209385 18204582607085240308657039)
        ·
          refine ⟨27306873910627860462985559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18204582607085240308657039 27306873910627860462985559)
          ·
            refine ⟨40960310865941790694478339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27306873910627860462985559 40960310865941790694478339)
            ·
              refine ⟨61440466298912686041717509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40960310865941790694478339 61440466298912686041717509)
              ·
                refine ⟨11520087431046128632822033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61440466298912686041717509 11520087431046128632822033)
                ·
                  refine ⟨8640065573284596474616525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11520087431046128632822033 8640065573284596474616525)
                  ·
                    refine ⟨3240024589981723677981197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8640065573284596474616525 3240024589981723677981197)
                    ·
                      refine ⟨1215009221243146379242949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3240024589981723677981197 1215009221243146379242949)
                      ·
                        rfl

theorem cell23_2366222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 4, 2, 3, 3].length) (baseStart_2366222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2366222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2366222 prefixEnd_2366222 := by exact prefixLift 2366222
  have htrace : WordTrace (prefixWord ++ tailWord_2366222) baseStart_2366222 baseEnd_2366222 := by
    simpa [prefixWord, tailWord_2366222, baseEnd_2366222] using wordTrace_append hprefix tailTrace_2366222
  have hstable : (prefixWord ++ tailWord_2366222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2366222).length < 2 ^ (prefixWord ++ tailWord_2366222).sum := by decide
  have hdescent : baseEnd_2366222 < baseStart_2366222 := by decide
  rcases family_descends (prefixWord ++ tailWord_2366222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2366259 : List Nat := [1, 1, 1, 2, 6, 3, 1, 1, 2, 5]
def baseStart_2366259 : Nat := 118140960795 + 2366259 * 2 ^ 59
def prefixEnd_2366259 : Nat := 4983230072969 + 3 ^ 40 * 2366259 * 2
def baseEnd_2366259 : Nat := 405009406675787578160093

theorem tailTrace_2366259 : CollatzResearch.WordTrace tailWord_2366259 prefixEnd_2366259 405009406675787578160093 := by
  unfold tailWord_2366259
  simp only [CollatzResearch.WordTrace]
  refine ⟨86304555934455242708285831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57536370622970161805523887 86304555934455242708285831)
  ·
    refine ⟨129456833901682864062428747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86304555934455242708285831 129456833901682864062428747)
    ·
      refine ⟨194185250852524296093643121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129456833901682864062428747 194185250852524296093643121)
      ·
        refine ⟨145638938139393222070232341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194185250852524296093643121 145638938139393222070232341)
        ·
          refine ⟨6826825225284057284542141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 145638938139393222070232341 6826825225284057284542141)
          ·
            refine ⟨2560059459481521481703303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6826825225284057284542141 2560059459481521481703303)
            ·
              refine ⟨3840089189222282222554955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2560059459481521481703303 3840089189222282222554955)
              ·
                refine ⟨5760133783833423333832433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3840089189222282222554955 5760133783833423333832433)
                ·
                  refine ⟨4320100337875067500374325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5760133783833423333832433 4320100337875067500374325)
                  ·
                    refine ⟨405009406675787578160093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4320100337875067500374325 405009406675787578160093)
                    ·
                      rfl

theorem cell23_2366259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 1, 2, 5].length) (baseStart_2366259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2366259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2366259 prefixEnd_2366259 := by exact prefixLift 2366259
  have htrace : WordTrace (prefixWord ++ tailWord_2366259) baseStart_2366259 baseEnd_2366259 := by
    simpa [prefixWord, tailWord_2366259, baseEnd_2366259] using wordTrace_append hprefix tailTrace_2366259
  have hstable : (prefixWord ++ tailWord_2366259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2366259).length < 2 ^ (prefixWord ++ tailWord_2366259).sum := by decide
  have hdescent : baseEnd_2366259 < baseStart_2366259 := by decide
  rcases family_descends (prefixWord ++ tailWord_2366259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2366275 : List Nat := [1, 1, 1, 3, 1, 4, 1, 1, 1, 3, 6]
def baseStart_2366275 : Nat := 118140960795 + 2366275 * 2 ^ 59
def prefixEnd_2366275 : Nat := 4983230072969 + 3 ^ 40 * 2366275 * 2
def baseEnd_2366275 : Nat := 1215036435717834671880205

theorem tailTrace_2366275 : CollatzResearch.WordTrace tailWord_2366275 prefixEnd_2366275 1215036435717834671880205 := by
  unfold tailWord_2366275
  simp only [CollatzResearch.WordTrace]
  refine ⟨86305139502397277440868279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57536759668264851627245519 86305139502397277440868279)
  ·
    refine ⟨129457709253595916161302419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86305139502397277440868279 129457709253595916161302419)
    ·
      refine ⟨194186563880393874241953629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129457709253595916161302419 194186563880393874241953629)
      ·
        refine ⟨72819961455147702840732611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 194186563880393874241953629 72819961455147702840732611)
        ·
          refine ⟨109229942182721554261098917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72819961455147702840732611 109229942182721554261098917)
          ·
            refine ⟨20480614159260291423956047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 109229942182721554261098917 20480614159260291423956047)
            ·
              refine ⟨30720921238890437135934071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20480614159260291423956047 30720921238890437135934071)
              ·
                refine ⟨46081381858335655703901107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30720921238890437135934071 46081381858335655703901107)
                ·
                  refine ⟨69122072787503483555851661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46081381858335655703901107 69122072787503483555851661)
                  ·
                    refine ⟨25920777295313806333444373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 69122072787503483555851661 25920777295313806333444373)
                    ·
                      refine ⟨1215036435717834671880205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25920777295313806333444373 1215036435717834671880205)
                      ·
                        rfl

theorem cell23_2366275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 3, 6].length) (baseStart_2366275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2366275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2366275 prefixEnd_2366275 := by exact prefixLift 2366275
  have htrace : WordTrace (prefixWord ++ tailWord_2366275) baseStart_2366275 baseEnd_2366275 := by
    simpa [prefixWord, tailWord_2366275, baseEnd_2366275] using wordTrace_append hprefix tailTrace_2366275
  have hstable : (prefixWord ++ tailWord_2366275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2366275).length < 2 ^ (prefixWord ++ tailWord_2366275).sum := by decide
  have hdescent : baseEnd_2366275 < baseStart_2366275 := by decide
  rcases family_descends (prefixWord ++ tailWord_2366275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2366356 : List Nat := [2, 4, 2, 1, 1, 1, 1, 2, 4, 3, 2]
def baseStart_2366356 : Nat := 118140960795 + 2366356 * 2 ^ 59
def prefixEnd_2366356 : Nat := 4983230072969 + 3 ^ 40 * 2366356 * 2
def baseEnd_2366356 : Nat := 1215078027650848854967333

theorem tailTrace_2366356 : CollatzResearch.WordTrace tailWord_2366356 prefixEnd_2366356 1215078027650848854967333 := by
  unfold tailWord_2366356
  simp only [CollatzResearch.WordTrace]
  refine ⟨43154046907551914137283461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57538729210069218849711281 43154046907551914137283461)
  ·
    refine ⟨8091383795165983900740649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43154046907551914137283461 8091383795165983900740649)
    ·
      refine ⟨6068537846374487925555487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8091383795165983900740649 6068537846374487925555487)
      ·
        refine ⟨9102806769561731888333231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6068537846374487925555487 9102806769561731888333231)
        ·
          refine ⟨13654210154342597832499847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9102806769561731888333231 13654210154342597832499847)
          ·
            refine ⟨20481315231513896748749771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13654210154342597832499847 20481315231513896748749771)
            ·
              refine ⟨30721972847270845123124657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20481315231513896748749771 30721972847270845123124657)
              ·
                refine ⟨23041479635453133842343493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30721972847270845123124657 23041479635453133842343493)
                ·
                  refine ⟨4320277431647462595439405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23041479635453133842343493 4320277431647462595439405)
                  ·
                    refine ⟨1620104036867798473289777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4320277431647462595439405 1620104036867798473289777)
                    ·
                      refine ⟨1215078027650848854967333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1620104036867798473289777 1215078027650848854967333)
                      ·
                        rfl

theorem cell23_2366356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 4, 3, 2].length) (baseStart_2366356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2366356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2366356 prefixEnd_2366356 := by exact prefixLift 2366356
  have htrace : WordTrace (prefixWord ++ tailWord_2366356) baseStart_2366356 baseEnd_2366356 := by
    simpa [prefixWord, tailWord_2366356, baseEnd_2366356] using wordTrace_append hprefix tailTrace_2366356
  have hstable : (prefixWord ++ tailWord_2366356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2366356).length < 2 ^ (prefixWord ++ tailWord_2366356).sum := by decide
  have hdescent : baseEnd_2366356 < baseStart_2366356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2366356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2366397 : List Nat := [1, 4, 1, 2, 4, 2, 2, 2, 1, 1, 3]
def baseStart_2366397 : Nat := 118140960795 + 2366397 * 2 ^ 59
def prefixEnd_2366397 : Nat := 4983230072969 + 3 ^ 40 * 2366397 * 2
def baseEnd_2366397 : Nat := 1215099080357683194554645

theorem tailTrace_2366397 : CollatzResearch.WordTrace tailWord_2366397 prefixEnd_2366397 1215099080357683194554645 := by
  unfold tailWord_2366397
  simp only [CollatzResearch.WordTrace]
  refine ⟨86309589207955292276809445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57539726138636861517872963 86309589207955292276809445)
  ·
    refine ⟨16183047976491617301901771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86309589207955292276809445 16183047976491617301901771)
    ·
      refine ⟨24274571964737425952852657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16183047976491617301901771 24274571964737425952852657)
      ·
        refine ⟨18205928973553069464639493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24274571964737425952852657 18205928973553069464639493)
        ·
          refine ⟨3413611682541200524619905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18205928973553069464639493 3413611682541200524619905)
          ·
            refine ⟨2560208761905900393464929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3413611682541200524619905 2560208761905900393464929)
            ·
              refine ⟨1920156571429425295098697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2560208761905900393464929 1920156571429425295098697)
              ·
                refine ⟨1440117428572068971324023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1920156571429425295098697 1440117428572068971324023)
                ·
                  refine ⟨2160176142858103456986035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1440117428572068971324023 2160176142858103456986035)
                  ·
                    refine ⟨3240264214287155185479053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2160176142858103456986035 3240264214287155185479053)
                    ·
                      refine ⟨1215099080357683194554645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3240264214287155185479053 1215099080357683194554645)
                      ·
                        rfl

theorem cell23_2366397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 2, 2, 1, 1, 3].length) (baseStart_2366397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2366397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2366397 prefixEnd_2366397 := by exact prefixLift 2366397
  have htrace : WordTrace (prefixWord ++ tailWord_2366397) baseStart_2366397 baseEnd_2366397 := by
    simpa [prefixWord, tailWord_2366397, baseEnd_2366397] using wordTrace_append hprefix tailTrace_2366397
  have hstable : (prefixWord ++ tailWord_2366397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2366397).length < 2 ^ (prefixWord ++ tailWord_2366397).sum := by decide
  have hdescent : baseEnd_2366397 < baseStart_2366397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2366397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2366403 : List Nat := [1, 1, 1, 3, 1, 1, 2, 8, 1, 2, 2]
def baseStart_2366403 : Nat := 118140960795 + 2366403 * 2 ^ 59
def prefixEnd_2366403 : Nat := 4983230072969 + 3 ^ 40 * 2366403 * 2
def baseEnd_2366403 : Nat := 1215102161241610171079617

theorem tailTrace_2366403 : CollatzResearch.WordTrace tailWord_2366403 prefixEnd_2366403 1215102161241610171079617 := by
  unfold tailWord_2366403
  simp only [CollatzResearch.WordTrace]
  refine ⟨86309808045933555301527863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57539872030622370201018575 86309808045933555301527863)
  ·
    refine ⟨129464712068900332952291795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86309808045933555301527863 129464712068900332952291795)
    ·
      refine ⟨194197068103350499428437693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129464712068900332952291795 194197068103350499428437693)
      ·
        refine ⟨72823900538756437285664135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 194197068103350499428437693 72823900538756437285664135)
        ·
          refine ⟨109235850808134655928496203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72823900538756437285664135 109235850808134655928496203)
          ·
            refine ⟨163853776212201983892744305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109235850808134655928496203 163853776212201983892744305)
            ·
              refine ⟨122890332159151487919558229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 163853776212201983892744305 122890332159151487919558229)
              ·
                refine ⟨1440121079990056499057323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 122890332159151487919558229 1440121079990056499057323)
                ·
                  refine ⟨2160181619985084748585985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1440121079990056499057323 2160181619985084748585985)
                  ·
                    refine ⟨1620136214988813561439489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2160181619985084748585985 1620136214988813561439489)
                    ·
                      refine ⟨1215102161241610171079617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1620136214988813561439489 1215102161241610171079617)
                      ·
                        rfl

theorem cell23_2366403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 8, 1, 2, 2].length) (baseStart_2366403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2366403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2366403 prefixEnd_2366403 := by exact prefixLift 2366403
  have htrace : WordTrace (prefixWord ++ tailWord_2366403) baseStart_2366403 baseEnd_2366403 := by
    simpa [prefixWord, tailWord_2366403, baseEnd_2366403] using wordTrace_append hprefix tailTrace_2366403
  have hstable : (prefixWord ++ tailWord_2366403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2366403).length < 2 ^ (prefixWord ++ tailWord_2366403).sum := by decide
  have hdescent : baseEnd_2366403 < baseStart_2366403 := by decide
  rcases family_descends (prefixWord ++ tailWord_2366403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2366437 : List Nat := [1, 3, 1, 6, 2, 1, 2, 1, 1, 1, 4]
def baseStart_2366437 : Nat := 118140960795 + 2366437 * 2 ^ 59
def prefixEnd_2366437 : Nat := 4983230072969 + 3 ^ 40 * 2366437 * 2
def baseEnd_2366437 : Nat := 1215119619583863038054461

theorem tailTrace_2366437 : CollatzResearch.WordTrace tailWord_2366437 prefixEnd_2366437 1215119619583863038054461 := by
  unfold tailWord_2366437
  simp only [CollatzResearch.WordTrace]
  refine ⟨86311048127810379108265565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57540698751873586072177043 86311048127810379108265565)
  ·
    refine ⟨32366643047928892165599587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86311048127810379108265565 32366643047928892165599587)
    ·
      refine ⟨48549964571893338248399381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32366643047928892165599587 48549964571893338248399381)
      ·
        refine ⟨2275779589307500230393721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 48549964571893338248399381 2275779589307500230393721)
        ·
          refine ⟨1706834691980625172795291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2275779589307500230393721 1706834691980625172795291)
          ·
            refine ⟨2560252037970937759192937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1706834691980625172795291 2560252037970937759192937)
            ·
              refine ⟨1920189028478203319394703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2560252037970937759192937 1920189028478203319394703)
              ·
                refine ⟨2880283542717304979092055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1920189028478203319394703 2880283542717304979092055)
                ·
                  refine ⟨4320425314075957468638083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2880283542717304979092055 4320425314075957468638083)
                  ·
                    refine ⟨6480637971113936202957125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4320425314075957468638083 6480637971113936202957125)
                    ·
                      refine ⟨1215119619583863038054461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6480637971113936202957125 1215119619583863038054461)
                      ·
                        rfl

theorem cell23_2366437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_2366437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2366437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2366437 prefixEnd_2366437 := by exact prefixLift 2366437
  have htrace : WordTrace (prefixWord ++ tailWord_2366437) baseStart_2366437 baseEnd_2366437 := by
    simpa [prefixWord, tailWord_2366437, baseEnd_2366437] using wordTrace_append hprefix tailTrace_2366437
  have hstable : (prefixWord ++ tailWord_2366437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2366437).length < 2 ^ (prefixWord ++ tailWord_2366437).sum := by decide
  have hdescent : baseEnd_2366437 < baseStart_2366437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2366437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2366510 : List Nat := [4, 1, 3, 1, 1, 1, 2, 4, 2, 2, 2]
def baseStart_2366510 : Nat := 118140960795 + 2366510 * 2 ^ 59
def prefixEnd_2366510 : Nat := 4983230072969 + 3 ^ 40 * 2366510 * 2
def baseEnd_2366510 : Nat := 1215157103671641252441625

theorem tailTrace_2366510 : CollatzResearch.WordTrace tailWord_2366510 prefixEnd_2366510 1215157103671641252441625 := by
  unfold tailWord_2366510
  simp only [CollatzResearch.WordTrace]
  refine ⟨10789213832068239071959123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57542473771030608383781989 10789213832068239071959123)
  ·
    refine ⟨16183820748102358607938685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10789213832068239071959123 16183820748102358607938685)
    ·
      refine ⟨6068932780538384477977007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16183820748102358607938685 6068932780538384477977007)
      ·
        refine ⟨9103399170807576716965511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6068932780538384477977007 9103399170807576716965511)
        ·
          refine ⟨13655098756211365075448267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9103399170807576716965511 13655098756211365075448267)
          ·
            refine ⟨20482648134317047613172401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13655098756211365075448267 20482648134317047613172401)
            ·
              refine ⟨15361986100737785709879301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20482648134317047613172401 15361986100737785709879301)
              ·
                refine ⟨2880372393888334820602369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15361986100737785709879301 2880372393888334820602369)
                ·
                  refine ⟨2160279295416251115451777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2880372393888334820602369 2160279295416251115451777)
                  ·
                    refine ⟨1620209471562188336588833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2160279295416251115451777 1620209471562188336588833)
                    ·
                      refine ⟨1215157103671641252441625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1620209471562188336588833 1215157103671641252441625)
                      ·
                        rfl

theorem cell23_2366510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 4, 2, 2, 2].length) (baseStart_2366510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2366510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2366510 prefixEnd_2366510 := by exact prefixLift 2366510
  have htrace : WordTrace (prefixWord ++ tailWord_2366510) baseStart_2366510 baseEnd_2366510 := by
    simpa [prefixWord, tailWord_2366510, baseEnd_2366510] using wordTrace_append hprefix tailTrace_2366510
  have hstable : (prefixWord ++ tailWord_2366510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2366510).length < 2 ^ (prefixWord ++ tailWord_2366510).sum := by decide
  have hdescent : baseEnd_2366510 < baseStart_2366510 := by decide
  rcases family_descends (prefixWord ++ tailWord_2366510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2366546 : List Nat := [3, 2, 2, 1, 3, 1, 1, 3, 2, 5]
def baseStart_2366546 : Nat := 118140960795 + 2366546 * 2 ^ 59
def prefixEnd_2366546 : Nat := 4983230072969 + 3 ^ 40 * 2366546 * 2
def baseEnd_2366546 : Nat := 405058529658401037197153

theorem tailTrace_2366546 : CollatzResearch.WordTrace tailWord_2366546 prefixEnd_2366546 405058529658401037197153 := by
  unfold tailWord_2366546
  simp only [CollatzResearch.WordTrace]
  refine ⟨21578755921103872680995873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57543349122943660482655661 21578755921103872680995873)
  ·
    refine ⟨16184066940827904510746905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21578755921103872680995873 16184066940827904510746905)
    ·
      refine ⟨12138050205620928383060179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16184066940827904510746905 12138050205620928383060179)
      ·
        refine ⟨18207075308431392574590269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12138050205620928383060179 18207075308431392574590269)
        ·
          refine ⟨6827653240661772215471351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18207075308431392574590269 6827653240661772215471351)
          ·
            refine ⟨10241479860992658323207027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6827653240661772215471351 10241479860992658323207027)
            ·
              refine ⟨15362219791488987484810541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10241479860992658323207027 15362219791488987484810541)
              ·
                refine ⟨5760832421808370306803953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15362219791488987484810541 5760832421808370306803953)
                ·
                  refine ⟨4320624316356277730102965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5760832421808370306803953 4320624316356277730102965)
                  ·
                    refine ⟨405058529658401037197153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4320624316356277730102965 405058529658401037197153)
                    ·
                      rfl

theorem cell23_2366546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 3, 2, 5].length) (baseStart_2366546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2366546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2366546 prefixEnd_2366546 := by exact prefixLift 2366546
  have htrace : WordTrace (prefixWord ++ tailWord_2366546) baseStart_2366546 baseEnd_2366546 := by
    simpa [prefixWord, tailWord_2366546, baseEnd_2366546] using wordTrace_append hprefix tailTrace_2366546
  have hstable : (prefixWord ++ tailWord_2366546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2366546).length < 2 ^ (prefixWord ++ tailWord_2366546).sum := by decide
  have hdescent : baseEnd_2366546 < baseStart_2366546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2366546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2366576 : List Nat := [2, 1, 1, 1, 5, 1, 2, 3, 3, 4]
def baseStart_2366576 : Nat := 118140960795 + 2366576 * 2 ^ 59
def prefixEnd_2366576 : Nat := 4983230072969 + 3 ^ 40 * 2366576 * 2
def baseEnd_2366576 : Nat := 405063664464945998072107

theorem tailTrace_2366576 : CollatzResearch.WordTrace tailWord_2366576 prefixEnd_2366576 405063664464945998072107 := by
  unfold tailWord_2366576
  simp only [CollatzResearch.WordTrace]
  refine ⟨43158058937153402923787791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57544078582871203898383721 43158058937153402923787791)
  ·
    refine ⟨64737088405730104385681687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43158058937153402923787791 64737088405730104385681687)
    ·
      refine ⟨97105632608595156578522531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64737088405730104385681687 97105632608595156578522531)
      ·
        refine ⟨145658448912892734867783797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97105632608595156578522531 145658448912892734867783797)
        ·
          refine ⟨13655479585583693893854731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 145658448912892734867783797 13655479585583693893854731)
          ·
            refine ⟨20483219378375540840782097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13655479585583693893854731 20483219378375540840782097)
            ·
              refine ⟨15362414533781655630586573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20483219378375540840782097 15362414533781655630586573)
              ·
                refine ⟨5760905450168120861469965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15362414533781655630586573 5760905450168120861469965)
                ·
                  refine ⟨2160339543813045323051237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5760905450168120861469965 2160339543813045323051237)
                  ·
                    refine ⟨405063664464945998072107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2160339543813045323051237 405063664464945998072107)
                    ·
                      rfl

theorem cell23_2366576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 3, 3, 4].length) (baseStart_2366576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2366576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2366576 prefixEnd_2366576 := by exact prefixLift 2366576
  have htrace : WordTrace (prefixWord ++ tailWord_2366576) baseStart_2366576 baseEnd_2366576 := by
    simpa [prefixWord, tailWord_2366576, baseEnd_2366576] using wordTrace_append hprefix tailTrace_2366576
  have hstable : (prefixWord ++ tailWord_2366576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2366576).length < 2 ^ (prefixWord ++ tailWord_2366576).sum := by decide
  have hdescent : baseEnd_2366576 < baseStart_2366576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2366576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2366593 : List Nat := [1, 2, 4, 2, 2, 2, 1, 2, 3, 4]
def baseStart_2366593 : Nat := 118140960795 + 2366593 * 2 ^ 59
def prefixEnd_2366593 : Nat := 4983230072969 + 3 ^ 40 * 2366593 * 2
def baseEnd_2366593 : Nat := 405066574188654809234581

theorem tailTrace_2366593 : CollatzResearch.WordTrace tailWord_2366593 prefixEnd_2366593 405066574188654809234581 := by
  unfold tailWord_2366593
  simp only [CollatzResearch.WordTrace]
  refine ⟨86316737915245217750944433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57544491943496811833962955 86316737915245217750944433)
  ·
    refine ⟨64737553436433913313208325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86316737915245217750944433 64737553436433913313208325)
    ·
      refine ⟨12138291269331358746226561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64737553436433913313208325 12138291269331358746226561)
      ·
        refine ⟨9103718451998519059669921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12138291269331358746226561 9103718451998519059669921)
        ·
          refine ⟨6827788838998889294752441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9103718451998519059669921 6827788838998889294752441)
          ·
            refine ⟨5120841629249166971064331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6827788838998889294752441 5120841629249166971064331)
            ·
              refine ⟨7681262443873750456596497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5120841629249166971064331 7681262443873750456596497)
              ·
                refine ⟨5760946832905312842447373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7681262443873750456596497 5760946832905312842447373)
                ·
                  refine ⟨2160355062339492315917765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5760946832905312842447373 2160355062339492315917765)
                  ·
                    refine ⟨405066574188654809234581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2160355062339492315917765 405066574188654809234581)
                    ·
                      rfl

theorem cell23_2366593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 2, 3, 4].length) (baseStart_2366593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2366593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2366593 prefixEnd_2366593 := by exact prefixLift 2366593
  have htrace : WordTrace (prefixWord ++ tailWord_2366593) baseStart_2366593 baseEnd_2366593 := by
    simpa [prefixWord, tailWord_2366593, baseEnd_2366593] using wordTrace_append hprefix tailTrace_2366593
  have hstable : (prefixWord ++ tailWord_2366593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2366593).length < 2 ^ (prefixWord ++ tailWord_2366593).sum := by decide
  have hdescent : baseEnd_2366593 < baseStart_2366593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2366593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2366600 : List Nat := [2, 1, 3, 4, 2, 2, 1, 1, 2, 1, 4]
def baseStart_2366600 : Nat := 118140960795 + 2366600 * 2 ^ 59
def prefixEnd_2366600 : Nat := 4983230072969 + 3 ^ 40 * 2366600 * 2
def baseEnd_2366600 : Nat := 1215203316930545900316211

theorem tailTrace_2366600 : CollatzResearch.WordTrace tailWord_2366600 prefixEnd_2366600 1215203316930545900316211 := by
  unfold tailWord_2366600
  simp only [CollatzResearch.WordTrace]
  refine ⟨43158496613109928973224627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57544662150813238630966169 43158496613109928973224627)
  ·
    refine ⟨64737744919664893459836941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43158496613109928973224627 64737744919664893459836941)
    ·
      refine ⟨24276654344874335047438853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64737744919664893459836941 24276654344874335047438853)
      ·
        refine ⟨4551872689663937821394785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24276654344874335047438853 4551872689663937821394785)
        ·
          refine ⟨3413904517247953366046089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4551872689663937821394785 3413904517247953366046089)
          ·
            refine ⟨2560428387935965024534567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3413904517247953366046089 2560428387935965024534567)
            ·
              refine ⟨3840642581903947536801851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2560428387935965024534567 3840642581903947536801851)
              ·
                refine ⟨5760963872855921305202777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3840642581903947536801851 5760963872855921305202777)
                ·
                  refine ⟨4320722904641940978902083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5760963872855921305202777 4320722904641940978902083)
                  ·
                    refine ⟨6481084356962911468353125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4320722904641940978902083 6481084356962911468353125)
                    ·
                      refine ⟨1215203316930545900316211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6481084356962911468353125 1215203316930545900316211)
                      ·
                        rfl

theorem cell23_2366600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_2366600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2366600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2366600 prefixEnd_2366600 := by exact prefixLift 2366600
  have htrace : WordTrace (prefixWord ++ tailWord_2366600) baseStart_2366600 baseEnd_2366600 := by
    simpa [prefixWord, tailWord_2366600, baseEnd_2366600] using wordTrace_append hprefix tailTrace_2366600
  have hstable : (prefixWord ++ tailWord_2366600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2366600).length < 2 ^ (prefixWord ++ tailWord_2366600).sum := by decide
  have hdescent : baseEnd_2366600 < baseStart_2366600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2366600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2366610 : List Nat := [3, 2, 3, 1, 1, 2, 1, 5, 1, 4]
def baseStart_2366610 : Nat := 118140960795 + 2366610 * 2 ^ 59
def prefixEnd_2366610 : Nat := 4983230072969 + 3 ^ 40 * 2366610 * 2
def baseEnd_2366610 : Nat := 405069483912363620397055

theorem tailTrace_2366610 : CollatzResearch.WordTrace tailWord_2366610 prefixEnd_2366610 405069483912363620397055 := by
  unfold tailWord_2366610
  simp only [CollatzResearch.WordTrace]
  refine ⟨21579339489045907413578321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57544905304122419769542189 21579339489045907413578321)
  ·
    refine ⟨16184504616784430560183741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21579339489045907413578321 16184504616784430560183741)
    ·
      refine ⟨6069189231294161460068903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16184504616784430560183741 6069189231294161460068903)
      ·
        refine ⟨9103783846941242190103355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6069189231294161460068903 9103783846941242190103355)
        ·
          refine ⟨13655675770411863285155033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9103783846941242190103355 13655675770411863285155033)
          ·
            refine ⟨10241756827808897463866275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13655675770411863285155033 10241756827808897463866275)
            ·
              refine ⟨15362635241713346195799413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10241756827808897463866275 15362635241713346195799413)
              ·
                refine ⟨1440247053910626205856195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15362635241713346195799413 1440247053910626205856195)
                ·
                  refine ⟨2160370580865939308784293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1440247053910626205856195 2160370580865939308784293)
                  ·
                    refine ⟨405069483912363620397055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2160370580865939308784293 405069483912363620397055)
                    ·
                      rfl

theorem cell23_2366610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_2366610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2366610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2366610 prefixEnd_2366610 := by exact prefixLift 2366610
  have htrace : WordTrace (prefixWord ++ tailWord_2366610) baseStart_2366610 baseEnd_2366610 := by
    simpa [prefixWord, tailWord_2366610, baseEnd_2366610] using wordTrace_append hprefix tailTrace_2366610
  have hstable : (prefixWord ++ tailWord_2366610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2366610).length < 2 ^ (prefixWord ++ tailWord_2366610).sum := by decide
  have hdescent : baseEnd_2366610 < baseStart_2366610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2366610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2366619 : List Nat := [1, 1, 1, 1, 1, 1, 2, 3, 7, 5]
def baseStart_2366619 : Nat := 118140960795 + 2366619 * 2 ^ 59
def prefixEnd_2366619 : Nat := 4983230072969 + 3 ^ 40 * 2366619 * 2
def baseEnd_2366619 : Nat := 405071024354327108659541

theorem tailTrace_2366619 : CollatzResearch.WordTrace tailWord_2366619 prefixEnd_2366619 405071024354327108659541 := by
  unfold tailWord_2366619
  simp only [CollatzResearch.WordTrace]
  refine ⟨86317686213151024191390911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57545124142100682794260607 86317686213151024191390911)
  ·
    refine ⟨129476529319726536287086367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86317686213151024191390911 129476529319726536287086367)
    ·
      refine ⟨194214793979589804430629551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129476529319726536287086367 194214793979589804430629551)
      ·
        refine ⟨291322190969384706645944327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194214793979589804430629551 291322190969384706645944327)
        ·
          refine ⟨436983286454077059968916491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 291322190969384706645944327 436983286454077059968916491)
          ·
            refine ⟨655474929681115589953374737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 436983286454077059968916491 655474929681115589953374737)
            ·
              refine ⟨491606197260836692465031053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 655474929681115589953374737 491606197260836692465031053)
              ·
                refine ⟨184352323972813759674386645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 491606197260836692465031053 184352323972813759674386645)
                ·
                  refine ⟨4320757593112822492368437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 184352323972813759674386645 4320757593112822492368437)
                  ·
                    refine ⟨405071024354327108659541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4320757593112822492368437 405071024354327108659541)
                    ·
                      rfl

theorem cell23_2366619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 7, 5].length) (baseStart_2366619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2366619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2366619 prefixEnd_2366619 := by exact prefixLift 2366619
  have htrace : WordTrace (prefixWord ++ tailWord_2366619) baseStart_2366619 baseEnd_2366619 := by
    simpa [prefixWord, tailWord_2366619, baseEnd_2366619] using wordTrace_append hprefix tailTrace_2366619
  have hstable : (prefixWord ++ tailWord_2366619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2366619).length < 2 ^ (prefixWord ++ tailWord_2366619).sum := by decide
  have hdescent : baseEnd_2366619 < baseStart_2366619 := by decide
  rcases family_descends (prefixWord ++ tailWord_2366619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2366679 : List Nat := [1, 1, 3, 2, 1, 2, 13]
def baseStart_2366679 : Nat := 118140960795 + 2366679 * 2 ^ 59
def prefixEnd_2366679 : Nat := 4983230072969 + 3 ^ 40 * 2366679 * 2
def baseEnd_2366679 : Nat := 15003010887682112237387

theorem tailTrace_2366679 : CollatzResearch.WordTrace tailWord_2366679 prefixEnd_2366679 15003010887682112237387 := by
  unfold tailWord_2366679
  simp only [CollatzResearch.WordTrace]
  refine ⟨86319874592933654438575091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57546583061955769625716727 86319874592933654438575091)
  ·
    refine ⟨129479811889400481657862637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86319874592933654438575091 129479811889400481657862637)
    ·
      refine ⟨48554929458525180621698489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129479811889400481657862637 48554929458525180621698489)
      ·
        refine ⟨36416197093893885466273867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48554929458525180621698489 36416197093893885466273867)
        ·
          refine ⟨54624295640840828199410801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36416197093893885466273867 54624295640840828199410801)
          ·
            refine ⟨40968221730630621149558101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54624295640840828199410801 40968221730630621149558101)
            ·
              refine ⟨15003010887682112237387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 40968221730630621149558101 15003010887682112237387)
              ·
                rfl

theorem cell23_2366679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 13].length) (baseStart_2366679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2366679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2366679 prefixEnd_2366679 := by exact prefixLift 2366679
  have htrace : WordTrace (prefixWord ++ tailWord_2366679) baseStart_2366679 baseEnd_2366679 := by
    simpa [prefixWord, tailWord_2366679, baseEnd_2366679] using wordTrace_append hprefix tailTrace_2366679
  have hstable : (prefixWord ++ tailWord_2366679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2366679).length < 2 ^ (prefixWord ++ tailWord_2366679).sum := by decide
  have hdescent : baseEnd_2366679 < baseStart_2366679 := by decide
  rcases family_descends (prefixWord ++ tailWord_2366679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2366696 : List Nat := [2, 1, 4, 1, 2, 1, 4, 8]
def baseStart_2366696 : Nat := 118140960795 + 2366696 * 2 ^ 59
def prefixEnd_2366696 : Nat := 4983230072969 + 3 ^ 40 * 2366696 * 2
def baseEnd_2366696 : Nat := 45009355965680649063547

theorem tailTrace_2366696 : CollatzResearch.WordTrace tailWord_2366696 prefixEnd_2366696 45009355965680649063547 := by
  unfold tailWord_2366696
  simp only [CollatzResearch.WordTrace]
  refine ⟨43160247316936033170971971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57546996422581377561295961 43160247316936033170971971)
  ·
    refine ⟨64740370975404049756457957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43160247316936033170971971 64740370975404049756457957)
    ·
      refine ⟨12138819557888259329335867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64740370975404049756457957 12138819557888259329335867)
      ·
        refine ⟨18208229336832388994003801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12138819557888259329335867 18208229336832388994003801)
        ·
          refine ⟨13656172002624291745502851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18208229336832388994003801 13656172002624291745502851)
          ·
            refine ⟨20484258003936437618254277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13656172002624291745502851 20484258003936437618254277)
            ·
              refine ⟨3840798375738082053422677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20484258003936437618254277 3840798375738082053422677)
              ·
                refine ⟨45009355965680649063547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3840798375738082053422677 45009355965680649063547)
                ·
                  rfl

theorem cell23_2366696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 8].length) (baseStart_2366696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2366696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2366696 prefixEnd_2366696 := by exact prefixLift 2366696
  have htrace : WordTrace (prefixWord ++ tailWord_2366696) baseStart_2366696 baseEnd_2366696 := by
    simpa [prefixWord, tailWord_2366696, baseEnd_2366696] using wordTrace_append hprefix tailTrace_2366696
  have hstable : (prefixWord ++ tailWord_2366696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2366696).length < 2 ^ (prefixWord ++ tailWord_2366696).sum := by decide
  have hdescent : baseEnd_2366696 < baseStart_2366696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2366696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2366700 : List Nat := [2, 2, 1, 1, 2, 4, 4, 1, 2, 4]
def baseStart_2366700 : Nat := 118140960795 + 2366700 * 2 ^ 59
def prefixEnd_2366700 : Nat := 4983230072969 + 3 ^ 40 * 2366700 * 2
def baseEnd_2366700 : Nat := 405084888331998503021917

theorem tailTrace_2366700 : CollatzResearch.WordTrace tailWord_2366700 prefixEnd_2366700 405084888331998503021917 := by
  unfold tailWord_2366700
  simp only [CollatzResearch.WordTrace]
  refine ⟨43160320262928787512544777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57547093683905050016726369 43160320262928787512544777)
  ·
    refine ⟨32370240197196590634408583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43160320262928787512544777 32370240197196590634408583)
    ·
      refine ⟨48555360295794885951612875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32370240197196590634408583 48555360295794885951612875)
      ·
        refine ⟨72833040443692328927419313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48555360295794885951612875 72833040443692328927419313)
        ·
          refine ⟨54624780332769246695564485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72833040443692328927419313 54624780332769246695564485)
          ·
            refine ⟨10242146312394233755418341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54624780332769246695564485 10242146312394233755418341)
            ·
              refine ⟨1920402433573918829140939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10242146312394233755418341 1920402433573918829140939)
              ·
                refine ⟨2880603650360878243711409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1920402433573918829140939 2880603650360878243711409)
                ·
                  refine ⟨2160452737770658682783557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2880603650360878243711409 2160452737770658682783557)
                  ·
                    refine ⟨405084888331998503021917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2160452737770658682783557 405084888331998503021917)
                    ·
                      rfl

theorem cell23_2366700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 4].length) (baseStart_2366700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2366700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2366700 prefixEnd_2366700 := by exact prefixLift 2366700
  have htrace : WordTrace (prefixWord ++ tailWord_2366700) baseStart_2366700 baseEnd_2366700 := by
    simpa [prefixWord, tailWord_2366700, baseEnd_2366700] using wordTrace_append hprefix tailTrace_2366700
  have hstable : (prefixWord ++ tailWord_2366700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2366700).length < 2 ^ (prefixWord ++ tailWord_2366700).sum := by decide
  have hdescent : baseEnd_2366700 < baseStart_2366700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2366700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2366723 : List Nat := [1, 1, 1, 3, 2, 5, 1, 2, 1, 3, 3]
def baseStart_2366723 : Nat := 118140960795 + 2366723 * 2 ^ 59
def prefixEnd_2366723 : Nat := 4983230072969 + 3 ^ 40 * 2366723 * 2
def baseEnd_2366723 : Nat := 1215266475051048919078145

theorem tailTrace_2366723 : CollatzResearch.WordTrace tailWord_2366723 prefixEnd_2366723 1215266475051048919078145 := by
  unfold tailWord_2366723
  simp only [CollatzResearch.WordTrace]
  refine ⟨86321479404774249953176823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57547652936516166635451215 86321479404774249953176823)
  ·
    refine ⟨129482219107161374929765235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86321479404774249953176823 129482219107161374929765235)
    ·
      refine ⟨194223328660742062394647853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129482219107161374929765235 194223328660742062394647853)
      ·
        refine ⟨72833748247778273397992945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 194223328660742062394647853 72833748247778273397992945)
        ·
          refine ⟨54625311185833705048494709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72833748247778273397992945 54625311185833705048494709)
          ·
            refine ⟨5121122923671909848296379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54625311185833705048494709 5121122923671909848296379)
            ·
              refine ⟨7681684385507864772444569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5121122923671909848296379 7681684385507864772444569)
              ·
                refine ⟨5761263289130898579333427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7681684385507864772444569 5761263289130898579333427)
                ·
                  refine ⟨8641894933696347869000141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5761263289130898579333427 8641894933696347869000141)
                  ·
                    refine ⟨3240710600136130450875053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8641894933696347869000141 3240710600136130450875053)
                    ·
                      refine ⟨1215266475051048919078145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3240710600136130450875053 1215266475051048919078145)
                      ·
                        rfl

theorem cell23_2366723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 2, 1, 3, 3].length) (baseStart_2366723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2366723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2366723 prefixEnd_2366723 := by exact prefixLift 2366723
  have htrace : WordTrace (prefixWord ++ tailWord_2366723) baseStart_2366723 baseEnd_2366723 := by
    simpa [prefixWord, tailWord_2366723, baseEnd_2366723] using wordTrace_append hprefix tailTrace_2366723
  have hstable : (prefixWord ++ tailWord_2366723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2366723).length < 2 ^ (prefixWord ++ tailWord_2366723).sum := by decide
  have hdescent : baseEnd_2366723 < baseStart_2366723 := by decide
  rcases family_descends (prefixWord ++ tailWord_2366723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2366776 : List Nat := [2, 1, 2, 1, 3, 1, 1, 1, 3, 4, 4]
def baseStart_2366776 : Nat := 118140960795 + 2366776 * 2 ^ 59
def prefixEnd_2366776 : Nat := 4983230072969 + 3 ^ 40 * 2366776 * 2
def baseEnd_2366776 : Nat := 1215293689525737211715401

theorem tailTrace_2366776 : CollatzResearch.WordTrace tailWord_2366776 prefixEnd_2366776 1215293689525737211715401 := by
  unfold tailWord_2366776
  simp only [CollatzResearch.WordTrace]
  refine ⟨43161706236791120002428091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57548941649054826669904121 43161706236791120002428091)
  ·
    refine ⟨64742559355186680003642137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43161706236791120002428091 64742559355186680003642137)
    ·
      refine ⟨48556919516390010002731603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64742559355186680003642137 48556919516390010002731603)
      ·
        refine ⟨72835379274585015004097405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48556919516390010002731603 72835379274585015004097405)
        ·
          refine ⟨27313267227969380626536527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72835379274585015004097405 27313267227969380626536527)
          ·
            refine ⟨40969900841954070939804791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27313267227969380626536527 40969900841954070939804791)
            ·
              refine ⟨61454851262931106409707187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40969900841954070939804791 61454851262931106409707187)
              ·
                refine ⟨92182276894396659614560781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61454851262931106409707187 92182276894396659614560781)
                ·
                  refine ⟨34568353835398747355460293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 92182276894396659614560781 34568353835398747355460293)
                  ·
                    refine ⟨6481566344137265129148805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34568353835398747355460293 6481566344137265129148805)
                    ·
                      refine ⟨1215293689525737211715401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6481566344137265129148805 1215293689525737211715401)
                      ·
                        rfl

theorem cell23_2366776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 3, 4, 4].length) (baseStart_2366776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2366776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2366776 prefixEnd_2366776 := by exact prefixLift 2366776
  have htrace : WordTrace (prefixWord ++ tailWord_2366776) baseStart_2366776 baseEnd_2366776 := by
    simpa [prefixWord, tailWord_2366776, baseEnd_2366776] using wordTrace_append hprefix tailTrace_2366776
  have hstable : (prefixWord ++ tailWord_2366776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2366776).length < 2 ^ (prefixWord ++ tailWord_2366776).sum := by decide
  have hdescent : baseEnd_2366776 < baseStart_2366776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2366776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2366780 : List Nat := [2, 2, 2, 2, 1, 3, 2, 2, 1, 4, 2]
def baseStart_2366780 : Nat := 118140960795 + 2366780 * 2 ^ 59
def prefixEnd_2366780 : Nat := 4983230072969 + 3 ^ 40 * 2366780 * 2
def baseEnd_2366780 : Nat := 1215295743448355196065383

theorem tailTrace_2366780 : CollatzResearch.WordTrace tailWord_2366780 prefixEnd_2366780 1215295743448355196065383 := by
  unfold tailWord_2366780
  simp only [CollatzResearch.WordTrace]
  refine ⟨43161779182783874344000897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57549038910378499125334529 43161779182783874344000897)
  ·
    refine ⟨32371334387087905758000673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43161779182783874344000897 32371334387087905758000673)
    ·
      refine ⟨24278500790315929318500505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32371334387087905758000673 24278500790315929318500505)
      ·
        refine ⟨18208875592736946988875379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24278500790315929318500505 18208875592736946988875379)
        ·
          refine ⟨27313313389105420483313069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18208875592736946988875379 27313313389105420483313069)
          ·
            refine ⟨10242492520914532681242401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27313313389105420483313069 10242492520914532681242401)
            ·
              refine ⟨7681869390685899510931801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10242492520914532681242401 7681869390685899510931801)
              ·
                refine ⟨5761402043014424633198851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7681869390685899510931801 5761402043014424633198851)
                ·
                  refine ⟨8642103064521636949798277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5761402043014424633198851 8642103064521636949798277)
                  ·
                    refine ⟨1620394324597806928087177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8642103064521636949798277 1620394324597806928087177)
                    ·
                      refine ⟨1215295743448355196065383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1620394324597806928087177 1215295743448355196065383)
                      ·
                        rfl

theorem cell23_2366780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 2, 1, 4, 2].length) (baseStart_2366780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2366780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2366780 prefixEnd_2366780 := by exact prefixLift 2366780
  have htrace : WordTrace (prefixWord ++ tailWord_2366780) baseStart_2366780 baseEnd_2366780 := by
    simpa [prefixWord, tailWord_2366780, baseEnd_2366780] using wordTrace_append hprefix tailTrace_2366780
  have hstable : (prefixWord ++ tailWord_2366780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2366780).length < 2 ^ (prefixWord ++ tailWord_2366780).sum := by decide
  have hdescent : baseEnd_2366780 < baseStart_2366780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2366780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2366803 : List Nat := [1, 1, 1, 2, 1, 1, 5, 6, 5]
def baseStart_2366803 : Nat := 118140960795 + 2366803 * 2 ^ 59
def prefixEnd_2366803 : Nat := 4983230072969 + 3 ^ 40 * 2366803 * 2
def baseEnd_2366803 : Nat := 135034172611489845119753

theorem tailTrace_2366803 : CollatzResearch.WordTrace tailWord_2366803 prefixEnd_2366803 135034172611489845119753 := by
  unfold tailWord_2366803
  simp only [CollatzResearch.WordTrace]
  refine ⟨86324397244484423616089063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57549598162989615744059375 86324397244484423616089063)
  ·
    refine ⟨129486595866726635424133595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86324397244484423616089063 129486595866726635424133595)
    ·
      refine ⟨194229893800089953136200393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129486595866726635424133595 194229893800089953136200393)
      ·
        refine ⟨145672420350067464852150295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194229893800089953136200393 145672420350067464852150295)
        ·
          refine ⟨218508630525101197278225443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145672420350067464852150295 218508630525101197278225443)
          ·
            refine ⟨327762945787651795917338165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 218508630525101197278225443 327762945787651795917338165)
            ·
              refine ⟨30727776167592355867250453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 327762945787651795917338165 30727776167592355867250453)
              ·
                refine ⟨1440364507855891681277365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 30727776167592355867250453 1440364507855891681277365)
                ·
                  refine ⟨135034172611489845119753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1440364507855891681277365 135034172611489845119753)
                  ·
                    rfl

theorem cell23_2366803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 6, 5].length) (baseStart_2366803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2366803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2366803 prefixEnd_2366803 := by exact prefixLift 2366803
  have htrace : WordTrace (prefixWord ++ tailWord_2366803) baseStart_2366803 baseEnd_2366803 := by
    simpa [prefixWord, tailWord_2366803, baseEnd_2366803] using wordTrace_append hprefix tailTrace_2366803
  have hstable : (prefixWord ++ tailWord_2366803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2366803).length < 2 ^ (prefixWord ++ tailWord_2366803).sum := by decide
  have hdescent : baseEnd_2366803 < baseStart_2366803 := by decide
  rcases family_descends (prefixWord ++ tailWord_2366803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2366853 : List Nat := [1, 3, 1, 1, 3, 1, 3, 1, 4, 1, 4]
def baseStart_2366853 : Nat := 118140960795 + 2366853 * 2 ^ 59
def prefixEnd_2366853 : Nat := 4983230072969 + 3 ^ 40 * 2366853 * 2
def baseEnd_2366853 : Nat := 1215333227536133410452547

theorem tailTrace_2366853 : CollatzResearch.WordTrace tailWord_2366853 prefixEnd_2366853 1215333227536133410452547 := by
  unfold tailWord_2366853
  simp only [CollatzResearch.WordTrace]
  refine ⟨86326220894303282155409213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57550813929535521436939475 86326220894303282155409213)
  ·
    refine ⟨32372332835363730808278455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86326220894303282155409213 32372332835363730808278455)
    ·
      refine ⟨48558499253045596212417683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32372332835363730808278455 48558499253045596212417683)
      ·
        refine ⟨72837748879568394318626525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48558499253045596212417683 72837748879568394318626525)
        ·
          refine ⟨27314155829838147869484947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72837748879568394318626525 27314155829838147869484947)
          ·
            refine ⟨40971233744757221804227421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27314155829838147869484947 40971233744757221804227421)
            ·
              refine ⟨15364212654283958176585283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40971233744757221804227421 15364212654283958176585283)
              ·
                refine ⟨23046318981425937264877925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15364212654283958176585283 23046318981425937264877925)
                ·
                  refine ⟨4321184809017363237164611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23046318981425937264877925 4321184809017363237164611)
                  ·
                    refine ⟨6481777213526044855746917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4321184809017363237164611 6481777213526044855746917)
                    ·
                      refine ⟨1215333227536133410452547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6481777213526044855746917 1215333227536133410452547)
                      ·
                        rfl

theorem cell23_2366853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 4, 1, 4].length) (baseStart_2366853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2366853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2366853 prefixEnd_2366853 := by exact prefixLift 2366853
  have htrace : WordTrace (prefixWord ++ tailWord_2366853) baseStart_2366853 baseEnd_2366853 := by
    simpa [prefixWord, tailWord_2366853, baseEnd_2366853] using wordTrace_append hprefix tailTrace_2366853
  have hstable : (prefixWord ++ tailWord_2366853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2366853).length < 2 ^ (prefixWord ++ tailWord_2366853).sum := by decide
  have hdescent : baseEnd_2366853 < baseStart_2366853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2366853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2366897 : List Nat := [1, 2, 2, 4, 1, 1, 2, 5, 1, 4]
def baseStart_2366897 : Nat := 118140960795 + 2366897 * 2 ^ 59
def prefixEnd_2366897 : Nat := 4983230072969 + 3 ^ 40 * 2366897 * 2
def baseEnd_2366897 : Nat := 405118606894977079434115

theorem tailTrace_2366897 : CollatzResearch.WordTrace tailWord_2366897 prefixEnd_2366897 405118606894977079434115 := by
  unfold tailWord_2366897
  simp only [CollatzResearch.WordTrace]
  refine ⟨86327825706143877670010945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57551883804095918446673963 86327825706143877670010945)
  ·
    refine ⟨64745869279607908252508209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86327825706143877670010945 64745869279607908252508209)
    ·
      refine ⟨48559401959705931189381157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64745869279607908252508209 48559401959705931189381157)
      ·
        refine ⟨9104887867444862098008967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48559401959705931189381157 9104887867444862098008967)
        ·
          refine ⟨13657331801167293147013451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9104887867444862098008967 13657331801167293147013451)
          ·
            refine ⟨20485997701750939720520177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13657331801167293147013451 20485997701750939720520177)
            ·
              refine ⟨15364498276313204790390133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20485997701750939720520177 15364498276313204790390133)
              ·
                refine ⟨1440421713404362949099075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15364498276313204790390133 1440421713404362949099075)
                ·
                  refine ⟨2160632570106544423648613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1440421713404362949099075 2160632570106544423648613)
                  ·
                    refine ⟨405118606894977079434115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2160632570106544423648613 405118606894977079434115)
                    ·
                      rfl

theorem cell23_2366897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 5, 1, 4].length) (baseStart_2366897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2366897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2366897 prefixEnd_2366897 := by exact prefixLift 2366897
  have htrace : WordTrace (prefixWord ++ tailWord_2366897) baseStart_2366897 baseEnd_2366897 := by
    simpa [prefixWord, tailWord_2366897, baseEnd_2366897] using wordTrace_append hprefix tailTrace_2366897
  have hstable : (prefixWord ++ tailWord_2366897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2366897).length < 2 ^ (prefixWord ++ tailWord_2366897).sum := by decide
  have hdescent : baseEnd_2366897 < baseStart_2366897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2366897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2366923 : List Nat := [1, 1, 1, 1, 3, 3, 3, 2, 3, 5]
def baseStart_2366923 : Nat := 118140960795 + 2366923 * 2 ^ 59
def prefixEnd_2366923 : Nat := 4983230072969 + 3 ^ 40 * 2366923 * 2
def baseEnd_2366923 : Nat := 405123057060649378859075

theorem tailTrace_2366923 : CollatzResearch.WordTrace tailWord_2366923 prefixEnd_2366923 405123057060649378859075 := by
  unfold tailWord_2366923
  simp only [CollatzResearch.WordTrace]
  refine ⟨86328774004049684110457423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57552516002699789406971615 86328774004049684110457423)
  ·
    refine ⟨129493161006074526165686135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86328774004049684110457423 129493161006074526165686135)
    ·
      refine ⟨194239741509111789248529203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129493161006074526165686135 194239741509111789248529203)
      ·
        refine ⟨291359612263667683872793805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194239741509111789248529203 291359612263667683872793805)
        ·
          refine ⟨109259854598875381452297677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 291359612263667683872793805 109259854598875381452297677)
          ·
            refine ⟨40972445474578268044611629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109259854598875381452297677 40972445474578268044611629)
            ·
              refine ⟨15364667052966850516729361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40972445474578268044611629 15364667052966850516729361)
              ·
                refine ⟨11523500289725137887547021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15364667052966850516729361 11523500289725137887547021)
                ·
                  refine ⟨4321312608646926707830133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11523500289725137887547021 4321312608646926707830133)
                  ·
                    refine ⟨405123057060649378859075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4321312608646926707830133 405123057060649378859075)
                    ·
                      rfl

theorem cell23_2366923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2, 3, 5].length) (baseStart_2366923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2366923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2366923 prefixEnd_2366923 := by exact prefixLift 2366923
  have htrace : WordTrace (prefixWord ++ tailWord_2366923) baseStart_2366923 baseEnd_2366923 := by
    simpa [prefixWord, tailWord_2366923, baseEnd_2366923] using wordTrace_append hprefix tailTrace_2366923
  have hstable : (prefixWord ++ tailWord_2366923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2366923).length < 2 ^ (prefixWord ++ tailWord_2366923).sum := by decide
  have hdescent : baseEnd_2366923 < baseStart_2366923 := by decide
  rcases family_descends (prefixWord ++ tailWord_2366923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2366933 : List Nat := [1, 3, 2, 3, 1, 1, 1, 1, 2, 1, 7]
def baseStart_2366933 : Nat := 118140960795 + 2366933 * 2 ^ 59
def prefixEnd_2366933 : Nat := 4983230072969 + 3 ^ 40 * 2366933 * 2
def baseEnd_2366933 : Nat := 1215374305988493097452179

theorem tailTrace_2366933 : CollatzResearch.WordTrace tailWord_2366933 prefixEnd_2366933 1215374305988493097452179 := by
  unfold tailWord_2366933
  simp only [CollatzResearch.WordTrace]
  refine ⟨86329138734013455818321453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57552759156008970545547635 86329138734013455818321453)
  ·
    refine ⟨32373427025255045931870545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86329138734013455818321453 32373427025255045931870545)
    ·
      refine ⟨24280070268941284448902909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32373427025255045931870545 24280070268941284448902909)
      ·
        refine ⟨9105026350852981668338591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24280070268941284448902909 9105026350852981668338591)
        ·
          refine ⟨13657539526279472502507887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9105026350852981668338591 13657539526279472502507887)
          ·
            refine ⟨20486309289419208753761831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13657539526279472502507887 20486309289419208753761831)
            ·
              refine ⟨30729463934128813130642747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20486309289419208753761831 30729463934128813130642747)
              ·
                refine ⟨46094195901193219695964121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30729463934128813130642747 46094195901193219695964121)
                ·
                  refine ⟨34570646925894914771973091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46094195901193219695964121 34570646925894914771973091)
                  ·
                    refine ⟨51855970388842372157959637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34570646925894914771973091 51855970388842372157959637)
                    ·
                      refine ⟨1215374305988493097452179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 51855970388842372157959637 1215374305988493097452179)
                      ·
                        rfl

theorem cell23_2366933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_2366933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2366933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2366933 prefixEnd_2366933 := by exact prefixLift 2366933
  have htrace : WordTrace (prefixWord ++ tailWord_2366933) baseStart_2366933 baseEnd_2366933 := by
    simpa [prefixWord, tailWord_2366933, baseEnd_2366933] using wordTrace_append hprefix tailTrace_2366933
  have hstable : (prefixWord ++ tailWord_2366933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2366933).length < 2 ^ (prefixWord ++ tailWord_2366933).sum := by decide
  have hdescent : baseEnd_2366933 < baseStart_2366933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2366933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2366937 : List Nat := [1, 2, 1, 2, 4, 3, 1, 2, 3, 1, 3]
def baseStart_2366937 : Nat := 118140960795 + 2366937 * 2 ^ 59
def prefixEnd_2366937 : Nat := 4983230072969 + 3 ^ 40 * 2366937 * 2
def baseEnd_2366937 : Nat := 1215376359911111081802161

theorem tailTrace_2366937 : CollatzResearch.WordTrace tailWord_2366937 prefixEnd_2366937 1215376359911111081802161 := by
  unfold tailWord_2366937
  simp only [CollatzResearch.WordTrace]
  refine ⟨86329284625998964501467065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57552856417332643000978043 86329284625998964501467065)
  ·
    refine ⟨64746963469499223376100299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86329284625998964501467065 64746963469499223376100299)
    ·
      refine ⟨97120445204248835064150449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64746963469499223376100299 97120445204248835064150449)
      ·
        refine ⟨72840333903186626298112837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97120445204248835064150449 72840333903186626298112837)
        ·
          refine ⟨13657562606847492430896157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72840333903186626298112837 13657562606847492430896157)
          ·
            refine ⟨5121585977567809661586059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13657562606847492430896157 5121585977567809661586059)
            ·
              refine ⟨7682378966351714492379089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5121585977567809661586059 7682378966351714492379089)
              ·
                refine ⟨5761784224763785869284317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7682378966351714492379089 5761784224763785869284317)
                ·
                  refine ⟨2160669084286419700981619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5761784224763785869284317 2160669084286419700981619)
                  ·
                    refine ⟨3241003626429629551472429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2160669084286419700981619 3241003626429629551472429)
                    ·
                      refine ⟨1215376359911111081802161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3241003626429629551472429 1215376359911111081802161)
                      ·
                        rfl

theorem cell23_2366937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 2, 3, 1, 3].length) (baseStart_2366937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2366937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2366937 prefixEnd_2366937 := by exact prefixLift 2366937
  have htrace : WordTrace (prefixWord ++ tailWord_2366937) baseStart_2366937 baseEnd_2366937 := by
    simpa [prefixWord, tailWord_2366937, baseEnd_2366937] using wordTrace_append hprefix tailTrace_2366937
  have hstable : (prefixWord ++ tailWord_2366937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2366937).length < 2 ^ (prefixWord ++ tailWord_2366937).sum := by decide
  have hdescent : baseEnd_2366937 < baseStart_2366937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2366937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2366947 : List Nat := [1, 1, 1, 6, 2, 2, 1, 1, 1, 5, 2]
def baseStart_2366947 : Nat := 118140960795 + 2366947 * 2 ^ 59
def prefixEnd_2366947 : Nat := 4983230072969 + 3 ^ 40 * 2366947 * 2
def baseEnd_2366947 : Nat := 1215381494717656042677115

theorem tailTrace_2366947 : CollatzResearch.WordTrace tailWord_2366947 prefixEnd_2366947 1215381494717656042677115 := by
  unfold tailWord_2366947
  simp only [CollatzResearch.WordTrace]
  refine ⟨86329649355962736209331095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57553099570641824139554063 86329649355962736209331095)
  ·
    refine ⟨129494474033944104313996643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86329649355962736209331095 129494474033944104313996643)
    ·
      refine ⟨194241711050916156470994965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129494474033944104313996643 194241711050916156470994965)
      ·
        refine ⟨9105080205511694834577889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 194241711050916156470994965 9105080205511694834577889)
        ·
          refine ⟨6828810154133771125933417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9105080205511694834577889 6828810154133771125933417)
          ·
            refine ⟨5121607615600328344450063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6828810154133771125933417 5121607615600328344450063)
            ·
              refine ⟨7682411423400492516675095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5121607615600328344450063 7682411423400492516675095)
              ·
                refine ⟨11523617135100738775012643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7682411423400492516675095 11523617135100738775012643)
                ·
                  refine ⟨17285425702651108162518965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11523617135100738775012643 17285425702651108162518965)
                  ·
                    refine ⟨1620508659623541390236153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17285425702651108162518965 1620508659623541390236153)
                    ·
                      refine ⟨1215381494717656042677115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1620508659623541390236153 1215381494717656042677115)
                      ·
                        rfl

theorem cell23_2366947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 1, 1, 5, 2].length) (baseStart_2366947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2366947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2366947 prefixEnd_2366947 := by exact prefixLift 2366947
  have htrace : WordTrace (prefixWord ++ tailWord_2366947) baseStart_2366947 baseEnd_2366947 := by
    simpa [prefixWord, tailWord_2366947, baseEnd_2366947] using wordTrace_append hprefix tailTrace_2366947
  have hstable : (prefixWord ++ tailWord_2366947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2366947).length < 2 ^ (prefixWord ++ tailWord_2366947).sum := by decide
  have hdescent : baseEnd_2366947 < baseStart_2366947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2366947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2366970 : List Nat := [3, 1, 1, 1, 1, 2, 5, 1, 4, 4]
def baseStart_2366970 : Nat := 118140960795 + 2366970 * 2 ^ 59
def prefixEnd_2366970 : Nat := 4983230072969 + 3 ^ 40 * 2366970 * 2
def baseEnd_2366970 : Nat := 405131101590903150896503

theorem tailTrace_2366970 : CollatzResearch.WordTrace tailWord_2366970 prefixEnd_2366970 405131101590903150896503 := by
  unfold tailWord_2366970
  simp only [CollatzResearch.WordTrace]
  refine ⟨21582622058719852784354591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57553658823252940758278909 21582622058719852784354591)
  ·
    refine ⟨32373933088079779176531887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21582622058719852784354591 32373933088079779176531887)
    ·
      refine ⟨48560899632119668764797831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32373933088079779176531887 48560899632119668764797831)
      ·
        refine ⟨72841349448179503147196747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48560899632119668764797831 72841349448179503147196747)
        ·
          refine ⟨109262024172269254720795121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72841349448179503147196747 109262024172269254720795121)
          ·
            refine ⟨81946518129201941040596341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109262024172269254720795121 81946518129201941040596341)
            ·
              refine ⟨7682486074612681972555907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 81946518129201941040596341 7682486074612681972555907)
              ·
                refine ⟨11523729111919022958833861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7682486074612681972555907 11523729111919022958833861)
                ·
                  refine ⟨2160699208484816804781349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11523729111919022958833861 2160699208484816804781349)
                  ·
                    refine ⟨405131101590903150896503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2160699208484816804781349 405131101590903150896503)
                    ·
                      rfl

theorem cell23_2366970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 1, 4, 4].length) (baseStart_2366970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2366970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2366970 prefixEnd_2366970 := by exact prefixLift 2366970
  have htrace : WordTrace (prefixWord ++ tailWord_2366970) baseStart_2366970 baseEnd_2366970 := by
    simpa [prefixWord, tailWord_2366970, baseEnd_2366970] using wordTrace_append hprefix tailTrace_2366970
  have hstable : (prefixWord ++ tailWord_2366970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2366970).length < 2 ^ (prefixWord ++ tailWord_2366970).sum := by decide
  have hdescent : baseEnd_2366970 < baseStart_2366970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2366970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2366987 : List Nat := [1, 1, 1, 1, 8, 2, 1, 1, 1, 6]
def baseStart_2366987 : Nat := 118140960795 + 2366987 * 2 ^ 59
def prefixEnd_2366987 : Nat := 4983230072969 + 3 ^ 40 * 2366987 * 2
def baseEnd_2366987 : Nat := 405134011314611962058977

theorem tailTrace_2366987 : CollatzResearch.WordTrace tailWord_2366987 prefixEnd_2366987 405134011314611962058977 := by
  unfold tailWord_2366987
  simp only [CollatzResearch.WordTrace]
  refine ⟨86331108275817823040787215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57554072183878548693858143 86331108275817823040787215)
  ·
    refine ⟨129496662413726734561180823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86331108275817823040787215 129496662413726734561180823)
    ·
      refine ⟨194244993620590101841771235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129496662413726734561180823 194244993620590101841771235)
      ·
        refine ⟨291367490430885152762656853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194244993620590101841771235 291367490430885152762656853)
        ·
          refine ⟨3414462778486935383937385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 291367490430885152762656853 3414462778486935383937385)
          ·
            refine ⟨2560847083865201537953039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3414462778486935383937385 2560847083865201537953039)
            ·
              refine ⟨3841270625797802306929559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2560847083865201537953039 3841270625797802306929559)
              ·
                refine ⟨5761905938696703460394339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3841270625797802306929559 5761905938696703460394339)
                ·
                  refine ⟨8642858908045055190591509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5761905938696703460394339 8642858908045055190591509)
                  ·
                    refine ⟨405134011314611962058977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8642858908045055190591509 405134011314611962058977)
                    ·
                      rfl

theorem cell23_2366987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 1, 1, 6].length) (baseStart_2366987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2366987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2366987 prefixEnd_2366987 := by exact prefixLift 2366987
  have htrace : WordTrace (prefixWord ++ tailWord_2366987) baseStart_2366987 baseEnd_2366987 := by
    simpa [prefixWord, tailWord_2366987, baseEnd_2366987] using wordTrace_append hprefix tailTrace_2366987
  have hstable : (prefixWord ++ tailWord_2366987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2366987).length < 2 ^ (prefixWord ++ tailWord_2366987).sum := by decide
  have hdescent : baseEnd_2366987 < baseStart_2366987 := by decide
  rcases family_descends (prefixWord ++ tailWord_2366987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2366997 : List Nat := [1, 3, 2, 1, 3, 2, 1, 4, 1, 2, 3]
def baseStart_2366997 : Nat := 118140960795 + 2366997 * 2 ^ 59
def prefixEnd_2366997 : Nat := 4983230072969 + 3 ^ 40 * 2366997 * 2
def baseEnd_2366997 : Nat := 1215407168750380847051885

theorem tailTrace_2366997 : CollatzResearch.WordTrace tailWord_2366997 prefixEnd_2366997 1215407168750380847051885 := by
  unfold tailWord_2366997
  simp only [CollatzResearch.WordTrace]
  refine ⟨86331473005781594748651245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57554315337187729832434163 86331473005781594748651245)
  ·
    refine ⟨32374302377168098030744217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86331473005781594748651245 32374302377168098030744217)
    ·
      refine ⟨24280726782876073523058163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32374302377168098030744217 24280726782876073523058163)
      ·
        refine ⟨36421090174314110284587245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24280726782876073523058163 36421090174314110284587245)
        ·
          refine ⟨13657908815367791356720217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36421090174314110284587245 13657908815367791356720217)
          ·
            refine ⟨10243431611525843517540163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13657908815367791356720217 10243431611525843517540163)
            ·
              refine ⟨15365147417288765276310245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10243431611525843517540163 15365147417288765276310245)
              ·
                refine ⟨2880965140741643489308171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15365147417288765276310245 2880965140741643489308171)
                ·
                  refine ⟨4321447711112465233962257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2880965140741643489308171 4321447711112465233962257)
                  ·
                    refine ⟨3241085783334348925471693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4321447711112465233962257 3241085783334348925471693)
                    ·
                      refine ⟨1215407168750380847051885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3241085783334348925471693 1215407168750380847051885)
                      ·
                        rfl

theorem cell23_2366997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 4, 1, 2, 3].length) (baseStart_2366997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2366997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2366997 prefixEnd_2366997 := by exact prefixLift 2366997
  have htrace : WordTrace (prefixWord ++ tailWord_2366997) baseStart_2366997 baseEnd_2366997 := by
    simpa [prefixWord, tailWord_2366997, baseEnd_2366997] using wordTrace_append hprefix tailTrace_2366997
  have hstable : (prefixWord ++ tailWord_2366997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2366997).length < 2 ^ (prefixWord ++ tailWord_2366997).sum := by decide
  have hdescent : baseEnd_2366997 < baseStart_2366997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2366997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367000 : List Nat := [2, 1, 2, 3, 4, 1, 1, 9]
def baseStart_2367000 : Nat := 118140960795 + 2367000 * 2 ^ 59
def prefixEnd_2367000 : Nat := 4983230072969 + 3 ^ 40 * 2367000 * 2
def baseEnd_2367000 : Nat := 45015137377494234641273

theorem tailTrace_2367000 : CollatzResearch.WordTrace tailWord_2367000 prefixEnd_2367000 45015137377494234641273 := by
  unfold tailWord_2367000
  simp only [CollatzResearch.WordTrace]
  refine ⟨43165791212385363130505227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57554388283180484174006969 43165791212385363130505227)
  ·
    refine ⟨64748686818578044695757841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43165791212385363130505227 64748686818578044695757841)
    ·
      refine ⟨48561515113933533521818381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64748686818578044695757841 48561515113933533521818381)
      ·
        refine ⟨18210568167725075070681893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48561515113933533521818381 18210568167725075070681893)
        ·
          refine ⟨3414481531448451575752855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18210568167725075070681893 3414481531448451575752855)
          ·
            refine ⟨5121722297172677363629283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3414481531448451575752855 5121722297172677363629283)
            ·
              refine ⟨7682583445759016045443925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5121722297172677363629283 7682583445759016045443925)
              ·
                refine ⟨45015137377494234641273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7682583445759016045443925 45015137377494234641273)
                ·
                  rfl

theorem cell23_2367000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 9].length) (baseStart_2367000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2367000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2367000 prefixEnd_2367000 := by exact prefixLift 2367000
  have htrace : WordTrace (prefixWord ++ tailWord_2367000) baseStart_2367000 baseEnd_2367000 := by
    simpa [prefixWord, tailWord_2367000, baseEnd_2367000] using wordTrace_append hprefix tailTrace_2367000
  have hstable : (prefixWord ++ tailWord_2367000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367000).length < 2 ^ (prefixWord ++ tailWord_2367000).sum := by decide
  have hdescent : baseEnd_2367000 < baseStart_2367000 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367013 : List Nat := [1, 3, 1, 2, 2, 1, 1, 2, 1, 9]
def baseStart_2367013 : Nat := 118140960795 + 2367013 * 2 ^ 59
def prefixEnd_2367013 : Nat := 4983230072969 + 3 ^ 40 * 2367013 * 2
def baseEnd_2367013 : Nat := 405138461480284261483937

theorem tailTrace_2367013 : CollatzResearch.WordTrace tailWord_2367013 prefixEnd_2367013 405138461480284261483937 := by
  unfold tailWord_2367013
  simp only [CollatzResearch.WordTrace]
  refine ⟨86332056573723629481233693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57554704382482419654155795 86332056573723629481233693)
  ·
    refine ⟨32374521215146361055462635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86332056573723629481233693 32374521215146361055462635)
    ·
      refine ⟨48561781822719541583193953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32374521215146361055462635 48561781822719541583193953)
      ·
        refine ⟨36421336367039656187395465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48561781822719541583193953 36421336367039656187395465)
        ·
          refine ⟨27316002275279742140546599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36421336367039656187395465 27316002275279742140546599)
          ·
            refine ⟨40974003412919613210819899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27316002275279742140546599 40974003412919613210819899)
            ·
              refine ⟨61461005119379419816229849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40974003412919613210819899 61461005119379419816229849)
              ·
                refine ⟨46095753839534564862172387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61461005119379419816229849 46095753839534564862172387)
                ·
                  refine ⟨69143630759301847293258581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46095753839534564862172387 69143630759301847293258581)
                  ·
                    refine ⟨405138461480284261483937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 69143630759301847293258581 405138461480284261483937)
                    ·
                      rfl

theorem cell23_2367013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 9].length) (baseStart_2367013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2367013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2367013 prefixEnd_2367013 := by exact prefixLift 2367013
  have htrace : WordTrace (prefixWord ++ tailWord_2367013) baseStart_2367013 baseEnd_2367013 := by
    simpa [prefixWord, tailWord_2367013, baseEnd_2367013] using wordTrace_append hprefix tailTrace_2367013
  have hstable : (prefixWord ++ tailWord_2367013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367013).length < 2 ^ (prefixWord ++ tailWord_2367013).sum := by decide
  have hdescent : baseEnd_2367013 < baseStart_2367013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367027 : List Nat := [1, 1, 1, 2, 4, 3, 2, 1, 4, 1, 3]
def baseStart_2367027 : Nat := 118140960795 + 2367027 * 2 ^ 59
def prefixEnd_2367027 : Nat := 4983230072969 + 3 ^ 40 * 2367027 * 2
def baseEnd_2367027 : Nat := 1215422573170015729676747

theorem tailTrace_2367027 : CollatzResearch.WordTrace tailWord_2367027 prefixEnd_2367027 1215422573170015729676747 := by
  unfold tailWord_2367027
  simp only [CollatzResearch.WordTrace]
  refine ⟨86332567195672909872243335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57555044797115273248162223 86332567195672909872243335)
  ·
    refine ⟨129498850793509364808365003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86332567195672909872243335 129498850793509364808365003)
    ·
      refine ⟨194248276190264047212547505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129498850793509364808365003 194248276190264047212547505)
      ·
        refine ⟨145686207142698035409410629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194248276190264047212547505 145686207142698035409410629)
        ·
          refine ⟨27316163839255881639264493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 145686207142698035409410629 27316163839255881639264493)
          ·
            refine ⟨10243561439720955614724185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27316163839255881639264493 10243561439720955614724185)
            ·
              refine ⟨7682671079790716711043139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10243561439720955614724185 7682671079790716711043139)
              ·
                refine ⟨11524006619686075066564709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7682671079790716711043139 11524006619686075066564709)
                ·
                  refine ⟨2160751241191139074980883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11524006619686075066564709 2160751241191139074980883)
                  ·
                    refine ⟨3241126861786708612471325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2160751241191139074980883 3241126861786708612471325)
                    ·
                      refine ⟨1215422573170015729676747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3241126861786708612471325 1215422573170015729676747)
                      ·
                        rfl

theorem cell23_2367027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 1, 4, 1, 3].length) (baseStart_2367027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2367027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2367027 prefixEnd_2367027 := by exact prefixLift 2367027
  have htrace : WordTrace (prefixWord ++ tailWord_2367027) baseStart_2367027 baseEnd_2367027 := by
    simpa [prefixWord, tailWord_2367027, baseEnd_2367027] using wordTrace_append hprefix tailTrace_2367027
  have hstable : (prefixWord ++ tailWord_2367027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367027).length < 2 ^ (prefixWord ++ tailWord_2367027).sum := by decide
  have hdescent : baseEnd_2367027 < baseStart_2367027 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367101 : List Nat := [1, 4, 1, 1, 4, 1, 2, 3, 2, 2, 2]
def baseStart_2367101 : Nat := 118140960795 + 2367101 * 2 ^ 59
def prefixEnd_2367101 : Nat := 4983230072969 + 3 ^ 40 * 2367101 * 2
def baseEnd_2367101 : Nat := 1215460570738448440151407

theorem tailTrace_2367101 : CollatzResearch.WordTrace tailWord_2367101 prefixEnd_2367101 1215460570738448440151407 := by
  unfold tailWord_2367101
  simp only [CollatzResearch.WordTrace]
  refine ⟨86335266197404820510437157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57556844131603213673624771 86335266197404820510437157)
  ·
    refine ⟨16187862412013403845706967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86335266197404820510437157 16187862412013403845706967)
    ·
      refine ⟨24281793618020105768560451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16187862412013403845706967 24281793618020105768560451)
      ·
        refine ⟨36422690427030158652840677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24281793618020105768560451 36422690427030158652840677)
        ·
          refine ⟨6829254455068154747407627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36422690427030158652840677 6829254455068154747407627)
          ·
            refine ⟨10243881682602232121111441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6829254455068154747407627 10243881682602232121111441)
            ·
              refine ⟨7682911261951674090833581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10243881682602232121111441 7682911261951674090833581)
              ·
                refine ⟨2881091723231877784062593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7682911261951674090833581 2881091723231877784062593)
                ·
                  refine ⟨2160818792423908338046945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2881091723231877784062593 2160818792423908338046945)
                  ·
                    refine ⟨1620614094317931253535209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2160818792423908338046945 1620614094317931253535209)
                    ·
                      refine ⟨1215460570738448440151407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1620614094317931253535209 1215460570738448440151407)
                      ·
                        rfl

theorem cell23_2367101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 3, 2, 2, 2].length) (baseStart_2367101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2367101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2367101 prefixEnd_2367101 := by exact prefixLift 2367101
  have htrace : WordTrace (prefixWord ++ tailWord_2367101) baseStart_2367101 baseEnd_2367101 := by
    simpa [prefixWord, tailWord_2367101, baseEnd_2367101] using wordTrace_append hprefix tailTrace_2367101
  have hstable : (prefixWord ++ tailWord_2367101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367101).length < 2 ^ (prefixWord ++ tailWord_2367101).sum := by decide
  have hdescent : baseEnd_2367101 < baseStart_2367101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367134 : List Nat := [4, 3, 1, 1, 1, 2, 1, 2, 2, 3, 3]
def baseStart_2367134 : Nat := 118140960795 + 2367134 * 2 ^ 59
def prefixEnd_2367134 : Nat := 4983230072969 + 3 ^ 40 * 2367134 * 2
def baseEnd_2367134 : Nat := 1215477515600046811038755

theorem tailTrace_2367134 : CollatzResearch.WordTrace tailWord_2367134 prefixEnd_2367134 1215477515600046811038755 := by
  unfold tailWord_2367134
  simp only [CollatzResearch.WordTrace]
  refine ⟨10792058725785658393298557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57557646537523511430925637 10792058725785658393298557)
  ·
    refine ⟨4047022022169621897486959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10792058725785658393298557 4047022022169621897486959)
    ·
      refine ⟨6070533033254432846230439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4047022022169621897486959 6070533033254432846230439)
      ·
        refine ⟨9105799549881649269345659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6070533033254432846230439 9105799549881649269345659)
        ·
          refine ⟨13658699324822473904018489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9105799549881649269345659 13658699324822473904018489)
          ·
            refine ⟨10244024493616855428013867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13658699324822473904018489 10244024493616855428013867)
            ·
              refine ⟨15366036740425283142020801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10244024493616855428013867 15366036740425283142020801)
              ·
                refine ⟨11524527555318962356515601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15366036740425283142020801 11524527555318962356515601)
                ·
                  refine ⟨8643395666489221767386701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11524527555318962356515601 8643395666489221767386701)
                  ·
                    refine ⟨3241273374933458162770013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8643395666489221767386701 3241273374933458162770013)
                    ·
                      refine ⟨1215477515600046811038755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3241273374933458162770013 1215477515600046811038755)
                      ·
                        rfl

theorem cell23_2367134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_2367134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2367134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2367134 prefixEnd_2367134 := by exact prefixLift 2367134
  have htrace : WordTrace (prefixWord ++ tailWord_2367134) baseStart_2367134 baseEnd_2367134 := by
    simpa [prefixWord, tailWord_2367134, baseEnd_2367134] using wordTrace_append hprefix tailTrace_2367134
  have hstable : (prefixWord ++ tailWord_2367134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367134).length < 2 ^ (prefixWord ++ tailWord_2367134).sum := by decide
  have hdescent : baseEnd_2367134 < baseStart_2367134 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367135 : List Nat := [1, 1, 2, 7, 1, 2, 1, 2, 2, 2, 2]
def baseStart_2367135 : Nat := 118140960795 + 2367135 * 2 ^ 59
def prefixEnd_2367135 : Nat := 4983230072969 + 3 ^ 40 * 2367135 * 2
def baseEnd_2367135 : Nat := 1215478029080701307126251

theorem tailTrace_2367135 : CollatzResearch.WordTrace tailWord_2367135 prefixEnd_2367135 1215478029080701307126251 := by
  unfold tailWord_2367135
  simp only [CollatzResearch.WordTrace]
  refine ⟨86336506279281644317174859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57557670852854429544783239 86336506279281644317174859)
  ·
    refine ⟨129504759418922466475762289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86336506279281644317174859 129504759418922466475762289)
    ·
      refine ⟨97128569564191849856821717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129504759418922466475762289 97128569564191849856821717)
      ·
        refine ⟨2276450849160746481019259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 97128569564191849856821717 2276450849160746481019259)
        ·
          refine ⟨3414676273741119721528889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2276450849160746481019259 3414676273741119721528889)
          ·
            refine ⟨2561007205305839791146667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3414676273741119721528889 2561007205305839791146667)
            ·
              refine ⟨3841510807958759686720001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2561007205305839791146667 3841510807958759686720001)
              ·
                refine ⟨2881133105969069765040001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3841510807958759686720001 2881133105969069765040001)
                ·
                  refine ⟨2160849829476802323780001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2881133105969069765040001 2160849829476802323780001)
                  ·
                    refine ⟨1620637372107601742835001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2160849829476802323780001 1620637372107601742835001)
                    ·
                      refine ⟨1215478029080701307126251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1620637372107601742835001 1215478029080701307126251)
                      ·
                        rfl

theorem cell23_2367135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_2367135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2367135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2367135 prefixEnd_2367135 := by exact prefixLift 2367135
  have htrace : WordTrace (prefixWord ++ tailWord_2367135) baseStart_2367135 baseEnd_2367135 := by
    simpa [prefixWord, tailWord_2367135, baseEnd_2367135] using wordTrace_append hprefix tailTrace_2367135
  have hstable : (prefixWord ++ tailWord_2367135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367135).length < 2 ^ (prefixWord ++ tailWord_2367135).sum := by decide
  have hdescent : baseEnd_2367135 < baseStart_2367135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367167 : List Nat := [1, 1, 2, 2, 2, 3, 1, 4, 3, 4]
def baseStart_2367167 : Nat := 118140960795 + 2367167 * 2 ^ 59
def prefixEnd_2367167 : Nat := 4983230072969 + 3 ^ 40 * 2367167 * 2
def baseEnd_2367167 : Nat := 405164820153881727308701

theorem tailTrace_2367167 : CollatzResearch.WordTrace tailWord_2367167 prefixEnd_2367167 405164820153881727308701 := by
  unfold tailWord_2367167
  simp only [CollatzResearch.WordTrace]
  refine ⟨86337673415165713782339755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57558448943443809188226503 86337673415165713782339755)
  ·
    refine ⟨129506510122748570673509633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86337673415165713782339755 129506510122748570673509633)
    ·
      refine ⟨97129882592061428005132225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129506510122748570673509633 97129882592061428005132225)
      ·
        refine ⟨72847411944046071003849169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97129882592061428005132225 72847411944046071003849169)
        ·
          refine ⟨54635558958034553252886877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72847411944046071003849169 54635558958034553252886877)
          ·
            refine ⟨20488334609262957469832579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54635558958034553252886877 20488334609262957469832579)
            ·
              refine ⟨30732501913894436204748869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20488334609262957469832579 30732501913894436204748869)
              ·
                refine ⟨5762344108855206788390413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30732501913894436204748869 5762344108855206788390413)
                ·
                  refine ⟨2160879040820702545646405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5762344108855206788390413 2160879040820702545646405)
                  ·
                    refine ⟨405164820153881727308701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2160879040820702545646405 405164820153881727308701)
                    ·
                      rfl

theorem cell23_2367167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 4, 3, 4].length) (baseStart_2367167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2367167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2367167 prefixEnd_2367167 := by exact prefixLift 2367167
  have htrace : WordTrace (prefixWord ++ tailWord_2367167) baseStart_2367167 baseEnd_2367167 := by
    simpa [prefixWord, tailWord_2367167, baseEnd_2367167] using wordTrace_append hprefix tailTrace_2367167
  have hstable : (prefixWord ++ tailWord_2367167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367167).length < 2 ^ (prefixWord ++ tailWord_2367167).sum := by decide
  have hdescent : baseEnd_2367167 < baseStart_2367167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367184 : List Nat := [2, 1, 1, 1, 1, 2, 1, 9, 1, 4]
def baseStart_2367184 : Nat := 118140960795 + 2367184 * 2 ^ 59
def prefixEnd_2367184 : Nat := 4983230072969 + 3 ^ 40 * 2367184 * 2
def baseEnd_2367184 : Nat := 405167729877590538471175

theorem tailTrace_2367184 : CollatzResearch.WordTrace tailWord_2367184 prefixEnd_2367184 405167729877590538471175 := by
  unfold tailWord_2367184
  simp only [CollatzResearch.WordTrace]
  refine ⟨43169146728052062842854303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57558862304069417123805737 43169146728052062842854303)
  ·
    refine ⟨64753720092078094264281455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43169146728052062842854303 64753720092078094264281455)
    ·
      refine ⟨97130580138117141396422183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64753720092078094264281455 97130580138117141396422183)
      ·
        refine ⟨145695870207175712094633275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97130580138117141396422183 145695870207175712094633275)
        ·
          refine ⟨218543805310763568141949913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145695870207175712094633275 218543805310763568141949913)
          ·
            refine ⟨163907853983072676106462435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 218543805310763568141949913 163907853983072676106462435)
            ·
              refine ⟨245861780974609014159693653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163907853983072676106462435 245861780974609014159693653)
              ·
                refine ⟨1440596372898099692341955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 245861780974609014159693653 1440596372898099692341955)
                ·
                  refine ⟨2160894559347149538512933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1440596372898099692341955 2160894559347149538512933)
                  ·
                    refine ⟨405167729877590538471175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2160894559347149538512933 405167729877590538471175)
                    ·
                      rfl

theorem cell23_2367184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 9, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 9, 1, 4].length) (baseStart_2367184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2367184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2367184 prefixEnd_2367184 := by exact prefixLift 2367184
  have htrace : WordTrace (prefixWord ++ tailWord_2367184) baseStart_2367184 baseEnd_2367184 := by
    simpa [prefixWord, tailWord_2367184, baseEnd_2367184] using wordTrace_append hprefix tailTrace_2367184
  have hstable : (prefixWord ++ tailWord_2367184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367184).length < 2 ^ (prefixWord ++ tailWord_2367184).sum := by decide
  have hdescent : baseEnd_2367184 < baseStart_2367184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367194 : List Nat := [3, 1, 1, 2, 2, 4, 1, 2, 2, 2, 3]
def baseStart_2367194 : Nat := 118140960795 + 2367194 * 2 ^ 59
def prefixEnd_2367194 : Nat := 4983230072969 + 3 ^ 40 * 2367194 * 2
def baseEnd_2367194 : Nat := 1215508324439316576288479

theorem tailTrace_2367194 : CollatzResearch.WordTrace tailWord_2367194 prefixEnd_2367194 1215508324439316576288479 := by
  unfold tailWord_2367194
  simp only [CollatzResearch.WordTrace]
  refine ⟨21584664546516974348393159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57559105457378598262381757 21584664546516974348393159)
  ·
    refine ⟨32376996819775461522589739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21584664546516974348393159 32376996819775461522589739)
    ·
      refine ⟨48565495229663192283884609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32376996819775461522589739 48565495229663192283884609)
      ·
        refine ⟨36424121422247394212913457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48565495229663192283884609 36424121422247394212913457)
        ·
          refine ⟨27318091066685545659685093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36424121422247394212913457 27318091066685545659685093)
          ·
            refine ⟨5122142075003539811190955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27318091066685545659685093 5122142075003539811190955)
            ·
              refine ⟨7683213112505309716786433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5122142075003539811190955 7683213112505309716786433)
              ·
                refine ⟨5762409834378982287589825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7683213112505309716786433 5762409834378982287589825)
                ·
                  refine ⟨4321807375784236715692369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5762409834378982287589825 4321807375784236715692369)
                  ·
                    refine ⟨3241355531838177536769277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4321807375784236715692369 3241355531838177536769277)
                    ·
                      refine ⟨1215508324439316576288479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3241355531838177536769277 1215508324439316576288479)
                      ·
                        rfl

theorem cell23_2367194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 2, 2, 2, 3].length) (baseStart_2367194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2367194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2367194 prefixEnd_2367194 := by exact prefixLift 2367194
  have htrace : WordTrace (prefixWord ++ tailWord_2367194) baseStart_2367194 baseEnd_2367194 := by
    simpa [prefixWord, tailWord_2367194, baseEnd_2367194] using wordTrace_append hprefix tailTrace_2367194
  have hstable : (prefixWord ++ tailWord_2367194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367194).length < 2 ^ (prefixWord ++ tailWord_2367194).sum := by decide
  have hdescent : baseEnd_2367194 < baseStart_2367194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367200 : List Nat := [2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 8]
def baseStart_2367200 : Nat := 118140960795 + 2367200 * 2 ^ 59
def prefixEnd_2367200 : Nat := 4983230072969 + 3 ^ 40 * 2367200 * 2
def baseEnd_2367200 : Nat := 1215511405323243552813451

theorem tailTrace_2367200 : CollatzResearch.WordTrace tailWord_2367200 prefixEnd_2367200 1215511405323243552813451 := by
  unfold tailWord_2367200
  simp only [CollatzResearch.WordTrace]
  refine ⟨43169438512023080209145527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57559251349364106945527369 43169438512023080209145527)
  ·
    refine ⟨64754157768034620313718291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43169438512023080209145527 64754157768034620313718291)
    ·
      refine ⟨97131236652051930470577437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64754157768034620313718291 97131236652051930470577437)
      ·
        refine ⟨36424213744519473926466539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97131236652051930470577437 36424213744519473926466539)
        ·
          refine ⟨54636320616779210889699809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36424213744519473926466539 54636320616779210889699809)
          ·
            refine ⟨40977240462584408167274857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54636320616779210889699809 40977240462584408167274857)
            ·
              refine ⟨30732930346938306125456143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40977240462584408167274857 30732930346938306125456143)
              ·
                refine ⟨46099395520407459188184215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30732930346938306125456143 46099395520407459188184215)
                ·
                  refine ⟨69149093280611188782276323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46099395520407459188184215 69149093280611188782276323)
                  ·
                    refine ⟨103723639920916783173414485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 69149093280611188782276323 103723639920916783173414485)
                    ·
                      refine ⟨1215511405323243552813451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 103723639920916783173414485 1215511405323243552813451)
                      ·
                        rfl

theorem cell23_2367200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_2367200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2367200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2367200 prefixEnd_2367200 := by exact prefixLift 2367200
  have htrace : WordTrace (prefixWord ++ tailWord_2367200) baseStart_2367200 baseEnd_2367200 := by
    simpa [prefixWord, tailWord_2367200, baseEnd_2367200] using wordTrace_append hprefix tailTrace_2367200
  have hstable : (prefixWord ++ tailWord_2367200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367200).length < 2 ^ (prefixWord ++ tailWord_2367200).sum := by decide
  have hdescent : baseEnd_2367200 < baseStart_2367200 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367201 : List Nat := [1, 2, 3, 1, 5, 2, 1, 1, 3, 4]
def baseStart_2367201 : Nat := 118140960795 + 2367201 * 2 ^ 59
def prefixEnd_2367201 : Nat := 4983230072969 + 3 ^ 40 * 2367201 * 2
def baseEnd_2367201 : Nat := 405170639601299349633649

theorem tailTrace_2367201 : CollatzResearch.WordTrace tailWord_2367201 prefixEnd_2367201 405170639601299349633649 := by
  unfold tailWord_2367201
  simp only [CollatzResearch.WordTrace]
  refine ⟨86338913497042537589077457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57559275664695025059384971 86338913497042537589077457)
  ·
    refine ⟨64754185122781903191808093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86338913497042537589077457 64754185122781903191808093)
    ·
      refine ⟨24282819421043213696928035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64754185122781903191808093 24282819421043213696928035)
      ·
        refine ⟨36424229131564820545392053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24282819421043213696928035 36424229131564820545392053)
        ·
          refine ⟨3414771481084201926130505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36424229131564820545392053 3414771481084201926130505)
          ·
            refine ⟨2561078610813151444597879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3414771481084201926130505 2561078610813151444597879)
            ·
              refine ⟨3841617916219727166896819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2561078610813151444597879 3841617916219727166896819)
              ·
                refine ⟨5762426874329590750345229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3841617916219727166896819 5762426874329590750345229)
                ·
                  refine ⟨2160910077873596531379461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5762426874329590750345229 2160910077873596531379461)
                  ·
                    refine ⟨405170639601299349633649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2160910077873596531379461 405170639601299349633649)
                    ·
                      rfl

theorem cell23_2367201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 1, 3, 4].length) (baseStart_2367201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2367201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2367201 prefixEnd_2367201 := by exact prefixLift 2367201
  have htrace : WordTrace (prefixWord ++ tailWord_2367201) baseStart_2367201 baseEnd_2367201 := by
    simpa [prefixWord, tailWord_2367201, baseEnd_2367201] using wordTrace_append hprefix tailTrace_2367201
  have hstable : (prefixWord ++ tailWord_2367201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367201).length < 2 ^ (prefixWord ++ tailWord_2367201).sum := by decide
  have hdescent : baseEnd_2367201 < baseStart_2367201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367227 : List Nat := [1, 1, 1, 1, 1, 3, 1, 8, 1, 5]
def baseStart_2367227 : Nat := 118140960795 + 2367227 * 2 ^ 59
def prefixEnd_2367227 : Nat := 4983230072969 + 3 ^ 40 * 2367227 * 2
def baseEnd_2367227 : Nat := 405175089766971649058609

theorem tailTrace_2367227 : CollatzResearch.WordTrace tailWord_2367227 prefixEnd_2367227 405175089766971649058609 := by
  unfold tailWord_2367227
  simp only [CollatzResearch.WordTrace]
  refine ⟨86339861794948344029523935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57559907863298896019682623 86339861794948344029523935)
  ·
    refine ⟨129509792692422516044285903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86339861794948344029523935 129509792692422516044285903)
    ·
      refine ⟨194264689038633774066428855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129509792692422516044285903 194264689038633774066428855)
      ·
        refine ⟨291397033557950661099643283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194264689038633774066428855 291397033557950661099643283)
        ·
          refine ⟨437095550336925991649464925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 291397033557950661099643283 437095550336925991649464925)
          ·
            refine ⟨163910831376347246868549347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 437095550336925991649464925 163910831376347246868549347)
            ·
              refine ⟨245866247064520870302824021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163910831376347246868549347 245866247064520870302824021)
              ·
                refine ⟨2881245082787353948861219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 245866247064520870302824021 2881245082787353948861219)
                ·
                  refine ⟨4321867624181030923291829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2881245082787353948861219 4321867624181030923291829)
                  ·
                    refine ⟨405175089766971649058609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4321867624181030923291829 405175089766971649058609)
                    ·
                      rfl

theorem cell23_2367227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 8, 1, 5].length) (baseStart_2367227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2367227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2367227 prefixEnd_2367227 := by exact prefixLift 2367227
  have htrace : WordTrace (prefixWord ++ tailWord_2367227) baseStart_2367227 baseEnd_2367227 := by
    simpa [prefixWord, tailWord_2367227, baseEnd_2367227] using wordTrace_append hprefix tailTrace_2367227
  have hstable : (prefixWord ++ tailWord_2367227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367227).length < 2 ^ (prefixWord ++ tailWord_2367227).sum := by decide
  have hdescent : baseEnd_2367227 < baseStart_2367227 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367241 : List Nat := [1, 2, 1, 1, 3, 2, 1, 7, 1, 1, 3]
def baseStart_2367241 : Nat := 118140960795 + 2367241 * 2 ^ 59
def prefixEnd_2367241 : Nat := 4983230072969 + 3 ^ 40 * 2367241 * 2
def baseEnd_2367241 : Nat := 1215532458030077892400763

theorem tailTrace_2367241 : CollatzResearch.WordTrace tailWord_2367241 prefixEnd_2367241 1215532458030077892400763 := by
  unfold tailWord_2367241
  simp only [CollatzResearch.WordTrace]
  refine ⟨86340372416897624420533577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57560248277931749613689051 86340372416897624420533577)
  ·
    refine ⟨64755279312673218315400183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86340372416897624420533577 64755279312673218315400183)
    ·
      refine ⟨97132918969009827473100275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64755279312673218315400183 97132918969009827473100275)
      ·
        refine ⟨145699378453514741209650413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97132918969009827473100275 145699378453514741209650413)
        ·
          refine ⟨54637266920068027953618905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 145699378453514741209650413 54637266920068027953618905)
          ·
            refine ⟨40977950190051020965214179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54637266920068027953618905 40977950190051020965214179)
            ·
              refine ⟨61466925285076531447821269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40977950190051020965214179 61466925285076531447821269)
              ·
                refine ⟨1440631061368981205808311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 61466925285076531447821269 1440631061368981205808311)
                ·
                  refine ⟨2160946592053471808712467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1440631061368981205808311 2160946592053471808712467)
                  ·
                    refine ⟨3241419888080207713068701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2160946592053471808712467 3241419888080207713068701)
                    ·
                      refine ⟨1215532458030077892400763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3241419888080207713068701 1215532458030077892400763)
                      ·
                        rfl

theorem cell23_2367241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 7, 1, 1, 3].length) (baseStart_2367241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2367241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2367241 prefixEnd_2367241 := by exact prefixLift 2367241
  have htrace : WordTrace (prefixWord ++ tailWord_2367241) baseStart_2367241 baseEnd_2367241 := by
    simpa [prefixWord, tailWord_2367241, baseEnd_2367241] using wordTrace_append hprefix tailTrace_2367241
  have hstable : (prefixWord ++ tailWord_2367241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367241).length < 2 ^ (prefixWord ++ tailWord_2367241).sum := by decide
  have hdescent : baseEnd_2367241 < baseStart_2367241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367252 : List Nat := [2, 4, 4, 1, 1, 1, 1, 4, 1, 4]
def baseStart_2367252 : Nat := 118140960795 + 2367252 * 2 ^ 59
def prefixEnd_2367252 : Nat := 4983230072969 + 3 ^ 40 * 2367252 * 2
def baseEnd_2367252 : Nat := 405179368772425783121071

theorem tailTrace_2367252 : CollatzResearch.WordTrace tailWord_2367252 prefixEnd_2367252 405179368772425783121071 := by
  unfold tailWord_2367252
  simp only [CollatzResearch.WordTrace]
  refine ⟨43170386809928886649592005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57560515746571848866122673 43170386809928886649592005)
  ·
    refine ⟨8094447526861666246798501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43170386809928886649592005 8094447526861666246798501)
    ·
      refine ⟨1517708911286562421274719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8094447526861666246798501 1517708911286562421274719)
      ·
        refine ⟨2276563366929843631912079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1517708911286562421274719 2276563366929843631912079)
        ·
          refine ⟨3414845050394765447868119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2276563366929843631912079 3414845050394765447868119)
          ·
            refine ⟨5122267575592148171802179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3414845050394765447868119 5122267575592148171802179)
            ·
              refine ⟨7683401363388222257703269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5122267575592148171802179 7683401363388222257703269)
              ·
                refine ⟨1440637755635291673319363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7683401363388222257703269 1440637755635291673319363)
                ·
                  refine ⟨2160956633452937509979045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1440637755635291673319363 2160956633452937509979045)
                  ·
                    refine ⟨405179368772425783121071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2160956633452937509979045 405179368772425783121071)
                    ·
                      rfl

theorem cell23_2367252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_2367252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2367252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2367252 prefixEnd_2367252 := by exact prefixLift 2367252
  have htrace : WordTrace (prefixWord ++ tailWord_2367252) baseStart_2367252 baseEnd_2367252 := by
    simpa [prefixWord, tailWord_2367252, baseEnd_2367252] using wordTrace_append hprefix tailTrace_2367252
  have hstable : (prefixWord ++ tailWord_2367252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367252).length < 2 ^ (prefixWord ++ tailWord_2367252).sum := by decide
  have hdescent : baseEnd_2367252 < baseStart_2367252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367257 : List Nat := [1, 2, 1, 2, 1, 1, 1, 2, 8, 4]
def baseStart_2367257 : Nat := 118140960795 + 2367257 * 2 ^ 59
def prefixEnd_2367257 : Nat := 4983230072969 + 3 ^ 40 * 2367257 * 2
def baseEnd_2367257 : Nat := 405180224573516609933563

theorem tailTrace_2367257 : CollatzResearch.WordTrace tailWord_2367257 prefixEnd_2367257 405180224573516609933563 := by
  unfold tailWord_2367257
  simp only [CollatzResearch.WordTrace]
  refine ⟨86340955984839659153116025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57560637323226439435410683 86340955984839659153116025)
  ·
    refine ⟨64755716988629744364837019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86340955984839659153116025 64755716988629744364837019)
    ·
      refine ⟨97133575482944616547255529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64755716988629744364837019 97133575482944616547255529)
      ·
        refine ⟨72850181612208462410441647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97133575482944616547255529 72850181612208462410441647)
        ·
          refine ⟨109275272418312693615662471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72850181612208462410441647 109275272418312693615662471)
          ·
            refine ⟨163912908627469040423493707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109275272418312693615662471 163912908627469040423493707)
            ·
              refine ⟨245869362941203560635240561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163912908627469040423493707 245869362941203560635240561)
              ·
                refine ⟨184402022205902670476430421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 245869362941203560635240561 184402022205902670476430421)
                ·
                  refine ⟨2160961197725421919645669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 184402022205902670476430421 2160961197725421919645669)
                  ·
                    refine ⟨405180224573516609933563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2160961197725421919645669 405180224573516609933563)
                    ·
                      rfl

theorem cell23_2367257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 8, 4].length) (baseStart_2367257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2367257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2367257 prefixEnd_2367257 := by exact prefixLift 2367257
  have htrace : WordTrace (prefixWord ++ tailWord_2367257) baseStart_2367257 baseEnd_2367257 := by
    simpa [prefixWord, tailWord_2367257, baseEnd_2367257] using wordTrace_append hprefix tailTrace_2367257
  have hstable : (prefixWord ++ tailWord_2367257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367257).length < 2 ^ (prefixWord ++ tailWord_2367257).sum := by decide
  have hdescent : baseEnd_2367257 < baseStart_2367257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367258 : List Nat := [3, 1, 1, 3, 2, 3, 1, 4, 1, 1, 3]
def baseStart_2367258 : Nat := 118140960795 + 2367258 * 2 ^ 59
def prefixEnd_2367258 : Nat := 4983230072969 + 3 ^ 40 * 2367258 * 2
def baseEnd_2367258 : Nat := 1215541187201204325888185

theorem tailTrace_2367258 : CollatzResearch.WordTrace tailWord_2367258 prefixEnd_2367258 1215541187201204325888185 := by
  unfold tailWord_2367258
  simp only [CollatzResearch.WordTrace]
  refine ⟨21585248114459009080975607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57560661638557357549268285 21585248114459009080975607)
  ·
    refine ⟨32377872171688513621463411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21585248114459009080975607 32377872171688513621463411)
    ·
      refine ⟨48566808257532770432195117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32377872171688513621463411 48566808257532770432195117)
      ·
        refine ⟨18212553096574788912073169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48566808257532770432195117 18212553096574788912073169)
        ·
          refine ⟨13659414822431091684054877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18212553096574788912073169 13659414822431091684054877)
          ·
            refine ⟨5122280558411659381520579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13659414822431091684054877 5122280558411659381520579)
            ·
              refine ⟨7683420837617489072280869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5122280558411659381520579 7683420837617489072280869)
              ·
                refine ⟨1440641407053279201052663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7683420837617489072280869 1440641407053279201052663)
                ·
                  refine ⟨2160962110579918801578995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1440641407053279201052663 2160962110579918801578995)
                  ·
                    refine ⟨3241443165869878202368493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2160962110579918801578995 3241443165869878202368493)
                    ·
                      refine ⟨1215541187201204325888185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3241443165869878202368493 1215541187201204325888185)
                      ·
                        rfl

theorem cell23_2367258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 4, 1, 1, 3].length) (baseStart_2367258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2367258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2367258 prefixEnd_2367258 := by exact prefixLift 2367258
  have htrace : WordTrace (prefixWord ++ tailWord_2367258) baseStart_2367258 baseEnd_2367258 := by
    simpa [prefixWord, tailWord_2367258, baseEnd_2367258] using wordTrace_append hprefix tailTrace_2367258
  have hstable : (prefixWord ++ tailWord_2367258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367258).length < 2 ^ (prefixWord ++ tailWord_2367258).sum := by decide
  have hdescent : baseEnd_2367258 < baseStart_2367258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367267 : List Nat := [1, 1, 1, 4, 2, 1, 2, 4, 1, 1, 5]
def baseStart_2367267 : Nat := 118140960795 + 2367267 * 2 ^ 59
def prefixEnd_2367267 : Nat := 4983230072969 + 3 ^ 40 * 2367267 * 2
def baseEnd_2367267 : Nat := 1215545808527094790675643

theorem tailTrace_2367267 : CollatzResearch.WordTrace tailWord_2367267 prefixEnd_2367267 1215545808527094790675643 := by
  unfold tailWord_2367267
  simp only [CollatzResearch.WordTrace]
  refine ⟨86341320714803430860980055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57560880476535620573986703 86341320714803430860980055)
  ·
    refine ⟨129511981072205146291470083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86341320714803430860980055 129511981072205146291470083)
    ·
      refine ⟨194267971608307719437205125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129511981072205146291470083 194267971608307719437205125)
      ·
        refine ⟨36425244676557697394475961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 194267971608307719437205125 36425244676557697394475961)
        ·
          refine ⟨27318933507418273045856971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36425244676557697394475961 27318933507418273045856971)
          ·
            refine ⟨40978400261127409568785457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27318933507418273045856971 40978400261127409568785457)
            ·
              refine ⟨30733800195845557176589093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40978400261127409568785457 30733800195845557176589093)
              ·
                refine ⟨5762587536721041970610455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30733800195845557176589093 5762587536721041970610455)
                ·
                  refine ⟨8643881305081562955915683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5762587536721041970610455 8643881305081562955915683)
                  ·
                    refine ⟨12965821957622344433873525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8643881305081562955915683 12965821957622344433873525)
                    ·
                      refine ⟨1215545808527094790675643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12965821957622344433873525 1215545808527094790675643)
                      ·
                        rfl

theorem cell23_2367267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 4, 1, 1, 5].length) (baseStart_2367267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2367267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2367267 prefixEnd_2367267 := by exact prefixLift 2367267
  have htrace : WordTrace (prefixWord ++ tailWord_2367267) baseStart_2367267 baseEnd_2367267 := by
    simpa [prefixWord, tailWord_2367267, baseEnd_2367267] using wordTrace_append hprefix tailTrace_2367267
  have hstable : (prefixWord ++ tailWord_2367267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367267).length < 2 ^ (prefixWord ++ tailWord_2367267).sum := by decide
  have hdescent : baseEnd_2367267 < baseStart_2367267 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367281 : List Nat := [1, 2, 2, 3, 2, 2, 1, 1, 5, 2, 2]
def baseStart_2367281 : Nat := 118140960795 + 2367281 * 2 ^ 59
def prefixEnd_2367281 : Nat := 4983230072969 + 3 ^ 40 * 2367281 * 2
def baseEnd_2367281 : Nat := 1215552997256257735900579

theorem tailTrace_2367281 : CollatzResearch.WordTrace tailWord_2367281 prefixEnd_2367281 1215552997256257735900579 := by
  unfold tailWord_2367281
  simp only [CollatzResearch.WordTrace]
  refine ⟨86341831336752711251989697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57561220891168474167993131 86341831336752711251989697)
  ·
    refine ⟨64756373502564533438992273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86341831336752711251989697 64756373502564533438992273)
    ·
      refine ⟨48567280126923400079244205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64756373502564533438992273 48567280126923400079244205)
      ·
        refine ⟨18212730047596275029716577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48567280126923400079244205 18212730047596275029716577)
        ·
          refine ⟨13659547535697206272287433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18212730047596275029716577 13659547535697206272287433)
          ·
            refine ⟨10244660651772904704215575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13659547535697206272287433 10244660651772904704215575)
            ·
              refine ⟨15366990977659357056323363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10244660651772904704215575 15366990977659357056323363)
              ·
                refine ⟨23050486466489035584485045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15366990977659357056323363 23050486466489035584485045)
                ·
                  refine ⟨2160983106233347086045473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23050486466489035584485045 2160983106233347086045473)
                  ·
                    refine ⟨1620737329675010314534105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2160983106233347086045473 1620737329675010314534105)
                    ·
                      refine ⟨1215552997256257735900579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1620737329675010314534105 1215552997256257735900579)
                      ·
                        rfl

theorem cell23_2367281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 5, 2, 2].length) (baseStart_2367281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2367281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2367281 prefixEnd_2367281 := by exact prefixLift 2367281
  have htrace : WordTrace (prefixWord ++ tailWord_2367281) baseStart_2367281 baseEnd_2367281 := by
    simpa [prefixWord, tailWord_2367281, baseEnd_2367281] using wordTrace_append hprefix tailTrace_2367281
  have hstable : (prefixWord ++ tailWord_2367281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367281).length < 2 ^ (prefixWord ++ tailWord_2367281).sum := by decide
  have hdescent : baseEnd_2367281 < baseStart_2367281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367285 : List Nat := [1, 3, 3, 1, 5, 1, 1, 1, 2, 3, 2]
def baseStart_2367285 : Nat := 118140960795 + 2367285 * 2 ^ 59
def prefixEnd_2367285 : Nat := 4983230072969 + 3 ^ 40 * 2367285 * 2
def baseEnd_2367285 : Nat := 1215555051178875720250561

theorem tailTrace_2367285 : CollatzResearch.WordTrace tailWord_2367285 prefixEnd_2367285 1215555051178875720250561 := by
  unfold tailWord_2367285
  simp only [CollatzResearch.WordTrace]
  refine ⟨86341977228738219935135309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57561318152492146623423539 86341977228738219935135309)
  ·
    refine ⟨32378241460776832475675741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86341977228738219935135309 32378241460776832475675741)
    ·
      refine ⟨12141840547791312178378403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32378241460776832475675741 12141840547791312178378403)
      ·
        refine ⟨18212760821686968267567605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12141840547791312178378403 18212760821686968267567605)
        ·
          refine ⟨1707446327033153275084463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18212760821686968267567605 1707446327033153275084463)
          ·
            refine ⟨2561169490549729912626695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1707446327033153275084463 2561169490549729912626695)
            ·
              refine ⟨3841754235824594868940043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2561169490549729912626695 3841754235824594868940043)
              ·
                refine ⟨5762631353736892303410065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3841754235824594868940043 5762631353736892303410065)
                ·
                  refine ⟨4321973515302669227557549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5762631353736892303410065 4321973515302669227557549)
                  ·
                    refine ⟨1620740068238500960334081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4321973515302669227557549 1620740068238500960334081)
                    ·
                      refine ⟨1215555051178875720250561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1620740068238500960334081 1215555051178875720250561)
                      ·
                        rfl

theorem cell23_2367285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 1, 2, 3, 2].length) (baseStart_2367285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2367285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2367285 prefixEnd_2367285 := by exact prefixLift 2367285
  have htrace : WordTrace (prefixWord ++ tailWord_2367285) baseStart_2367285 baseEnd_2367285 := by
    simpa [prefixWord, tailWord_2367285, baseEnd_2367285] using wordTrace_append hprefix tailTrace_2367285
  have hstable : (prefixWord ++ tailWord_2367285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367285).length < 2 ^ (prefixWord ++ tailWord_2367285).sum := by decide
  have hdescent : baseEnd_2367285 < baseStart_2367285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367308 : List Nat := [2, 2, 1, 3, 4, 2, 1, 2, 2, 4]
def baseStart_2367308 : Nat := 118140960795 + 2367308 * 2 ^ 59
def prefixEnd_2367308 : Nat := 4983230072969 + 3 ^ 40 * 2367308 * 2
def baseEnd_2367308 : Nat := 405188953744643043420985

theorem tailTrace_2367308 : CollatzResearch.WordTrace tailWord_2367308 prefixEnd_2367308 405188953744643043420985 := by
  unfold tailWord_2367308
  simp only [CollatzResearch.WordTrace]
  refine ⟨43171408053827447431611289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57561877405103263242148385 43171408053827447431611289)
  ·
    refine ⟨32378556040370585573708467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43171408053827447431611289 32378556040370585573708467)
    ·
      refine ⟨48567834060555878360562701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32378556040370585573708467 48567834060555878360562701)
      ·
        refine ⟨18212937772708454385211013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48567834060555878360562701 18212937772708454385211013)
        ·
          refine ⟨3414925832382835197227065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18212937772708454385211013 3414925832382835197227065)
          ·
            refine ⟨2561194374287126397920299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3414925832382835197227065 2561194374287126397920299)
            ·
              refine ⟨3841791561430689596880449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2561194374287126397920299 3841791561430689596880449)
              ·
                refine ⟨2881343671073017197660337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3841791561430689596880449 2881343671073017197660337)
                ·
                  refine ⟨2161007753304762898245253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2881343671073017197660337 2161007753304762898245253)
                  ·
                    refine ⟨405188953744643043420985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2161007753304762898245253 405188953744643043420985)
                    ·
                      rfl

theorem cell23_2367308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 2, 2, 4].length) (baseStart_2367308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2367308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2367308 prefixEnd_2367308 := by exact prefixLift 2367308
  have htrace : WordTrace (prefixWord ++ tailWord_2367308) baseStart_2367308 baseEnd_2367308 := by
    simpa [prefixWord, tailWord_2367308, baseEnd_2367308] using wordTrace_append hprefix tailTrace_2367308
  have hstable : (prefixWord ++ tailWord_2367308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367308).length < 2 ^ (prefixWord ++ tailWord_2367308).sum := by decide
  have hdescent : baseEnd_2367308 < baseStart_2367308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367337 : List Nat := [1, 2, 1, 1, 1, 3, 1, 4, 2, 3, 4]
def baseStart_2367337 : Nat := 118140960795 + 2367337 * 2 ^ 59
def prefixEnd_2367337 : Nat := 4983230072969 + 3 ^ 40 * 2367337 * 2
def baseEnd_2367337 : Nat := 1215581752172909516800321

theorem tailTrace_2367337 : CollatzResearch.WordTrace tailWord_2367337 prefixEnd_2367337 1215581752172909516800321 := by
  unfold tailWord_2367337
  simp only [CollatzResearch.WordTrace]
  refine ⟨86343873824549832816028265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57562582549699888544018843 86343873824549832816028265)
  ·
    refine ⟨64757905368412374612021199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86343873824549832816028265 64757905368412374612021199)
    ·
      refine ⟨97136858052618561918031799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64757905368412374612021199 97136858052618561918031799)
      ·
        refine ⟨145705287078927842877047699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97136858052618561918031799 145705287078927842877047699)
        ·
          refine ⟨218557930618391764315571549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145705287078927842877047699 218557930618391764315571549)
          ·
            refine ⟨81959223981896911618339331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 218557930618391764315571549 81959223981896911618339331)
            ·
              refine ⟨122938835972845367427508997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81959223981896911618339331 122938835972845367427508997)
              ·
                refine ⟨23051031744908506392657937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 122938835972845367427508997 23051031744908506392657937)
                ·
                  refine ⟨17288273808681379794493453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23051031744908506392657937 17288273808681379794493453)
                  ·
                    refine ⟨6483102678255517422935045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17288273808681379794493453 6483102678255517422935045)
                    ·
                      refine ⟨1215581752172909516800321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6483102678255517422935045 1215581752172909516800321)
                      ·
                        rfl

theorem cell23_2367337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2, 3, 4].length) (baseStart_2367337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2367337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2367337 prefixEnd_2367337 := by exact prefixLift 2367337
  have htrace : WordTrace (prefixWord ++ tailWord_2367337) baseStart_2367337 baseEnd_2367337 := by
    simpa [prefixWord, tailWord_2367337, baseEnd_2367337] using wordTrace_append hprefix tailTrace_2367337
  have hstable : (prefixWord ++ tailWord_2367337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367337).length < 2 ^ (prefixWord ++ tailWord_2367337).sum := by decide
  have hdescent : baseEnd_2367337 < baseStart_2367337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367338 : List Nat := [3, 1, 3, 4, 1, 2, 2, 7]
def baseStart_2367338 : Nat := 118140960795 + 2367338 * 2 ^ 59
def prefixEnd_2367338 : Nat := 4983230072969 + 3 ^ 40 * 2367338 * 2
def baseEnd_2367338 : Nat := 45021565394576444921771

theorem tailTrace_2367338 : CollatzResearch.WordTrace tailWord_2367338 prefixEnd_2367338 45021565394576444921771 := by
  unfold tailWord_2367338
  simp only [CollatzResearch.WordTrace]
  refine ⟨21585977574386552496703667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57562606865030806657876445 21585977574386552496703667)
  ·
    refine ⟨32378966361579828745055501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21585977574386552496703667 32378966361579828745055501)
    ·
      refine ⟨12142112385592435779395813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32378966361579828745055501 12142112385592435779395813)
      ·
        refine ⟨2276646072298581708636715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12142112385592435779395813 2276646072298581708636715)
        ·
          refine ⟨3414969108447872562955073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2276646072298581708636715 3414969108447872562955073)
          ·
            refine ⟨2561226831335904422216305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3414969108447872562955073 2561226831335904422216305)
            ·
              refine ⟨1920920123501928316662229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2561226831335904422216305 1920920123501928316662229)
              ·
                refine ⟨45021565394576444921771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1920920123501928316662229 45021565394576444921771)
                ·
                  rfl

theorem cell23_2367338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 2, 7].length) (baseStart_2367338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2367338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2367338 prefixEnd_2367338 := by exact prefixLift 2367338
  have htrace : WordTrace (prefixWord ++ tailWord_2367338) baseStart_2367338 baseEnd_2367338 := by
    simpa [prefixWord, tailWord_2367338, baseEnd_2367338] using wordTrace_append hprefix tailTrace_2367338
  have hstable : (prefixWord ++ tailWord_2367338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367338).length < 2 ^ (prefixWord ++ tailWord_2367338).sum := by decide
  have hdescent : baseEnd_2367338 < baseStart_2367338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367341 : List Nat := [1, 5, 1, 1, 1, 1, 2, 3, 3, 3, 2]
def baseStart_2367341 : Nat := 118140960795 + 2367341 * 2 ^ 59
def prefixEnd_2367341 : Nat := 4983230072969 + 3 ^ 40 * 2367341 * 2
def baseEnd_2367341 : Nat := 1215583806095527501150303

theorem tailTrace_2367341 : CollatzResearch.WordTrace tailWord_2367341 prefixEnd_2367341 1215583806095527501150303 := by
  unfold tailWord_2367341
  simp only [CollatzResearch.WordTrace]
  refine ⟨86344019716535341499173877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57562679811023560999449251 86344019716535341499173877)
  ·
    refine ⟨8094751848425188265547551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 86344019716535341499173877 8094751848425188265547551)
    ·
      refine ⟨12142127772637782398321327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8094751848425188265547551 12142127772637782398321327)
      ·
        refine ⟨18213191658956673597481991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12142127772637782398321327 18213191658956673597481991)
        ·
          refine ⟨27319787488435010396222987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18213191658956673597481991 27319787488435010396222987)
          ·
            refine ⟨40979681232652515594334481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27319787488435010396222987 40979681232652515594334481)
            ·
              refine ⟨30734760924489386695750861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40979681232652515594334481 30734760924489386695750861)
              ·
                refine ⟨11525535346683520010906573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30734760924489386695750861 11525535346683520010906573)
                ·
                  refine ⟨4322075755006320004089965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11525535346683520010906573 4322075755006320004089965)
                  ·
                    refine ⟨1620778408127370001533737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4322075755006320004089965 1620778408127370001533737)
                    ·
                      refine ⟨1215583806095527501150303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1620778408127370001533737 1215583806095527501150303)
                      ·
                        rfl

theorem cell23_2367341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 3, 3, 3, 2].length) (baseStart_2367341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2367341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2367341 prefixEnd_2367341 := by exact prefixLift 2367341
  have htrace : WordTrace (prefixWord ++ tailWord_2367341) baseStart_2367341 baseEnd_2367341 := by
    simpa [prefixWord, tailWord_2367341, baseEnd_2367341] using wordTrace_append hprefix tailTrace_2367341
  have hstable : (prefixWord ++ tailWord_2367341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367341).length < 2 ^ (prefixWord ++ tailWord_2367341).sum := by decide
  have hdescent : baseEnd_2367341 < baseStart_2367341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367397 : List Nat := [1, 3, 1, 2, 1, 1, 1, 2, 2, 1, 8]
def baseStart_2367397 : Nat := 118140960795 + 2367397 * 2 ^ 59
def prefixEnd_2367397 : Nat := 4983230072969 + 3 ^ 40 * 2367397 * 2
def baseEnd_2367397 : Nat := 1215612561012179282050045

theorem tailTrace_2367397 : CollatzResearch.WordTrace tailWord_2367397 prefixEnd_2367397 1215612561012179282050045 := by
  unfold tailWord_2367397
  simp only [CollatzResearch.WordTrace]
  refine ⟨86346062204332463063212445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57564041469554975375474963 86346062204332463063212445)
  ·
    refine ⟨32379773326624673648704667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86346062204332463063212445 32379773326624673648704667)
    ·
      refine ⟨48569659989937010473057001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32379773326624673648704667 48569659989937010473057001)
      ·
        refine ⟨36427244992452757854792751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48569659989937010473057001 36427244992452757854792751)
        ·
          refine ⟨54640867488679136782189127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36427244992452757854792751 54640867488679136782189127)
          ·
            refine ⟨81961301233018705173283691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54640867488679136782189127 81961301233018705173283691)
            ·
              refine ⟨122941951849528057759925537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81961301233018705173283691 122941951849528057759925537)
              ·
                refine ⟨92206463887146043319944153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 122941951849528057759925537 92206463887146043319944153)
                ·
                  refine ⟨69154847915359532489958115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 92206463887146043319944153 69154847915359532489958115)
                  ·
                    refine ⟨103732271873039298734937173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 69154847915359532489958115 103732271873039298734937173)
                    ·
                      refine ⟨1215612561012179282050045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 103732271873039298734937173 1215612561012179282050045)
                      ·
                        rfl

theorem cell23_2367397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 1, 8].length) (baseStart_2367397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2367397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2367397 prefixEnd_2367397 := by exact prefixLift 2367397
  have htrace : WordTrace (prefixWord ++ tailWord_2367397) baseStart_2367397 baseEnd_2367397 := by
    simpa [prefixWord, tailWord_2367397, baseEnd_2367397] using wordTrace_append hprefix tailTrace_2367397
  have hstable : (prefixWord ++ tailWord_2367397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367397).length < 2 ^ (prefixWord ++ tailWord_2367397).sum := by decide
  have hdescent : baseEnd_2367397 < baseStart_2367397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367424 : List Nat := [2, 1, 1, 2, 3, 2, 1, 4, 2, 5]
def baseStart_2367424 : Nat := 118140960795 + 2367424 * 2 ^ 59
def prefixEnd_2367424 : Nat := 4983230072969 + 3 ^ 40 * 2367424 * 2
def baseEnd_2367424 : Nat := 405208808329950225470807

theorem tailTrace_2367424 : CollatzResearch.WordTrace tailWord_2367424 prefixEnd_2367424 405208808329950225470807 := by
  unfold tailWord_2367424
  simp only [CollatzResearch.WordTrace]
  refine ⟨43173523487617323337222663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57564697983489764449630217 43173523487617323337222663)
  ·
    refine ⟨64760285231425985005833995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43173523487617323337222663 64760285231425985005833995)
    ·
      refine ⟨97140427847138977508750993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64760285231425985005833995 97140427847138977508750993)
      ·
        refine ⟨72855320885354233131563245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97140427847138977508750993 72855320885354233131563245)
        ·
          refine ⟨27320745332007837424336217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72855320885354233131563245 27320745332007837424336217)
          ·
            refine ⟨20490558999005878068252163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27320745332007837424336217 20490558999005878068252163)
            ·
              refine ⟨30735838498508817102378245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20490558999005878068252163 30735838498508817102378245)
              ·
                refine ⟨5762969718470403206695921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30735838498508817102378245 5762969718470403206695921)
                ·
                  refine ⟨4322227288852802405021941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5762969718470403206695921 4322227288852802405021941)
                  ·
                    refine ⟨405208808329950225470807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4322227288852802405021941 405208808329950225470807)
                    ·
                      rfl

theorem cell23_2367424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 4, 2, 5].length) (baseStart_2367424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2367424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2367424 prefixEnd_2367424 := by exact prefixLift 2367424
  have htrace : WordTrace (prefixWord ++ tailWord_2367424) baseStart_2367424 baseEnd_2367424 := by
    simpa [prefixWord, tailWord_2367424, baseEnd_2367424] using wordTrace_append hprefix tailTrace_2367424
  have hstable : (prefixWord ++ tailWord_2367424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367424).length < 2 ^ (prefixWord ++ tailWord_2367424).sum := by decide
  have hdescent : baseEnd_2367424 < baseStart_2367424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367427 : List Nat := [1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 8]
def baseStart_2367427 : Nat := 118140960795 + 2367427 * 2 ^ 59
def prefixEnd_2367427 : Nat := 4983230072969 + 3 ^ 40 * 2367427 * 2
def baseEnd_2367427 : Nat := 1215627965431814164674907

theorem tailTrace_2367427 : CollatzResearch.WordTrace tailWord_2367427 prefixEnd_2367427 1215627965431814164674907 := by
  unfold tailWord_2367427
  simp only [CollatzResearch.WordTrace]
  refine ⟨86347156394223778186804535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57564770929482518791203023 86347156394223778186804535)
  ·
    refine ⟨129520734591335667280206803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86347156394223778186804535 129520734591335667280206803)
    ·
      refine ⟨194281101887003500920310205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129520734591335667280206803 194281101887003500920310205)
      ·
        refine ⟨72855413207626312845116327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 194281101887003500920310205 72855413207626312845116327)
        ·
          refine ⟨109283119811439469267674491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72855413207626312845116327 109283119811439469267674491)
          ·
            refine ⟨163924679717159203901511737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109283119811439469267674491 163924679717159203901511737)
            ·
              refine ⟨122943509787869402926133803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 163924679717159203901511737 122943509787869402926133803)
              ·
                refine ⟨184415264681804104389200705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122943509787869402926133803 184415264681804104389200705)
                ·
                  refine ⟨138311448511353078291900529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 184415264681804104389200705 138311448511353078291900529)
                  ·
                    refine ⟨103733586383514808718925397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 138311448511353078291900529 103733586383514808718925397)
                    ·
                      refine ⟨1215627965431814164674907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 103733586383514808718925397 1215627965431814164674907)
                      ·
                        rfl

theorem cell23_2367427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 8].length) (baseStart_2367427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2367427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2367427 prefixEnd_2367427 := by exact prefixLift 2367427
  have htrace : WordTrace (prefixWord ++ tailWord_2367427) baseStart_2367427 baseEnd_2367427 := by
    simpa [prefixWord, tailWord_2367427, baseEnd_2367427] using wordTrace_append hprefix tailTrace_2367427
  have hstable : (prefixWord ++ tailWord_2367427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367427).length < 2 ^ (prefixWord ++ tailWord_2367427).sum := by decide
  have hdescent : baseEnd_2367427 < baseStart_2367427 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367434 : List Nat := [3, 1, 2, 1, 2, 1, 4, 1, 1, 2, 5]
def baseStart_2367434 : Nat := 118140960795 + 2367434 * 2 ^ 59
def prefixEnd_2367434 : Nat := 4983230072969 + 3 ^ 40 * 2367434 * 2
def baseEnd_2367434 : Nat := 1215631559796395637287375

theorem tailTrace_2367434 : CollatzResearch.WordTrace tailWord_2367434 prefixEnd_2367434 1215631559796395637287375 := by
  unfold tailWord_2367434
  simp only [CollatzResearch.WordTrace]
  refine ⟨21586852926299604595577339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57564941136798945588206237 21586852926299604595577339)
  ·
    refine ⟨32380279389449406893366009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21586852926299604595577339 32380279389449406893366009)
    ·
      refine ⟨24285209542087055170024507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32380279389449406893366009 24285209542087055170024507)
      ·
        refine ⟨36427814313130582755036761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24285209542087055170024507 36427814313130582755036761)
        ·
          refine ⟨27320860734847937066277571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36427814313130582755036761 27320860734847937066277571)
          ·
            refine ⟨40981291102271905599416357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27320860734847937066277571 40981291102271905599416357)
            ·
              refine ⟨7683992081675982299890567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40981291102271905599416357 7683992081675982299890567)
              ·
                refine ⟨11525988122513973449835851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7683992081675982299890567 11525988122513973449835851)
                ·
                  refine ⟨17288982183770960174753777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11525988122513973449835851 17288982183770960174753777)
                  ·
                    refine ⟨12966736637828220131065333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17288982183770960174753777 12966736637828220131065333)
                    ·
                      refine ⟨1215631559796395637287375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12966736637828220131065333 1215631559796395637287375)
                      ·
                        rfl

theorem cell23_2367434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 1, 1, 2, 5].length) (baseStart_2367434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2367434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2367434 prefixEnd_2367434 := by exact prefixLift 2367434
  have htrace : WordTrace (prefixWord ++ tailWord_2367434) baseStart_2367434 baseEnd_2367434 := by
    simpa [prefixWord, tailWord_2367434, baseEnd_2367434] using wordTrace_append hprefix tailTrace_2367434
  have hstable : (prefixWord ++ tailWord_2367434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367434).length < 2 ^ (prefixWord ++ tailWord_2367434).sum := by decide
  have hdescent : baseEnd_2367434 < baseStart_2367434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367458 : List Nat := [3, 3, 3, 1, 2, 1, 1, 1, 1, 7]
def baseStart_2367458 : Nat := 118140960795 + 2367458 * 2 ^ 59
def prefixEnd_2367458 : Nat := 4983230072969 + 3 ^ 40 * 2367458 * 2
def baseEnd_2367458 : Nat := 405214627777367847795755

theorem tailTrace_2367458 : CollatzResearch.WordTrace tailWord_2367458 prefixEnd_2367458 405214627777367847795755 := by
  unfold tailWord_2367458
  simp only [CollatzResearch.WordTrace]
  refine ⟨21587071764277867620295757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57565524704740980320788685 21587071764277867620295757)
  ·
    refine ⟨8095151911604200357610909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21587071764277867620295757 8095151911604200357610909)
    ·
      refine ⟨3035681966851575134104091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8095151911604200357610909 3035681966851575134104091)
      ·
        refine ⟨4553522950277362701156137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3035681966851575134104091 4553522950277362701156137)
        ·
          refine ⟨3415142212708022025867103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4553522950277362701156137 3415142212708022025867103)
          ·
            refine ⟨5122713319062033038800655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3415142212708022025867103 5122713319062033038800655)
            ·
              refine ⟨7684069978593049558200983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5122713319062033038800655 7684069978593049558200983)
              ·
                refine ⟨11526104967889574337301475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7684069978593049558200983 11526104967889574337301475)
                ·
                  refine ⟨17289157451834361505952213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11526104967889574337301475 17289157451834361505952213)
                  ·
                    refine ⟨405214627777367847795755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17289157451834361505952213 405214627777367847795755)
                    ·
                      rfl

theorem cell23_2367458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_2367458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2367458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2367458 prefixEnd_2367458 := by exact prefixLift 2367458
  have htrace : WordTrace (prefixWord ++ tailWord_2367458) baseStart_2367458 baseEnd_2367458 := by
    simpa [prefixWord, tailWord_2367458, baseEnd_2367458] using wordTrace_append hprefix tailTrace_2367458
  have hstable : (prefixWord ++ tailWord_2367458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367458).length < 2 ^ (prefixWord ++ tailWord_2367458).sum := by decide
  have hdescent : baseEnd_2367458 < baseStart_2367458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367484 : List Nat := [2, 2, 2, 1, 2, 2, 3, 1, 8]
def baseStart_2367484 : Nat := 118140960795 + 2367484 * 2 ^ 59
def prefixEnd_2367484 : Nat := 4983230072969 + 3 ^ 40 * 2367484 * 2
def baseEnd_2367484 : Nat := 135073025981013382406905

theorem tailTrace_2367484 : CollatzResearch.WordTrace tailWord_2367484 prefixEnd_2367484 135073025981013382406905 := by
  unfold tailWord_2367484
  simp only [CollatzResearch.WordTrace]
  refine ⟨43174617677508638460814753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57566156903344851281086337 43174617677508638460814753)
  ·
    refine ⟨32380963258131478845611065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43174617677508638460814753 32380963258131478845611065)
    ·
      refine ⟨24285722443598609134208299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32380963258131478845611065 24285722443598609134208299)
      ·
        refine ⟨36428583665397913701312449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24285722443598609134208299 36428583665397913701312449)
        ·
          refine ⟨27321437749048435275984337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36428583665397913701312449 27321437749048435275984337)
          ·
            refine ⟨20491078311786326456988253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27321437749048435275984337 20491078311786326456988253)
            ·
              refine ⟨7684154366919872421370595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20491078311786326456988253 7684154366919872421370595)
              ·
                refine ⟨11526231550379808632055893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7684154366919872421370595 11526231550379808632055893)
                ·
                  refine ⟨135073025981013382406905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11526231550379808632055893 135073025981013382406905)
                  ·
                    rfl

theorem cell23_2367484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 1, 8].length) (baseStart_2367484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2367484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2367484 prefixEnd_2367484 := by exact prefixLift 2367484
  have htrace : WordTrace (prefixWord ++ tailWord_2367484) baseStart_2367484 baseEnd_2367484 := by
    simpa [prefixWord, tailWord_2367484, baseEnd_2367484] using wordTrace_append hprefix tailTrace_2367484
  have hstable : (prefixWord ++ tailWord_2367484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367484).length < 2 ^ (prefixWord ++ tailWord_2367484).sum := by decide
  have hdescent : baseEnd_2367484 < baseStart_2367484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367538 : List Nat := [3, 2, 1, 1, 2, 3, 1, 1, 4, 3, 2]
def baseStart_2367538 : Nat := 118140960795 + 2367538 * 2 ^ 59
def prefixEnd_2367538 : Nat := 4983230072969 + 3 ^ 40 * 2367538 * 2
def baseEnd_2367538 : Nat := 1215684961784463230386897

theorem tailTrace_2367538 : CollatzResearch.WordTrace tailWord_2367538 prefixEnd_2367538 1215684961784463230386897 := by
  unfold tailWord_2367538
  simp only [CollatzResearch.WordTrace]
  refine ⟨21587801224205411036023817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57567469931214429429396845 21587801224205411036023817)
  ·
    refine ⟨16190850918154058277017863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21587801224205411036023817 16190850918154058277017863)
    ·
      refine ⟨24286276377231087415526795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16190850918154058277017863 24286276377231087415526795)
      ·
        refine ⟨36429414565846631123290193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24286276377231087415526795 36429414565846631123290193)
        ·
          refine ⟨27322060924384973342467645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36429414565846631123290193 27322060924384973342467645)
          ·
            refine ⟨10245772846644365003425367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27322060924384973342467645 10245772846644365003425367)
            ·
              refine ⟨15368659269966547505138051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10245772846644365003425367 15368659269966547505138051)
              ·
                refine ⟨23052988904949821257707077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15368659269966547505138051 23052988904949821257707077)
                ·
                  refine ⟨4322435419678091485820077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23052988904949821257707077 4322435419678091485820077)
                  ·
                    refine ⟨1620913282379284307182529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4322435419678091485820077 1620913282379284307182529)
                    ·
                      refine ⟨1215684961784463230386897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1620913282379284307182529 1215684961784463230386897)
                      ·
                        rfl

theorem cell23_2367538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 4, 3, 2].length) (baseStart_2367538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2367538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2367538 prefixEnd_2367538 := by exact prefixLift 2367538
  have htrace : WordTrace (prefixWord ++ tailWord_2367538) baseStart_2367538 baseEnd_2367538 := by
    simpa [prefixWord, tailWord_2367538, baseEnd_2367538] using wordTrace_append hprefix tailTrace_2367538
  have hstable : (prefixWord ++ tailWord_2367538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367538).length < 2 ^ (prefixWord ++ tailWord_2367538).sum := by decide
  have hdescent : baseEnd_2367538 < baseStart_2367538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367588 : List Nat := [2, 3, 1, 1, 2, 1, 2, 5, 1, 2, 3]
def baseStart_2367588 : Nat := 118140960795 + 2367588 * 2 ^ 59
def prefixEnd_2367588 : Nat := 4983230072969 + 3 ^ 40 * 2367588 * 2
def baseEnd_2367588 : Nat := 1215710635817188034761667

theorem tailTrace_2367588 : CollatzResearch.WordTrace tailWord_2367588 prefixEnd_2367588 1215710635817188034761667 := by
  unfold tailWord_2367588
  simp only [CollatzResearch.WordTrace]
  refine ⟨43176514273320251341707709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57568685697760335122276945 43176514273320251341707709)
  ·
    refine ⟨16191192852495094253140391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43176514273320251341707709 16191192852495094253140391)
    ·
      refine ⟨24286789278742641379710587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16191192852495094253140391 24286789278742641379710587)
      ·
        refine ⟨36430183918113962069565881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24286789278742641379710587 36430183918113962069565881)
        ·
          refine ⟨27322637938585471552174411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36430183918113962069565881 27322637938585471552174411)
          ·
            refine ⟨40983956907878207328261617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27322637938585471552174411 40983956907878207328261617)
            ·
              refine ⟨30737967680908655496196213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40983956907878207328261617 30737967680908655496196213)
              ·
                refine ⟨2881684470085186452768395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30737967680908655496196213 2881684470085186452768395)
                ·
                  refine ⟨4322526705127779679152593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2881684470085186452768395 4322526705127779679152593)
                  ·
                    refine ⟨3241895028845834759364445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4322526705127779679152593 3241895028845834759364445)
                    ·
                      refine ⟨1215710635817188034761667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3241895028845834759364445 1215710635817188034761667)
                      ·
                        rfl

theorem cell23_2367588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 5, 1, 2, 3].length) (baseStart_2367588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2367588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2367588 prefixEnd_2367588 := by exact prefixLift 2367588
  have htrace : WordTrace (prefixWord ++ tailWord_2367588) baseStart_2367588 baseEnd_2367588 := by
    simpa [prefixWord, tailWord_2367588, baseEnd_2367588] using wordTrace_append hprefix tailTrace_2367588
  have hstable : (prefixWord ++ tailWord_2367588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367588).length < 2 ^ (prefixWord ++ tailWord_2367588).sum := by decide
  have hdescent : baseEnd_2367588 < baseStart_2367588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367601 : List Nat := [1, 2, 2, 2, 1, 1, 3, 2, 3, 3, 3]
def baseStart_2367601 : Nat := 118140960795 + 2367601 * 2 ^ 59
def prefixEnd_2367601 : Nat := 4983230072969 + 3 ^ 40 * 2367601 * 2
def baseEnd_2367601 : Nat := 1215717311065696483899107

theorem tailTrace_2367601 : CollatzResearch.WordTrace tailWord_2367601 prefixEnd_2367601 1215717311065696483899107 := by
  unfold tailWord_2367601
  simp only [CollatzResearch.WordTrace]
  refine ⟨86353502695593405903638657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57569001797062270602425771 86353502695593405903638657)
  ·
    refine ⟨64765127021695054427728993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86353502695593405903638657 64765127021695054427728993)
    ·
      refine ⟨48573845266271290820796745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64765127021695054427728993 48573845266271290820796745)
      ·
        refine ⟨36430383949703468115597559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48573845266271290820796745 36430383949703468115597559)
        ·
          refine ⟨54645575924555202173396339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36430383949703468115597559 54645575924555202173396339)
          ·
            refine ⟨81968363886832803260094509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54645575924555202173396339 81968363886832803260094509)
            ·
              refine ⟨30738136457562301222535441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81968363886832803260094509 30738136457562301222535441)
              ·
                refine ⟨23053602343171725916901581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30738136457562301222535441 23053602343171725916901581)
                ·
                  refine ⟨8645100878689397218838093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23053602343171725916901581 8645100878689397218838093)
                  ·
                    refine ⟨3241912829508523957064285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8645100878689397218838093 3241912829508523957064285)
                    ·
                      refine ⟨1215717311065696483899107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3241912829508523957064285 1215717311065696483899107)
                      ·
                        rfl

theorem cell23_2367601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 3, 3, 3].length) (baseStart_2367601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2367601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2367601 prefixEnd_2367601 := by exact prefixLift 2367601
  have htrace : WordTrace (prefixWord ++ tailWord_2367601) baseStart_2367601 baseEnd_2367601 := by
    simpa [prefixWord, tailWord_2367601, baseEnd_2367601] using wordTrace_append hprefix tailTrace_2367601
  have hstable : (prefixWord ++ tailWord_2367601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367601).length < 2 ^ (prefixWord ++ tailWord_2367601).sum := by decide
  have hdescent : baseEnd_2367601 < baseStart_2367601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367636 : List Nat := [2, 4, 2, 3, 2, 1, 2, 1, 1, 1, 4]
def baseStart_2367636 : Nat := 118140960795 + 2367636 * 2 ^ 59
def prefixEnd_2367636 : Nat := 4983230072969 + 3 ^ 40 * 2367636 * 2
def baseEnd_2367636 : Nat := 1215735282888603846961447

theorem tailTrace_2367636 : CollatzResearch.WordTrace tailWord_2367636 prefixEnd_2367636 1215735282888603846961447 := by
  unfold tailWord_2367636
  simp only [CollatzResearch.WordTrace]
  refine ⟨43177389625233303440581381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57569852833644404587441841 43177389625233303440581381)
  ·
    refine ⟨8095760554731244395109009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43177389625233303440581381 8095760554731244395109009)
    ·
      refine ⟨6071820416048433296331757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8095760554731244395109009 6071820416048433296331757)
      ·
        refine ⟨2276932656018162486124409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6071820416048433296331757 2276932656018162486124409)
        ·
          refine ⟨1707699492013621864593307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2276932656018162486124409 1707699492013621864593307)
          ·
            refine ⟨2561549238020432796889961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1707699492013621864593307 2561549238020432796889961)
            ·
              refine ⟨1921161928515324597667471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2561549238020432796889961 1921161928515324597667471)
              ·
                refine ⟨2881742892772986896501207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1921161928515324597667471 2881742892772986896501207)
                ·
                  refine ⟨4322614339159480344751811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2881742892772986896501207 4322614339159480344751811)
                  ·
                    refine ⟨6483921508739220517127717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4322614339159480344751811 6483921508739220517127717)
                    ·
                      refine ⟨1215735282888603846961447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6483921508739220517127717 1215735282888603846961447)
                      ·
                        rfl

theorem cell23_2367636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_2367636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2367636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2367636 prefixEnd_2367636 := by exact prefixLift 2367636
  have htrace : WordTrace (prefixWord ++ tailWord_2367636) baseStart_2367636 baseEnd_2367636 := by
    simpa [prefixWord, tailWord_2367636, baseEnd_2367636] using wordTrace_append hprefix tailTrace_2367636
  have hstable : (prefixWord ++ tailWord_2367636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367636).length < 2 ^ (prefixWord ++ tailWord_2367636).sum := by decide
  have hdescent : baseEnd_2367636 < baseStart_2367636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367639 : List Nat := [1, 1, 3, 3, 5, 1, 2, 1, 1, 2, 3]
def baseStart_2367639 : Nat := 118140960795 + 2367639 * 2 ^ 59
def prefixEnd_2367639 : Nat := 4983230072969 + 3 ^ 40 * 2367639 * 2
def baseEnd_2367639 : Nat := 1215736823330567335223933

theorem tailTrace_2367639 : CollatzResearch.WordTrace tailWord_2367639 prefixEnd_2367639 1215736823330567335223933 := by
  unfold tailWord_2367639
  simp only [CollatzResearch.WordTrace]
  refine ⟨86354888669455738393521971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57569925779637158929014647 86354888669455738393521971)
  ·
    refine ⟨129532333004183607590282957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86354888669455738393521971 129532333004183607590282957)
    ·
      refine ⟨48574624876568852846356109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129532333004183607590282957 48574624876568852846356109)
      ·
        refine ⟨18215484328713319817383541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48574624876568852846356109 18215484328713319817383541)
        ·
          refine ⟨1707701655816873732879707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18215484328713319817383541 1707701655816873732879707)
          ·
            refine ⟨2561552483725310599319561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1707701655816873732879707 2561552483725310599319561)
            ·
              refine ⟨1921164362793982949489671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2561552483725310599319561 1921164362793982949489671)
              ·
                refine ⟨2881746544190974424234507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1921164362793982949489671 2881746544190974424234507)
                ·
                  refine ⟨4322619816286461636351761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2881746544190974424234507 4322619816286461636351761)
                  ·
                    refine ⟨3241964862214846227263821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4322619816286461636351761 3241964862214846227263821)
                    ·
                      refine ⟨1215736823330567335223933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3241964862214846227263821 1215736823330567335223933)
                      ·
                        rfl

theorem cell23_2367639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 2, 1, 1, 2, 3].length) (baseStart_2367639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2367639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2367639 prefixEnd_2367639 := by exact prefixLift 2367639
  have htrace : WordTrace (prefixWord ++ tailWord_2367639) baseStart_2367639 baseEnd_2367639 := by
    simpa [prefixWord, tailWord_2367639, baseEnd_2367639] using wordTrace_append hprefix tailTrace_2367639
  have hstable : (prefixWord ++ tailWord_2367639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367639).length < 2 ^ (prefixWord ++ tailWord_2367639).sum := by decide
  have hdescent : baseEnd_2367639 < baseStart_2367639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367669 : List Nat := [1, 3, 3, 4, 2, 1, 1, 1, 1, 3, 3]
def baseStart_2367669 : Nat := 118140960795 + 2367669 * 2 ^ 59
def prefixEnd_2367669 : Nat := 4983230072969 + 3 ^ 40 * 2367669 * 2
def baseEnd_2367669 : Nat := 1215752227750202217848795

theorem tailTrace_2367669 : CollatzResearch.WordTrace tailWord_2367669 prefixEnd_2367669 1215752227750202217848795 := by
  unfold tailWord_2367669
  simp only [CollatzResearch.WordTrace]
  refine ⟨86355982859347053517114061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57570655239564702344742707 86355982859347053517114061)
  ·
    refine ⟨32383493572255145068917773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86355982859347053517114061 32383493572255145068917773)
    ·
      refine ⟨12143810089595679400844165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32383493572255145068917773 12143810089595679400844165)
      ·
        refine ⟨2276964391799189887658281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12143810089595679400844165 2276964391799189887658281)
        ·
          refine ⟨1707723293849392415743711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2276964391799189887658281 1707723293849392415743711)
          ·
            refine ⟨2561584940774088623615567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1707723293849392415743711 2561584940774088623615567)
            ·
              refine ⟨3842377411161132935423351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2561584940774088623615567 3842377411161132935423351)
              ·
                refine ⟨5763566116741699403135027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3842377411161132935423351 5763566116741699403135027)
                ·
                  refine ⟨8645349175112549104702541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5763566116741699403135027 8645349175112549104702541)
                  ·
                    refine ⟨3242005940667205914263453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8645349175112549104702541 3242005940667205914263453)
                    ·
                      refine ⟨1215752227750202217848795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3242005940667205914263453 1215752227750202217848795)
                      ·
                        rfl

theorem cell23_2367669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_2367669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2367669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2367669 prefixEnd_2367669 := by exact prefixLift 2367669
  have htrace : WordTrace (prefixWord ++ tailWord_2367669) baseStart_2367669 baseEnd_2367669 := by
    simpa [prefixWord, tailWord_2367669, baseEnd_2367669] using wordTrace_append hprefix tailTrace_2367669
  have hstable : (prefixWord ++ tailWord_2367669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367669).length < 2 ^ (prefixWord ++ tailWord_2367669).sum := by decide
  have hdescent : baseEnd_2367669 < baseStart_2367669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367721 : List Nat := [1, 2, 1, 1, 1, 2, 2, 5, 1, 2, 5]
def baseStart_2367721 : Nat := 118140960795 + 2367721 * 2 ^ 59
def prefixEnd_2367721 : Nat := 4983230072969 + 3 ^ 40 * 2367721 * 2
def baseEnd_2367721 : Nat := 1215778928744236014398555

theorem tailTrace_2367721 : CollatzResearch.WordTrace tailWord_2367721 prefixEnd_2367721 1215778928744236014398555 := by
  unfold tailWord_2367721
  simp only [CollatzResearch.WordTrace]
  refine ⟨86357879455158666398007017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57571919636772444265338011 86357879455158666398007017)
  ·
    refine ⟨64768409591368999798505263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86357879455158666398007017 64768409591368999798505263)
    ·
      refine ⟨97152614387053499697757895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64768409591368999798505263 97152614387053499697757895)
      ·
        refine ⟨145728921580580249546636843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97152614387053499697757895 145728921580580249546636843)
        ·
          refine ⟨218593382370870374319955265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145728921580580249546636843 218593382370870374319955265)
          ·
            refine ⟨163945036778152780739966449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 218593382370870374319955265 163945036778152780739966449)
            ·
              refine ⟨122958777583614585554974837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 163945036778152780739966449 122958777583614585554974837)
              ·
                refine ⟨11527385398463867395778891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 122958777583614585554974837 11527385398463867395778891)
                ·
                  refine ⟨17291078097695801093668337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11527385398463867395778891 17291078097695801093668337)
                  ·
                    refine ⟨12968308573271850820251253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17291078097695801093668337 12968308573271850820251253)
                    ·
                      refine ⟨1215778928744236014398555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12968308573271850820251253 1215778928744236014398555)
                      ·
                        rfl

theorem cell23_2367721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5, 1, 2, 5].length) (baseStart_2367721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2367721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2367721 prefixEnd_2367721 := by exact prefixLift 2367721
  have htrace : WordTrace (prefixWord ++ tailWord_2367721) baseStart_2367721 baseEnd_2367721 := by
    simpa [prefixWord, tailWord_2367721, baseEnd_2367721] using wordTrace_append hprefix tailTrace_2367721
  have hstable : (prefixWord ++ tailWord_2367721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367721).length < 2 ^ (prefixWord ++ tailWord_2367721).sum := by decide
  have hdescent : baseEnd_2367721 < baseStart_2367721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367741 : List Nat := [1, 4, 1, 1, 1, 1, 1, 3, 2, 8]
def baseStart_2367741 : Nat := 118140960795 + 2367741 * 2 ^ 59
def prefixEnd_2367741 : Nat := 4983230072969 + 3 ^ 40 * 2367741 * 2
def baseEnd_2367741 : Nat := 405263066119108645382821

theorem tailTrace_2367741 : CollatzResearch.WordTrace tailWord_2367741 prefixEnd_2367741 405263066119108645382821 := by
  unfold tailWord_2367741
  simp only [CollatzResearch.WordTrace]
  refine ⟨86358608915086209813735077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57572405943390806542490051 86358608915086209813735077)
  ·
    refine ⟨16192239171578664340075327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86358608915086209813735077 16192239171578664340075327)
    ·
      refine ⟨24288358757367996510112991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16192239171578664340075327 24288358757367996510112991)
      ·
        refine ⟨36432538136051994765169487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24288358757367996510112991 36432538136051994765169487)
        ·
          refine ⟨54648807204077992147754231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36432538136051994765169487 54648807204077992147754231)
          ·
            refine ⟨81973210806116988221631347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54648807204077992147754231 81973210806116988221631347)
            ·
              refine ⟨122959816209175482332447021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81973210806116988221631347 122959816209175482332447021)
              ·
                refine ⟨46109931078440805874667633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 122959816209175482332447021 46109931078440805874667633)
                ·
                  refine ⟨34582448308830604406000725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46109931078440805874667633 34582448308830604406000725)
                  ·
                    refine ⟨405263066119108645382821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 34582448308830604406000725 405263066119108645382821)
                    ·
                      rfl

theorem cell23_2367741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 8].length) (baseStart_2367741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2367741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2367741 prefixEnd_2367741 := by exact prefixLift 2367741
  have htrace : WordTrace (prefixWord ++ tailWord_2367741) baseStart_2367741 baseEnd_2367741 := by
    simpa [prefixWord, tailWord_2367741, baseEnd_2367741] using wordTrace_append hprefix tailTrace_2367741
  have hstable : (prefixWord ++ tailWord_2367741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367741).length < 2 ^ (prefixWord ++ tailWord_2367741).sum := by decide
  have hdescent : baseEnd_2367741 < baseStart_2367741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367771 : List Nat := [1, 1, 1, 1, 1, 1, 6, 3, 8]
def baseStart_2367771 : Nat := 118140960795 + 2367771 * 2 ^ 59
def prefixEnd_2367771 : Nat := 4983230072969 + 3 ^ 40 * 2367771 * 2
def baseEnd_2367771 : Nat := 135089400308551202085925

theorem tailTrace_2367771 : CollatzResearch.WordTrace tailWord_2367771 prefixEnd_2367771 135089400308551202085925 := by
  unfold tailWord_2367771
  simp only [CollatzResearch.WordTrace]
  refine ⟨86359703104977524937327167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57573135403318349958218111 86359703104977524937327167)
  ·
    refine ⟨129539554657466287405990751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86359703104977524937327167 129539554657466287405990751)
    ·
      refine ⟨194309331986199431108986127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129539554657466287405990751 194309331986199431108986127)
      ·
        refine ⟨291463997979299146663479191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194309331986199431108986127 291463997979299146663479191)
        ·
          refine ⟨437195996968948719995218787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 291463997979299146663479191 437195996968948719995218787)
          ·
            refine ⟨655793995453423079992828181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 437195996968948719995218787 655793995453423079992828181)
            ·
              refine ⟨30740343536879206874663821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 655793995453423079992828181 30740343536879206874663821)
              ·
                refine ⟨11527628826329702577998933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30740343536879206874663821 11527628826329702577998933)
                ·
                  refine ⟨135089400308551202085925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11527628826329702577998933 135089400308551202085925)
                  ·
                    rfl

theorem cell23_2367771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3, 8].length) (baseStart_2367771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2367771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2367771 prefixEnd_2367771 := by exact prefixLift 2367771
  have htrace : WordTrace (prefixWord ++ tailWord_2367771) baseStart_2367771 baseEnd_2367771 := by
    simpa [prefixWord, tailWord_2367771, baseEnd_2367771] using wordTrace_append hprefix tailTrace_2367771
  have hstable : (prefixWord ++ tailWord_2367771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367771).length < 2 ^ (prefixWord ++ tailWord_2367771).sum := by decide
  have hdescent : baseEnd_2367771 < baseStart_2367771 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367788 : List Nat := [2, 2, 1, 1, 1, 3, 4, 3, 6]
def baseStart_2367788 : Nat := 118140960795 + 2367788 * 2 ^ 59
def prefixEnd_2367788 : Nat := 4983230072969 + 3 ^ 40 * 2367788 * 2
def baseEnd_2367788 : Nat := 135090370216454139140083

theorem tailTrace_2367788 : CollatzResearch.WordTrace tailWord_2367788 prefixEnd_2367788 135090370216454139140083 := by
  unfold tailWord_2367788
  simp only [CollatzResearch.WordTrace]
  refine ⟨43180161572957968420348009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57573548763943957893797345 43180161572957968420348009)
  ·
    refine ⟨32385121179718476315261007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43180161572957968420348009 32385121179718476315261007)
    ·
      refine ⟨48577681769577714472891511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32385121179718476315261007 48577681769577714472891511)
      ·
        refine ⟨72866522654366571709337267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48577681769577714472891511 72866522654366571709337267)
        ·
          refine ⟨109299783981549857564005901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72866522654366571709337267 109299783981549857564005901)
          ·
            refine ⟨40987418993081196586502213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109299783981549857564005901 40987418993081196586502213)
            ·
              refine ⟨7685141061202724359969165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40987418993081196586502213 7685141061202724359969165)
              ·
                refine ⟨2881927897951021634988437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7685141061202724359969165 2881927897951021634988437)
                ·
                  refine ⟨135090370216454139140083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2881927897951021634988437 135090370216454139140083)
                  ·
                    rfl

theorem cell23_2367788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 6].length) (baseStart_2367788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2367788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2367788 prefixEnd_2367788 := by exact prefixLift 2367788
  have htrace : WordTrace (prefixWord ++ tailWord_2367788) baseStart_2367788 baseEnd_2367788 := by
    simpa [prefixWord, tailWord_2367788, baseEnd_2367788] using wordTrace_append hprefix tailTrace_2367788
  have hstable : (prefixWord ++ tailWord_2367788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367788).length < 2 ^ (prefixWord ++ tailWord_2367788).sum := by decide
  have hdescent : baseEnd_2367788 < baseStart_2367788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367802 : List Nat := [3, 1, 1, 1, 4, 4, 1, 1, 2, 2, 3]
def baseStart_2367802 : Nat := 118140960795 + 2367802 * 2 ^ 59
def prefixEnd_2367802 : Nat := 4983230072969 + 3 ^ 40 * 2367802 * 2
def baseEnd_2367802 : Nat := 1215820520677250197485683

theorem tailTrace_2367802 : CollatzResearch.WordTrace tailWord_2367802 prefixEnd_2367802 1215820520677250197485683 := by
  unfold tailWord_2367802
  simp only [CollatzResearch.WordTrace]
  refine ⟨21590208441966304307926415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57573889178576811487803773 21590208441966304307926415)
  ·
    refine ⟨32385312662949456461889623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21590208441966304307926415 32385312662949456461889623)
    ·
      refine ⟨48577968994424184692834435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32385312662949456461889623 48577968994424184692834435)
      ·
        refine ⟨72866953491636277039251653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48577968994424184692834435 72866953491636277039251653)
        ·
          refine ⟨13662553779681801944859685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72866953491636277039251653 13662553779681801944859685)
          ·
            refine ⟨2561728833690337864661191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13662553779681801944859685 2561728833690337864661191)
            ·
              refine ⟨3842593250535506796991787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2561728833690337864661191 3842593250535506796991787)
              ·
                refine ⟨5763889875803260195487681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3842593250535506796991787 5763889875803260195487681)
                ·
                  refine ⟨4322917406852445146615761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5763889875803260195487681 4322917406852445146615761)
                  ·
                    refine ⟨3242188055139333859961821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4322917406852445146615761 3242188055139333859961821)
                    ·
                      refine ⟨1215820520677250197485683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3242188055139333859961821 1215820520677250197485683)
                      ·
                        rfl

theorem cell23_2367802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 1, 2, 2, 3].length) (baseStart_2367802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2367802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2367802 prefixEnd_2367802 := by exact prefixLift 2367802
  have htrace : WordTrace (prefixWord ++ tailWord_2367802) baseStart_2367802 baseEnd_2367802 := by
    simpa [prefixWord, tailWord_2367802, baseEnd_2367802] using wordTrace_append hprefix tailTrace_2367802
  have hstable : (prefixWord ++ tailWord_2367802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367802).length < 2 ^ (prefixWord ++ tailWord_2367802).sum := by decide
  have hdescent : baseEnd_2367802 < baseStart_2367802 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367815 : List Nat := [1, 1, 4, 1, 2, 2, 1, 2, 5, 1, 3]
def baseStart_2367815 : Nat := 118140960795 + 2367815 * 2 ^ 59
def prefixEnd_2367815 : Nat := 4983230072969 + 3 ^ 40 * 2367815 * 2
def baseEnd_2367815 : Nat := 1215827195925758646623123

theorem tailTrace_2367815 : CollatzResearch.WordTrace tailWord_2367815 prefixEnd_2367815 1215827195925758646623123 := by
  unfold tailWord_2367815
  simp only [CollatzResearch.WordTrace]
  refine ⟨86361307916818120451928899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57574205277878746967952599 86361307916818120451928899)
  ·
    refine ⟨129541961875227180677893349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86361307916818120451928899 129541961875227180677893349)
    ·
      refine ⟨24289117851605096377105003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 129541961875227180677893349 24289117851605096377105003)
      ·
        refine ⟨36433676777407644565657505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24289117851605096377105003 36433676777407644565657505)
        ·
          refine ⟨27325257583055733424243129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36433676777407644565657505 27325257583055733424243129)
          ·
            refine ⟨20493943187291800068182347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27325257583055733424243129 20493943187291800068182347)
            ·
              refine ⟨30740914780937700102273521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20493943187291800068182347 30740914780937700102273521)
              ·
                refine ⟨23055686085703275076705141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30740914780937700102273521 23055686085703275076705141)
                ·
                  refine ⟨2161470570534682038441107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23055686085703275076705141 2161470570534682038441107)
                  ·
                    refine ⟨3242205855802023057661661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2161470570534682038441107 3242205855802023057661661)
                    ·
                      refine ⟨1215827195925758646623123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3242205855802023057661661 1215827195925758646623123)
                      ·
                        rfl

theorem cell23_2367815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 5, 1, 3].length) (baseStart_2367815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2367815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2367815 prefixEnd_2367815 := by exact prefixLift 2367815
  have htrace : WordTrace (prefixWord ++ tailWord_2367815) baseStart_2367815 baseEnd_2367815 := by
    simpa [prefixWord, tailWord_2367815, baseEnd_2367815] using wordTrace_append hprefix tailTrace_2367815
  have hstable : (prefixWord ++ tailWord_2367815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367815).length < 2 ^ (prefixWord ++ tailWord_2367815).sum := by decide
  have hdescent : baseEnd_2367815 < baseStart_2367815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367842 : List Nat := [3, 3, 2, 1, 1, 2, 1, 2, 1, 5, 2]
def baseStart_2367842 : Nat := 118140960795 + 2367842 * 2 ^ 59
def prefixEnd_2367842 : Nat := 4983230072969 + 3 ^ 40 * 2367842 * 2
def baseEnd_2367842 : Nat := 1215841059903430040985499

theorem tailTrace_2367842 : CollatzResearch.WordTrace tailWord_2367842 prefixEnd_2367842 1215841059903430040985499 := by
  unfold tailWord_2367842
  simp only [CollatzResearch.WordTrace]
  refine ⟨21590573171930076015790445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57574861791813536042107853 21590573171930076015790445)
  ·
    refine ⟨8096464939473778505921417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21590573171930076015790445 8096464939473778505921417)
    ·
      refine ⟨6072348704605333879441063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8096464939473778505921417 6072348704605333879441063)
      ·
        refine ⟨9108523056908000819161595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6072348704605333879441063 9108523056908000819161595)
        ·
          refine ⟨13662784585362001228742393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9108523056908000819161595 13662784585362001228742393)
          ·
            refine ⟨10247088439021500921556795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13662784585362001228742393 10247088439021500921556795)
            ·
              refine ⟨15370632658532251382335193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10247088439021500921556795 15370632658532251382335193)
              ·
                refine ⟨11527974493899188536751395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15370632658532251382335193 11527974493899188536751395)
                ·
                  refine ⟨17291961740848782805127093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11527974493899188536751395 17291961740848782805127093)
                  ·
                    refine ⟨1621121413204573387980665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17291961740848782805127093 1621121413204573387980665)
                    ·
                      refine ⟨1215841059903430040985499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1621121413204573387980665 1215841059903430040985499)
                      ·
                        rfl

theorem cell23_2367842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 2, 1, 5, 2].length) (baseStart_2367842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2367842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2367842 prefixEnd_2367842 := by exact prefixLift 2367842
  have htrace : WordTrace (prefixWord ++ tailWord_2367842) baseStart_2367842 baseEnd_2367842 := by
    simpa [prefixWord, tailWord_2367842, baseEnd_2367842] using wordTrace_append hprefix tailTrace_2367842
  have hstable : (prefixWord ++ tailWord_2367842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367842).length < 2 ^ (prefixWord ++ tailWord_2367842).sum := by decide
  have hdescent : baseEnd_2367842 < baseStart_2367842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367852 : List Nat := [2, 2, 1, 1, 6, 1, 2, 2, 1, 5]
def baseStart_2367852 : Nat := 118140960795 + 2367852 * 2 ^ 59
def prefixEnd_2367852 : Nat := 4983230072969 + 3 ^ 40 * 2367852 * 2
def baseEnd_2367852 : Nat := 405282064903325000620151

theorem tailTrace_2367852 : CollatzResearch.WordTrace tailWord_2367852 prefixEnd_2367852 405282064903325000620151 := by
  unfold tailWord_2367852
  simp only [CollatzResearch.WordTrace]
  refine ⟨43181328708842037885512905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57575104945122717180683873 43181328708842037885512905)
  ·
    refine ⟨32385996531631528414134679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43181328708842037885512905 32385996531631528414134679)
    ·
      refine ⟨48578994797447292621202019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32385996531631528414134679 48578994797447292621202019)
      ·
        refine ⟨72868492196170938931803029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48578994797447292621202019 72868492196170938931803029)
        ·
          refine ⟨3415710571695512762428267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 72868492196170938931803029 3415710571695512762428267)
          ·
            refine ⟨5123565857543269143642401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3415710571695512762428267 5123565857543269143642401)
            ·
              refine ⟨3842674393157451857731801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5123565857543269143642401 3842674393157451857731801)
              ·
                refine ⟨2882005794868088893298851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3842674393157451857731801 2882005794868088893298851)
                ·
                  refine ⟨4323008692302133339948277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2882005794868088893298851 4323008692302133339948277)
                  ·
                    refine ⟨405282064903325000620151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4323008692302133339948277 405282064903325000620151)
                    ·
                      rfl

theorem cell23_2367852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 5].length) (baseStart_2367852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2367852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2367852 prefixEnd_2367852 := by exact prefixLift 2367852
  have htrace : WordTrace (prefixWord ++ tailWord_2367852) baseStart_2367852 baseEnd_2367852 := by
    simpa [prefixWord, tailWord_2367852, baseEnd_2367852] using wordTrace_append hprefix tailTrace_2367852
  have hstable : (prefixWord ++ tailWord_2367852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367852).length < 2 ^ (prefixWord ++ tailWord_2367852).sum := by decide
  have hdescent : baseEnd_2367852 < baseStart_2367852 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367902 : List Nat := [4, 3, 1, 2, 1, 1, 2, 1, 1, 1, 6]
def baseStart_2367902 : Nat := 118140960795 + 2367902 * 2 ^ 59
def prefixEnd_2367902 : Nat := 4983230072969 + 3 ^ 40 * 2367902 * 2
def baseEnd_2367902 : Nat := 1215871868742699806235223

theorem tailTrace_2367902 : CollatzResearch.WordTrace tailWord_2367902 prefixEnd_2367902 1215871868742699806235223 := by
  unfold tailWord_2367902
  simp only [CollatzResearch.WordTrace]
  refine ⟨10795560133437866788793245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57576320711668622873563973 10795560133437866788793245)
  ·
    refine ⟨4048335050039200045797467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10795560133437866788793245 4048335050039200045797467)
    ·
      refine ⟨6072502575058800068696201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4048335050039200045797467 6072502575058800068696201)
      ·
        refine ⟨4554376931294100051522151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6072502575058800068696201 4554376931294100051522151)
        ·
          refine ⟨6831565396941150077283227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4554376931294100051522151 6831565396941150077283227)
          ·
            refine ⟨10247348095411725115924841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6831565396941150077283227 10247348095411725115924841)
            ·
              refine ⟨7685511071558793836943631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10247348095411725115924841 7685511071558793836943631)
              ·
                refine ⟨11528266607338190755415447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7685511071558793836943631 11528266607338190755415447)
                ·
                  refine ⟨17292399911007286133123171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11528266607338190755415447 17292399911007286133123171)
                  ·
                    refine ⟨25938599866510929199684757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17292399911007286133123171 25938599866510929199684757)
                    ·
                      refine ⟨1215871868742699806235223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25938599866510929199684757 1215871868742699806235223)
                      ·
                        rfl

theorem cell23_2367902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_2367902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2367902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2367902 prefixEnd_2367902 := by exact prefixLift 2367902
  have htrace : WordTrace (prefixWord ++ tailWord_2367902) baseStart_2367902 baseEnd_2367902 := by
    simpa [prefixWord, tailWord_2367902, baseEnd_2367902] using wordTrace_append hprefix tailTrace_2367902
  have hstable : (prefixWord ++ tailWord_2367902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367902).length < 2 ^ (prefixWord ++ tailWord_2367902).sum := by decide
  have hdescent : baseEnd_2367902 < baseStart_2367902 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2367975 : List Nat := [1, 1, 5, 2, 1, 1, 1, 2, 1, 4, 4]
def baseStart_2367975 : Nat := 118140960795 + 2367975 * 2 ^ 59
def prefixEnd_2367975 : Nat := 4983230072969 + 3 ^ 40 * 2367975 * 2
def baseEnd_2367975 : Nat := 1215909352830478020622387

theorem tailTrace_2367975 : CollatzResearch.WordTrace tailWord_2367975 prefixEnd_2367975 1215909352830478020622387 := by
  unfold tailWord_2367975
  simp only [CollatzResearch.WordTrace]
  refine ⟨86367143596238467777753379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57578095730825645185168919 86367143596238467777753379)
  ·
    refine ⟨129550715394357701666630069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86367143596238467777753379 129550715394357701666630069)
    ·
      refine ⟨12145379568221034531246569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 129550715394357701666630069 12145379568221034531246569)
      ·
        refine ⟨9109034676165775898434927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12145379568221034531246569 9109034676165775898434927)
        ·
          refine ⟨13663552014248663847652391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9109034676165775898434927 13663552014248663847652391)
          ·
            refine ⟨20495328021372995771478587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13663552014248663847652391 20495328021372995771478587)
            ·
              refine ⟨30742992032059493657217881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20495328021372995771478587 30742992032059493657217881)
              ·
                refine ⟨23057244024044620242913411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30742992032059493657217881 23057244024044620242913411)
                ·
                  refine ⟨34585866036066930364370117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23057244024044620242913411 34585866036066930364370117)
                  ·
                    refine ⟨6484849881762549443319397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34585866036066930364370117 6484849881762549443319397)
                    ·
                      refine ⟨1215909352830478020622387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6484849881762549443319397 1215909352830478020622387)
                      ·
                        rfl

theorem cell23_2367975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_2367975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2367975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2367975 prefixEnd_2367975 := by exact prefixLift 2367975
  have htrace : WordTrace (prefixWord ++ tailWord_2367975) baseStart_2367975 baseEnd_2367975 := by
    simpa [prefixWord, tailWord_2367975, baseEnd_2367975] using wordTrace_append hprefix tailTrace_2367975
  have hstable : (prefixWord ++ tailWord_2367975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2367975).length < 2 ^ (prefixWord ++ tailWord_2367975).sum := by decide
  have hdescent : baseEnd_2367975 < baseStart_2367975 := by decide
  rcases family_descends (prefixWord ++ tailWord_2367975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368006 : List Nat := [6, 2, 1, 1, 1, 1, 2, 1, 2, 6]
def baseStart_2368006 : Nat := 118140960795 + 2368006 * 2 ^ 59
def prefixEnd_2368006 : Nat := 4983230072969 + 3 ^ 40 * 2368006 * 2
def baseEnd_2368006 : Nat := 405308423576922466444915

theorem tailTrace_2368006 : CollatzResearch.WordTrace tailWord_2368006 prefixEnd_2368006 405308423576922466444915 := by
  unfold tailWord_2368006
  simp only [CollatzResearch.WordTrace]
  refine ⟨2699008570597692502254121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 57578849506084106714754581 2699008570597692502254121)
  ·
    refine ⟨2024256427948269376690591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2699008570597692502254121 2024256427948269376690591)
    ·
      refine ⟨3036384641922404065035887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2024256427948269376690591 3036384641922404065035887)
      ·
        refine ⟨4554576962883606097553831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3036384641922404065035887 4554576962883606097553831)
        ·
          refine ⟨6831865444325409146330747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4554576962883606097553831 6831865444325409146330747)
          ·
            refine ⟨10247798166488113719496121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6831865444325409146330747 10247798166488113719496121)
            ·
              refine ⟨7685848624866085289622091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10247798166488113719496121 7685848624866085289622091)
              ·
                refine ⟨11528772937299127934433137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7685848624866085289622091 11528772937299127934433137)
                ·
                  refine ⟨8646579702974345950824853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11528772937299127934433137 8646579702974345950824853)
                  ·
                    refine ⟨405308423576922466444915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8646579702974345950824853 405308423576922466444915)
                    ·
                      rfl

theorem cell23_2368006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_2368006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2368006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2368006 prefixEnd_2368006 := by exact prefixLift 2368006
  have htrace : WordTrace (prefixWord ++ tailWord_2368006) baseStart_2368006 baseEnd_2368006 := by
    simpa [prefixWord, tailWord_2368006, baseEnd_2368006] using wordTrace_append hprefix tailTrace_2368006
  have hstable : (prefixWord ++ tailWord_2368006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368006).length < 2 ^ (prefixWord ++ tailWord_2368006).sum := by decide
  have hdescent : baseEnd_2368006 < baseStart_2368006 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368012 : List Nat := [2, 2, 1, 2, 4, 1, 2, 1, 2, 3, 3]
def baseStart_2368012 : Nat := 118140960795 + 2368012 * 2 ^ 59
def prefixEnd_2368012 : Nat := 4983230072969 + 3 ^ 40 * 2368012 * 2
def baseEnd_2368012 : Nat := 1215928351614694375859717

theorem tailTrace_2368012 : CollatzResearch.WordTrace tailWord_2368012 prefixEnd_2368012 1215928351614694375859717 := by
  unfold tailWord_2368012
  simp only [CollatzResearch.WordTrace]
  refine ⟨43184246548552211548425145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57578995398069615397900193 43184246548552211548425145)
  ·
    refine ⟨32388184911414158661318859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43184246548552211548425145 32388184911414158661318859)
    ·
      refine ⟨48582277367121237991978289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32388184911414158661318859 48582277367121237991978289)
      ·
        refine ⟨36436708025340928493983717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48582277367121237991978289 36436708025340928493983717)
        ·
          refine ⟨6831882754751424092621947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36436708025340928493983717 6831882754751424092621947)
          ·
            refine ⟨10247824132127136138932921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6831882754751424092621947 10247824132127136138932921)
            ·
              refine ⟨7685868099095352104199691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10247824132127136138932921 7685868099095352104199691)
              ·
                refine ⟨11528802148643028156299537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7685868099095352104199691 11528802148643028156299537)
                ·
                  refine ⟨8646601611482271117224653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11528802148643028156299537 8646601611482271117224653)
                  ·
                    refine ⟨3242475604305851668959245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8646601611482271117224653 3242475604305851668959245)
                    ·
                      refine ⟨1215928351614694375859717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3242475604305851668959245 1215928351614694375859717)
                      ·
                        rfl

theorem cell23_2368012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 1, 2, 3, 3].length) (baseStart_2368012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2368012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2368012 prefixEnd_2368012 := by exact prefixLift 2368012
  have htrace : WordTrace (prefixWord ++ tailWord_2368012) baseStart_2368012 baseEnd_2368012 := by
    simpa [prefixWord, tailWord_2368012, baseEnd_2368012] using wordTrace_append hprefix tailTrace_2368012
  have hstable : (prefixWord ++ tailWord_2368012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368012).length < 2 ^ (prefixWord ++ tailWord_2368012).sum := by decide
  have hdescent : baseEnd_2368012 < baseStart_2368012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368013 : List Nat := [1, 7, 1, 1, 1, 1, 3, 1, 1, 4, 2]
def baseStart_2368013 : Nat := 118140960795 + 2368013 * 2 ^ 59
def prefixEnd_2368013 : Nat := 4983230072969 + 3 ^ 40 * 2368013 * 2
def baseEnd_2368013 : Nat := 1215928865095348871947213

theorem tailTrace_2368013 : CollatzResearch.WordTrace tailWord_2368013 prefixEnd_2368013 1215928865095348871947213 := by
  unfold tailWord_2368013
  simp only [CollatzResearch.WordTrace]
  refine ⟨86368529570100800267636693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57579019713400533511757795 86368529570100800267636693)
  ·
    refine ⟨2024262411799237506272735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 86368529570100800267636693 2024262411799237506272735)
    ·
      refine ⟨3036393617698856259409103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2024262411799237506272735 3036393617698856259409103)
      ·
        refine ⟨4554590426548284389113655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3036393617698856259409103 4554590426548284389113655)
        ·
          refine ⟨6831885639822426583670483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4554590426548284389113655 6831885639822426583670483)
          ·
            refine ⟨10247828459733639875505725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6831885639822426583670483 10247828459733639875505725)
            ·
              refine ⟨3842935672400114953314647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10247828459733639875505725 3842935672400114953314647)
              ·
                refine ⟨5764403508600172429971971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3842935672400114953314647 5764403508600172429971971)
                ·
                  refine ⟨8646605262900258644957957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5764403508600172429971971 8646605262900258644957957)
                  ·
                    refine ⟨1621238486793798495929617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8646605262900258644957957 1621238486793798495929617)
                    ·
                      refine ⟨1215928865095348871947213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1621238486793798495929617 1215928865095348871947213)
                      ·
                        rfl

theorem cell23_2368013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_2368013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2368013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2368013 prefixEnd_2368013 := by exact prefixLift 2368013
  have htrace : WordTrace (prefixWord ++ tailWord_2368013) baseStart_2368013 baseEnd_2368013 := by
    simpa [prefixWord, tailWord_2368013, baseEnd_2368013] using wordTrace_append hprefix tailTrace_2368013
  have hstable : (prefixWord ++ tailWord_2368013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368013).length < 2 ^ (prefixWord ++ tailWord_2368013).sum := by decide
  have hdescent : baseEnd_2368013 < baseStart_2368013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368109 : List Nat := [1, 5, 1, 1, 3, 2, 2, 2, 6]
def baseStart_2368109 : Nat := 118140960795 + 2368109 * 2 ^ 59
def prefixEnd_2368109 : Nat := 4983230072969 + 3 ^ 40 * 2368109 * 2
def baseEnd_2368109 : Nat := 135108684359797832927419

theorem tailTrace_2368109 : CollatzResearch.WordTrace tailWord_2368109 prefixEnd_2368109 135108684359797832927419 := by
  unfold tailWord_2368109
  simp only [CollatzResearch.WordTrace]
  refine ⟨86372030977753008663131381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57581353985168672442087587 86372030977753008663131381)
  ·
    refine ⟨8097377904164344562168567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 86372030977753008663131381 8097377904164344562168567)
    ·
      refine ⟨12146066856246516843252851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8097377904164344562168567 12146066856246516843252851)
      ·
        refine ⟨18219100284369775264879277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12146066856246516843252851 18219100284369775264879277)
        ·
          refine ⟨6832162606638665724329729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18219100284369775264879277 6832162606638665724329729)
          ·
            refine ⟨5124121954978999293247297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6832162606638665724329729 5124121954978999293247297)
            ·
              refine ⟨3843091466234249469935473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5124121954978999293247297 3843091466234249469935473)
              ·
                refine ⟨2882318599675687102451605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3843091466234249469935473 2882318599675687102451605)
                ·
                  refine ⟨135108684359797832927419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2882318599675687102451605 135108684359797832927419)
                  ·
                    rfl

theorem cell23_2368109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 2, 6].length) (baseStart_2368109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2368109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2368109 prefixEnd_2368109 := by exact prefixLift 2368109
  have htrace : WordTrace (prefixWord ++ tailWord_2368109) baseStart_2368109 baseEnd_2368109 := by
    simpa [prefixWord, tailWord_2368109, baseEnd_2368109] using wordTrace_append hprefix tailTrace_2368109
  have hstable : (prefixWord ++ tailWord_2368109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368109).length < 2 ^ (prefixWord ++ tailWord_2368109).sum := by decide
  have hdescent : baseEnd_2368109 < baseStart_2368109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368129 : List Nat := [1, 2, 4, 2, 1, 1, 2, 2, 1, 5, 2]
def baseStart_2368129 : Nat := 118140960795 + 2368129 * 2 ^ 59
def prefixEnd_2368129 : Nat := 4983230072969 + 3 ^ 40 * 2368129 * 2
def baseEnd_2368129 : Nat := 1215988428851270418096679

theorem tailTrace_2368129 : CollatzResearch.WordTrace tailWord_2368129 prefixEnd_2368129 1215988428851270418096679 := by
  unfold tailWord_2368129
  simp only [CollatzResearch.WordTrace]
  refine ⟨86372760437680552078859441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57581840291787034719239627 86372760437680552078859441)
  ·
    refine ⟨64779570328260414059144581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86372760437680552078859441 64779570328260414059144581)
    ·
      refine ⟨12146169436548827636089609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64779570328260414059144581 12146169436548827636089609)
      ·
        refine ⟨9109627077411620727067207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12146169436548827636089609 9109627077411620727067207)
        ·
          refine ⟨13664440616117431090600811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9109627077411620727067207 13664440616117431090600811)
          ·
            refine ⟨20496660924176146635901217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13664440616117431090600811 20496660924176146635901217)
            ·
              refine ⟨15372495693132109976925913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20496660924176146635901217 15372495693132109976925913)
              ·
                refine ⟨11529371769849082482694435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15372495693132109976925913 11529371769849082482694435)
                ·
                  refine ⟨17294057654773623724041653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11529371769849082482694435 17294057654773623724041653)
                  ·
                    refine ⟨1621317905135027224128905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17294057654773623724041653 1621317905135027224128905)
                    ·
                      refine ⟨1215988428851270418096679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1621317905135027224128905 1215988428851270418096679)
                      ·
                        rfl

theorem cell23_2368129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 2, 1, 5, 2].length) (baseStart_2368129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2368129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2368129 prefixEnd_2368129 := by exact prefixLift 2368129
  have htrace : WordTrace (prefixWord ++ tailWord_2368129) baseStart_2368129 baseEnd_2368129 := by
    simpa [prefixWord, tailWord_2368129, baseEnd_2368129] using wordTrace_append hprefix tailTrace_2368129
  have hstable : (prefixWord ++ tailWord_2368129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368129).length < 2 ^ (prefixWord ++ tailWord_2368129).sum := by decide
  have hdescent : baseEnd_2368129 < baseStart_2368129 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368130 : List Nat := [3, 4, 3, 1, 1, 1, 1, 2, 3, 4]
def baseStart_2368130 : Nat := 118140960795 + 2368130 * 2 ^ 59
def prefixEnd_2368130 : Nat := 4983230072969 + 3 ^ 40 * 2368130 * 2
def baseEnd_2368130 : Nat := 405329647443974971394725

theorem tailTrace_2368130 : CollatzResearch.WordTrace tailWord_2368130 prefixEnd_2368130 405329647443974971394725 := by
  unfold tailWord_2368130
  simp only [CollatzResearch.WordTrace]
  refine ⟨21593199227669232312411461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57581864607117952833097229 21593199227669232312411461)
  ·
    refine ⟨4048724855187981058577149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21593199227669232312411461 4048724855187981058577149)
    ·
      refine ⟨1518271820695492896966431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4048724855187981058577149 1518271820695492896966431)
      ·
        refine ⟨2277407731043239345449647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1518271820695492896966431 2277407731043239345449647)
        ·
          refine ⟨3416111596564859018174471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2277407731043239345449647 3416111596564859018174471)
          ·
            refine ⟨5124167394847288527261707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3416111596564859018174471 5124167394847288527261707)
            ·
              refine ⟨7686251092270932790892561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5124167394847288527261707 7686251092270932790892561)
              ·
                refine ⟨5764688319203199593169421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7686251092270932790892561 5764688319203199593169421)
                ·
                  refine ⟨2161758119701199847438533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5764688319203199593169421 2161758119701199847438533)
                  ·
                    refine ⟨405329647443974971394725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2161758119701199847438533 405329647443974971394725)
                    ·
                      rfl

theorem cell23_2368130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_2368130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2368130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2368130 prefixEnd_2368130 := by exact prefixLift 2368130
  have htrace : WordTrace (prefixWord ++ tailWord_2368130) baseStart_2368130 baseEnd_2368130 := by
    simpa [prefixWord, tailWord_2368130, baseEnd_2368130] using wordTrace_append hprefix tailTrace_2368130
  have hstable : (prefixWord ++ tailWord_2368130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368130).length < 2 ^ (prefixWord ++ tailWord_2368130).sum := by decide
  have hdescent : baseEnd_2368130 < baseStart_2368130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368146 : List Nat := [3, 2, 3, 1, 2, 2, 1, 1, 1, 5, 2]
def baseStart_2368146 : Nat := 118140960795 + 2368146 * 2 ^ 59
def prefixEnd_2368146 : Nat := 4983230072969 + 3 ^ 40 * 2368146 * 2
def baseEnd_2368146 : Nat := 1215997158022396851584101

theorem tailTrace_2368146 : CollatzResearch.WordTrace tailWord_2368146 prefixEnd_2368146 1215997158022396851584101 := by
  unfold tailWord_2368146
  simp only [CollatzResearch.WordTrace]
  refine ⟨21593345119654740995557073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57582253652412642654818861 21593345119654740995557073)
  ·
    refine ⟨16195008839741055746667805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21593345119654740995557073 16195008839741055746667805)
    ·
      refine ⟨6073128314902895905000427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16195008839741055746667805 6073128314902895905000427)
      ·
        refine ⟨9109692472354343857500641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6073128314902895905000427 9109692472354343857500641)
        ·
          refine ⟨6832269354265757893125481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9109692472354343857500641 6832269354265757893125481)
          ·
            refine ⟨5124202015699318419844111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6832269354265757893125481 5124202015699318419844111)
            ·
              refine ⟨7686303023548977629766167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5124202015699318419844111 7686303023548977629766167)
              ·
                refine ⟨11529454535323466444649251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7686303023548977629766167 11529454535323466444649251)
                ·
                  refine ⟨17294181802985199666973877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11529454535323466444649251 17294181802985199666973877)
                  ·
                    refine ⟨1621329544029862468778801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17294181802985199666973877 1621329544029862468778801)
                    ·
                      refine ⟨1215997158022396851584101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1621329544029862468778801 1215997158022396851584101)
                      ·
                        rfl

theorem cell23_2368146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 1, 1, 5, 2].length) (baseStart_2368146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2368146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2368146 prefixEnd_2368146 := by exact prefixLift 2368146
  have htrace : WordTrace (prefixWord ++ tailWord_2368146) baseStart_2368146 baseEnd_2368146 := by
    simpa [prefixWord, tailWord_2368146, baseEnd_2368146] using wordTrace_append hprefix tailTrace_2368146
  have hstable : (prefixWord ++ tailWord_2368146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368146).length < 2 ^ (prefixWord ++ tailWord_2368146).sum := by decide
  have hdescent : baseEnd_2368146 < baseStart_2368146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368152 : List Nat := [2, 1, 2, 4, 1, 1, 1, 4, 1, 6]
def baseStart_2368152 : Nat := 118140960795 + 2368152 * 2 ^ 59
def prefixEnd_2368152 : Nat := 4983230072969 + 3 ^ 40 * 2368152 * 2
def baseEnd_2368152 : Nat := 405333412968774609369691

theorem tailTrace_2368152 : CollatzResearch.WordTrace tailWord_2368152 prefixEnd_2368152 405333412968774609369691 := by
  unfold tailWord_2368152
  simp only [CollatzResearch.WordTrace]
  refine ⟨43186799658298613503473355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57582399544398151337964473 43186799658298613503473355)
  ·
    refine ⟨64780199487447920255210033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43186799658298613503473355 64780199487447920255210033)
    ·
      refine ⟨48585149615585940191407525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64780199487447920255210033 48585149615585940191407525)
      ·
        refine ⟨9109715552922363785888911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48585149615585940191407525 9109715552922363785888911)
        ·
          refine ⟨13664573329383545678833367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9109715552922363785888911 13664573329383545678833367)
          ·
            refine ⟨20496859994075318518250051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13664573329383545678833367 20496859994075318518250051)
            ·
              refine ⟨30745289991112977777375077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20496859994075318518250051 30745289991112977777375077)
              ·
                refine ⟨5764741873333683333257827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30745289991112977777375077 5764741873333683333257827)
                ·
                  refine ⟨8647112810000524999886741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5764741873333683333257827 8647112810000524999886741)
                  ·
                    refine ⟨405333412968774609369691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8647112810000524999886741 405333412968774609369691)
                    ·
                      rfl

theorem cell23_2368152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 4, 1, 6].length) (baseStart_2368152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2368152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2368152 prefixEnd_2368152 := by exact prefixLift 2368152
  have htrace : WordTrace (prefixWord ++ tailWord_2368152) baseStart_2368152 baseEnd_2368152 := by
    simpa [prefixWord, tailWord_2368152, baseEnd_2368152] using wordTrace_append hprefix tailTrace_2368152
  have hstable : (prefixWord ++ tailWord_2368152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368152).length < 2 ^ (prefixWord ++ tailWord_2368152).sum := by decide
  have hdescent : baseEnd_2368152 < baseStart_2368152 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368156 : List Nat := [2, 2, 3, 2, 2, 1, 4, 1, 1, 5]
def baseStart_2368156 : Nat := 118140960795 + 2368156 * 2 ^ 59
def prefixEnd_2368156 : Nat := 4983230072969 + 3 ^ 40 * 2368156 * 2
def baseEnd_2368156 : Nat := 405334097609647270819685

theorem tailTrace_2368156 : CollatzResearch.WordTrace tailWord_2368156 prefixEnd_2368156 405334097609647270819685 := by
  unfold tailWord_2368156
  simp only [CollatzResearch.WordTrace]
  refine ⟨43186872604291367845046161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57582496805721823793394881 43186872604291367845046161)
  ·
    refine ⟨32390154453218525883784621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43186872604291367845046161 32390154453218525883784621)
    ·
      refine ⟨12146307919956947206419233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32390154453218525883784621 12146307919956947206419233)
      ·
        refine ⟨9109730939967710404814425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12146307919956947206419233 9109730939967710404814425)
        ·
          refine ⟨6832298204975782803610819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9109730939967710404814425 6832298204975782803610819)
          ·
            refine ⟨10248447307463674205416229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6832298204975782803610819 10248447307463674205416229)
            ·
              refine ⟨1921583870149438913515543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10248447307463674205416229 1921583870149438913515543)
              ·
                refine ⟨2882375805224158370273315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1921583870149438913515543 2882375805224158370273315)
                ·
                  refine ⟨4323563707836237555409973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2882375805224158370273315 4323563707836237555409973)
                  ·
                    refine ⟨405334097609647270819685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4323563707836237555409973 405334097609647270819685)
                    ·
                      rfl

theorem cell23_2368156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 4, 1, 1, 5].length) (baseStart_2368156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2368156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2368156 prefixEnd_2368156 := by exact prefixLift 2368156
  have htrace : WordTrace (prefixWord ++ tailWord_2368156) baseStart_2368156 baseEnd_2368156 := by
    simpa [prefixWord, tailWord_2368156, baseEnd_2368156] using wordTrace_append hprefix tailTrace_2368156
  have hstable : (prefixWord ++ tailWord_2368156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368156).length < 2 ^ (prefixWord ++ tailWord_2368156).sum := by decide
  have hdescent : baseEnd_2368156 < baseStart_2368156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368170 : List Nat := [3, 1, 5, 2, 1, 1, 2, 1, 3, 1, 3]
def baseStart_2368170 : Nat := 118140960795 + 2368170 * 2 ^ 59
def prefixEnd_2368170 : Nat := 4983230072969 + 3 ^ 40 * 2368170 * 2
def baseEnd_2368170 : Nat := 1216009481558104757683991

theorem tailTrace_2368170 : CollatzResearch.WordTrace tailWord_2368170 prefixEnd_2368170 1216009481558104757683991 := by
  unfold tailWord_2368170
  simp only [CollatzResearch.WordTrace]
  refine ⟨21593563957633004020275491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57582837220354677387401309 21593563957633004020275491)
  ·
    refine ⟨32390345936449506030413237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21593563957633004020275491 32390345936449506030413237)
    ·
      refine ⟨3036594931542141190351241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32390345936449506030413237 3036594931542141190351241)
      ·
        refine ⟨2277446198656605892763431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3036594931542141190351241 2277446198656605892763431)
        ·
          refine ⟨3416169297984908839145147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2277446198656605892763431 3416169297984908839145147)
          ·
            refine ⟨5124253946977363258717721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3416169297984908839145147 5124253946977363258717721)
            ·
              refine ⟨3843190460233022444038291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5124253946977363258717721 3843190460233022444038291)
              ·
                refine ⟨5764785690349533666057437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3843190460233022444038291 5764785690349533666057437)
                ·
                  refine ⟨2161794633881075124771539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5764785690349533666057437 2161794633881075124771539)
                  ·
                    refine ⟨3242691950821612687157309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2161794633881075124771539 3242691950821612687157309)
                    ·
                      refine ⟨1216009481558104757683991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3242691950821612687157309 1216009481558104757683991)
                      ·
                        rfl

theorem cell23_2368170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_2368170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2368170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2368170 prefixEnd_2368170 := by exact prefixLift 2368170
  have htrace : WordTrace (prefixWord ++ tailWord_2368170) baseStart_2368170 baseEnd_2368170 := by
    simpa [prefixWord, tailWord_2368170, baseEnd_2368170] using wordTrace_append hprefix tailTrace_2368170
  have hstable : (prefixWord ++ tailWord_2368170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368170).length < 2 ^ (prefixWord ++ tailWord_2368170).sum := by decide
  have hdescent : baseEnd_2368170 < baseStart_2368170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368186 : List Nat := [3, 1, 1, 1, 2, 3, 5, 1, 2, 4]
def baseStart_2368186 : Nat := 118140960795 + 2368186 * 2 ^ 59
def prefixEnd_2368186 : Nat := 4983230072969 + 3 ^ 40 * 2368186 * 2
def baseEnd_2368186 : Nat := 405339232416192231694639

theorem tailTrace_2368186 : CollatzResearch.WordTrace tailWord_2368186 prefixEnd_2368186 405339232416192231694639 := by
  unfold tailWord_2368186
  simp only [CollatzResearch.WordTrace]
  refine ⟨21593709849618512703421103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57583226265649367209122941 21593709849618512703421103)
  ·
    refine ⟨32390564774427769055131655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21593709849618512703421103 32390564774427769055131655)
    ·
      refine ⟨48585847161641653582697483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32390564774427769055131655 48585847161641653582697483)
      ·
        refine ⟨72878770742462480374046225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48585847161641653582697483 72878770742462480374046225)
        ·
          refine ⟨54659078056846860280534669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72878770742462480374046225 54659078056846860280534669)
          ·
            refine ⟨20497154271317572605200501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54659078056846860280534669 20497154271317572605200501)
            ·
              refine ⟨1921608212936022431737547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20497154271317572605200501 1921608212936022431737547)
              ·
                refine ⟨2882412319404033647606321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1921608212936022431737547 2882412319404033647606321)
                ·
                  refine ⟨2161809239553025235704741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2882412319404033647606321 2161809239553025235704741)
                  ·
                    refine ⟨405339232416192231694639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2161809239553025235704741 405339232416192231694639)
                    ·
                      rfl

theorem cell23_2368186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 5, 1, 2, 4].length) (baseStart_2368186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2368186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2368186 prefixEnd_2368186 := by exact prefixLift 2368186
  have htrace : WordTrace (prefixWord ++ tailWord_2368186) baseStart_2368186 baseEnd_2368186 := by
    simpa [prefixWord, tailWord_2368186, baseEnd_2368186] using wordTrace_append hprefix tailTrace_2368186
  have hstable : (prefixWord ++ tailWord_2368186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368186).length < 2 ^ (prefixWord ++ tailWord_2368186).sum := by decide
  have hdescent : baseEnd_2368186 < baseStart_2368186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368189 : List Nat := [1, 4, 1, 2, 1, 3, 3, 1, 1, 2, 4]
def baseStart_2368189 : Nat := 118140960795 + 2368189 * 2 ^ 59
def prefixEnd_2368189 : Nat := 4983230072969 + 3 ^ 40 * 2368189 * 2
def baseEnd_2368189 : Nat := 1216019237690540183346403

theorem tailTrace_2368189 : CollatzResearch.WordTrace tailWord_2368189 prefixEnd_2368189 1216019237690540183346403 := by
  unfold tailWord_2368189
  simp only [CollatzResearch.WordTrace]
  refine ⟨86374948817463182326043621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57583299211642121550695747 86374948817463182326043621)
  ·
    refine ⟨16195302903274346686133179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86374948817463182326043621 16195302903274346686133179)
    ·
      refine ⟨24292954354911520029199769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16195302903274346686133179 24292954354911520029199769)
      ·
        refine ⟨18219715766183640021899827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24292954354911520029199769 18219715766183640021899827)
        ·
          refine ⟨27329573649275460032849741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18219715766183640021899827 27329573649275460032849741)
          ·
            refine ⟨10248590118478297512318653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27329573649275460032849741 10248590118478297512318653)
            ·
              refine ⟨3843221294429361567119495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10248590118478297512318653 3843221294429361567119495)
              ·
                refine ⟨5764831941644042350679243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3843221294429361567119495 5764831941644042350679243)
                ·
                  refine ⟨8647247912466063526018865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5764831941644042350679243 8647247912466063526018865)
                  ·
                    refine ⟨6485435934349547644514149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8647247912466063526018865 6485435934349547644514149)
                    ·
                      refine ⟨1216019237690540183346403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6485435934349547644514149 1216019237690540183346403)
                      ·
                        rfl

theorem cell23_2368189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 1, 1, 2, 4].length) (baseStart_2368189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2368189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2368189 prefixEnd_2368189 := by exact prefixLift 2368189
  have htrace : WordTrace (prefixWord ++ tailWord_2368189) baseStart_2368189 baseEnd_2368189 := by
    simpa [prefixWord, tailWord_2368189, baseEnd_2368189] using wordTrace_append hprefix tailTrace_2368189
  have hstable : (prefixWord ++ tailWord_2368189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368189).length < 2 ^ (prefixWord ++ tailWord_2368189).sum := by decide
  have hdescent : baseEnd_2368189 < baseStart_2368189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368196 : List Nat := [2, 3, 3, 1, 1, 2, 1, 4, 1, 2, 3]
def baseStart_2368196 : Nat := 118140960795 + 2368196 * 2 ^ 59
def prefixEnd_2368196 : Nat := 4983230072969 + 3 ^ 40 * 2368196 * 2
def baseEnd_2368196 : Nat := 1216022832055121655958871

theorem tailTrace_2368196 : CollatzResearch.WordTrace tailWord_2368196 prefixEnd_2368196 1216022832055121655958871 := by
  unfold tailWord_2368196
  simp only [CollatzResearch.WordTrace]
  refine ⟨43187602064218911260774221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57583469418958548347698961 43187602064218911260774221)
  ·
    refine ⟨16195350774082091722790333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43187602064218911260774221 16195350774082091722790333)
    ·
      refine ⟨6073256540280784396046375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16195350774082091722790333 6073256540280784396046375)
      ·
        refine ⟨9109884810421176594069563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6073256540280784396046375 9109884810421176594069563)
        ·
          refine ⟨13664827215631764891104345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9109884810421176594069563 13664827215631764891104345)
          ·
            refine ⟨10248620411723823668328259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13664827215631764891104345 10248620411723823668328259)
            ·
              refine ⟨15372930617585735502492389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10248620411723823668328259 15372930617585735502492389)
              ·
                refine ⟨2882424490797325406717323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15372930617585735502492389 2882424490797325406717323)
                ·
                  refine ⟨4323636736195988110075985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2882424490797325406717323 4323636736195988110075985)
                  ·
                    refine ⟨3242727552146991082556989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4323636736195988110075985 3242727552146991082556989)
                    ·
                      refine ⟨1216022832055121655958871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3242727552146991082556989 1216022832055121655958871)
                      ·
                        rfl

theorem cell23_2368196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_2368196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2368196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2368196 prefixEnd_2368196 := by exact prefixLift 2368196
  have htrace : WordTrace (prefixWord ++ tailWord_2368196) baseStart_2368196 baseEnd_2368196 := by
    simpa [prefixWord, tailWord_2368196, baseEnd_2368196] using wordTrace_append hprefix tailTrace_2368196
  have hstable : (prefixWord ++ tailWord_2368196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368196).length < 2 ^ (prefixWord ++ tailWord_2368196).sum := by decide
  have hdescent : baseEnd_2368196 < baseStart_2368196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368209 : List Nat := [1, 2, 2, 1, 2, 3, 1, 1, 6, 1, 3]
def baseStart_2368209 : Nat := 118140960795 + 2368209 * 2 ^ 59
def prefixEnd_2368209 : Nat := 4983230072969 + 3 ^ 40 * 2368209 * 2
def baseEnd_2368209 : Nat := 1216029507303630105096311

theorem tailTrace_2368209 : CollatzResearch.WordTrace tailWord_2368209 prefixEnd_2368209 1216029507303630105096311 := by
  unfold tailWord_2368209
  simp only [CollatzResearch.WordTrace]
  refine ⟨86375678277390725741771681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57583785518260483827847787 86375678277390725741771681)
  ·
    refine ⟨64781758708043044306328761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86375678277390725741771681 64781758708043044306328761)
    ·
      refine ⟨48586319031032283229746571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64781758708043044306328761 48586319031032283229746571)
      ·
        refine ⟨72879478546548424844619857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48586319031032283229746571 72879478546548424844619857)
        ·
          refine ⟨54659608909911318633464893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72879478546548424844619857 54659608909911318633464893)
          ·
            refine ⟨20497353341216744487549335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54659608909911318633464893 20497353341216744487549335)
            ·
              refine ⟨30746030011825116731324003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20497353341216744487549335 30746030011825116731324003)
              ·
                refine ⟨46119045017737675096986005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30746030011825116731324003 46119045017737675096986005)
                ·
                  refine ⟨2161830235206453520171219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 46119045017737675096986005 2161830235206453520171219)
                  ·
                    refine ⟨3242745352809680280256829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2161830235206453520171219 3242745352809680280256829)
                    ·
                      refine ⟨1216029507303630105096311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3242745352809680280256829 1216029507303630105096311)
                      ·
                        rfl

theorem cell23_2368209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 6, 1, 3].length) (baseStart_2368209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2368209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2368209 prefixEnd_2368209 := by exact prefixLift 2368209
  have htrace : WordTrace (prefixWord ++ tailWord_2368209) baseStart_2368209 baseEnd_2368209 := by
    simpa [prefixWord, tailWord_2368209, baseEnd_2368209] using wordTrace_append hprefix tailTrace_2368209
  have hstable : (prefixWord ++ tailWord_2368209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368209).length < 2 ^ (prefixWord ++ tailWord_2368209).sum := by decide
  have hdescent : baseEnd_2368209 < baseStart_2368209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368227 : List Nat := [1, 1, 1, 7, 1, 2, 3, 2, 1, 2, 2]
def baseStart_2368227 : Nat := 118140960795 + 2368227 * 2 ^ 59
def prefixEnd_2368227 : Nat := 4983230072969 + 3 ^ 40 * 2368227 * 2
def baseEnd_2368227 : Nat := 1216038749955411034671229

theorem tailTrace_2368227 : CollatzResearch.WordTrace tailWord_2368227 prefixEnd_2368227 1216038749955411034671229 := by
  unfold tailWord_2368227
  simp only [CollatzResearch.WordTrace]
  refine ⟨86376334791325514815926935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57584223194217009877284623 86376334791325514815926935)
  ·
    refine ⟨129564502186988272223890403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86376334791325514815926935 129564502186988272223890403)
    ·
      refine ⟨194346753280482408335835605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129564502186988272223890403 194346753280482408335835605)
      ·
        refine ⟨4555002030011306445371147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 194346753280482408335835605 4555002030011306445371147)
        ·
          refine ⟨6832503045016959668056721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4555002030011306445371147 6832503045016959668056721)
          ·
            refine ⟨5124377283762719751042541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6832503045016959668056721 5124377283762719751042541)
            ·
              refine ⟨1921641481411019906640953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5124377283762719751042541 1921641481411019906640953)
              ·
                refine ⟨1441231111058264929980715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1921641481411019906640953 1441231111058264929980715)
                ·
                  refine ⟨2161846666587397394971073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1441231111058264929980715 2161846666587397394971073)
                  ·
                    refine ⟨1621384999940548046228305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2161846666587397394971073 1621384999940548046228305)
                    ·
                      refine ⟨1216038749955411034671229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1621384999940548046228305 1216038749955411034671229)
                      ·
                        rfl

theorem cell23_2368227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_2368227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2368227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2368227 prefixEnd_2368227 := by exact prefixLift 2368227
  have htrace : WordTrace (prefixWord ++ tailWord_2368227) baseStart_2368227 baseEnd_2368227 := by
    simpa [prefixWord, tailWord_2368227, baseEnd_2368227] using wordTrace_append hprefix tailTrace_2368227
  have hstable : (prefixWord ++ tailWord_2368227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368227).length < 2 ^ (prefixWord ++ tailWord_2368227).sum := by decide
  have hdescent : baseEnd_2368227 < baseStart_2368227 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368249 : List Nat := [1, 2, 1, 3, 1, 1, 1, 2, 5, 4, 2]
def baseStart_2368249 : Nat := 118140960795 + 2368249 * 2 ^ 59
def prefixEnd_2368249 : Nat := 4983230072969 + 3 ^ 40 * 2368249 * 2
def baseEnd_2368249 : Nat := 1216050046529809948596127

theorem tailTrace_2368249 : CollatzResearch.WordTrace tailWord_2368249 prefixEnd_2368249 1216050046529809948596127 := by
  unfold tailWord_2368249
  simp only [CollatzResearch.WordTrace]
  refine ⟨86377137197245812573227801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57584758131497208382151867 86377137197245812573227801)
  ·
    refine ⟨64782852897934359429920851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86377137197245812573227801 64782852897934359429920851)
    ·
      refine ⟨97174279346901539144881277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64782852897934359429920851 97174279346901539144881277)
      ·
        refine ⟨36440354755088077179330479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97174279346901539144881277 36440354755088077179330479)
        ·
          refine ⟨54660532132632115768995719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36440354755088077179330479 54660532132632115768995719)
          ·
            refine ⟨81990798198948173653493579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54660532132632115768995719 81990798198948173653493579)
            ·
              refine ⟨122986197298422260480240369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81990798198948173653493579 122986197298422260480240369)
              ·
                refine ⟨92239647973816695360180277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 122986197298422260480240369 92239647973816695360180277)
                ·
                  refine ⟨8647466997545315190016901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 92239647973816695360180277 8647466997545315190016901)
                  ·
                    refine ⟨1621400062039746598128169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8647466997545315190016901 1621400062039746598128169)
                    ·
                      refine ⟨1216050046529809948596127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1621400062039746598128169 1216050046529809948596127)
                      ·
                        rfl

theorem cell23_2368249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 5, 4, 2].length) (baseStart_2368249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2368249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2368249 prefixEnd_2368249 := by exact prefixLift 2368249
  have htrace : WordTrace (prefixWord ++ tailWord_2368249) baseStart_2368249 baseEnd_2368249 := by
    simpa [prefixWord, tailWord_2368249, baseEnd_2368249] using wordTrace_append hprefix tailTrace_2368249
  have hstable : (prefixWord ++ tailWord_2368249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368249).length < 2 ^ (prefixWord ++ tailWord_2368249).sum := by decide
  have hdescent : baseEnd_2368249 < baseStart_2368249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368266 : List Nat := [3, 1, 2, 2, 1, 2, 3, 2, 1, 4, 2]
def baseStart_2368266 : Nat := 118140960795 + 2368266 * 2 ^ 59
def prefixEnd_2368266 : Nat := 4983230072969 + 3 ^ 40 * 2368266 * 2
def baseEnd_2368266 : Nat := 1216058775700936382083549

theorem tailTrace_2368266 : CollatzResearch.WordTrace tailWord_2368266 prefixEnd_2368266 1216058775700936382083549 := by
  unfold tailWord_2368266
  simp only [CollatzResearch.WordTrace]
  refine ⟨21594439309546056119149163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57585171492122816317731101 21594439309546056119149163)
  ·
    refine ⟨32391658964319084178723745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21594439309546056119149163 32391658964319084178723745)
    ·
      refine ⟨24293744223239313134042809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32391658964319084178723745 24293744223239313134042809)
      ·
        refine ⟨18220308167429484850532107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24293744223239313134042809 18220308167429484850532107)
        ·
          refine ⟨27330462251144227275798161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18220308167429484850532107 27330462251144227275798161)
          ·
            refine ⟨20497846688358170456848621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27330462251144227275798161 20497846688358170456848621)
            ·
              refine ⟨7686692508134313921318233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20497846688358170456848621 7686692508134313921318233)
              ·
                refine ⟨5765019381100735440988675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7686692508134313921318233 5765019381100735440988675)
                ·
                  refine ⟨8647529071651103161483013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5765019381100735440988675 8647529071651103161483013)
                  ·
                    refine ⟨1621411700934581842778065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8647529071651103161483013 1621411700934581842778065)
                    ·
                      refine ⟨1216058775700936382083549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1621411700934581842778065 1216058775700936382083549)
                      ·
                        rfl

theorem cell23_2368266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 2, 1, 4, 2].length) (baseStart_2368266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2368266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2368266 prefixEnd_2368266 := by exact prefixLift 2368266
  have htrace : WordTrace (prefixWord ++ tailWord_2368266) baseStart_2368266 baseEnd_2368266 := by
    simpa [prefixWord, tailWord_2368266, baseEnd_2368266] using wordTrace_append hprefix tailTrace_2368266
  have hstable : (prefixWord ++ tailWord_2368266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368266).length < 2 ^ (prefixWord ++ tailWord_2368266).sum := by decide
  have hdescent : baseEnd_2368266 < baseStart_2368266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368319 : List Nat := [1, 1, 2, 2, 5, 2, 1, 1, 1, 7]
def baseStart_2368319 : Nat := 118140960795 + 2368319 * 2 ^ 59
def prefixEnd_2368319 : Nat := 4983230072969 + 3 ^ 40 * 2368319 * 2
def baseEnd_2368319 : Nat := 405361996725208224906935

theorem tailTrace_2368319 : CollatzResearch.WordTrace tailWord_2368319 prefixEnd_2368319 405361996725208224906935 := by
  unfold tailWord_2368319
  simp only [CollatzResearch.WordTrace]
  refine ⟨86379690306992214528276011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57586460204661476352184007 86379690306992214528276011)
  ·
    refine ⟨129569535460488321792414017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86379690306992214528276011 129569535460488321792414017)
    ·
      refine ⟨97177151595366241344310513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129569535460488321792414017 97177151595366241344310513)
      ·
        refine ⟨72882863696524681008232885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97177151595366241344310513 72882863696524681008232885)
        ·
          refine ⟨6832768471549188844521833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 72882863696524681008232885 6832768471549188844521833)
          ·
            refine ⟨5124576353661891633391375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6832768471549188844521833 5124576353661891633391375)
            ·
              refine ⟨7686864530492837450087063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5124576353661891633391375 7686864530492837450087063)
              ·
                refine ⟨11530296795739256175130595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7686864530492837450087063 11530296795739256175130595)
                ·
                  refine ⟨17295445193608884262695893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11530296795739256175130595 17295445193608884262695893)
                  ·
                    refine ⟨405361996725208224906935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17295445193608884262695893 405361996725208224906935)
                    ·
                      rfl

theorem cell23_2368319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 1, 1, 7].length) (baseStart_2368319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2368319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2368319 prefixEnd_2368319 := by exact prefixLift 2368319
  have htrace : WordTrace (prefixWord ++ tailWord_2368319) baseStart_2368319 baseEnd_2368319 := by
    simpa [prefixWord, tailWord_2368319, baseEnd_2368319] using wordTrace_append hprefix tailTrace_2368319
  have hstable : (prefixWord ++ tailWord_2368319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368319).length < 2 ^ (prefixWord ++ tailWord_2368319).sum := by decide
  have hdescent : baseEnd_2368319 < baseStart_2368319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368339 : List Nat := [1, 1, 1, 2, 1, 1, 3, 6, 2, 1, 4]
def baseStart_2368339 : Nat := 118140960795 + 2368339 * 2 ^ 59
def prefixEnd_2368339 : Nat := 4983230072969 + 3 ^ 40 * 2368339 * 2
def baseEnd_2368339 : Nat := 1216096259788714596470713

theorem tailTrace_2368339 : CollatzResearch.WordTrace tailWord_2368339 prefixEnd_2368339 1216096259788714596470713 := by
  unfold tailWord_2368339
  simp only [CollatzResearch.WordTrace]
  refine ⟨86380419766919757944004071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57586946511279838629336047 86380419766919757944004071)
  ·
    refine ⟨129570629650379636916006107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86380419766919757944004071 129570629650379636916006107)
    ·
      refine ⟨194355944475569455374009161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129570629650379636916006107 194355944475569455374009161)
      ·
        refine ⟨145766958356677091530506871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194355944475569455374009161 145766958356677091530506871)
        ·
          refine ⟨218650437535015637295760307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145766958356677091530506871 218650437535015637295760307)
          ·
            refine ⟨327975656302523455943640461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 218650437535015637295760307 327975656302523455943640461)
            ·
              refine ⟨122990871113446295978865173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 327975656302523455943640461 122990871113446295978865173)
              ·
                refine ⟨5765197083442795124009305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 122990871113446295978865173 5765197083442795124009305)
                ·
                  refine ⟨4323897812582096343006979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5765197083442795124009305 4323897812582096343006979)
                  ·
                    refine ⟨6485846718873144514510469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4323897812582096343006979 6485846718873144514510469)
                    ·
                      refine ⟨1216096259788714596470713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6485846718873144514510469 1216096259788714596470713)
                      ·
                        rfl

theorem cell23_2368339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 6, 2, 1, 4].length) (baseStart_2368339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2368339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2368339 prefixEnd_2368339 := by exact prefixLift 2368339
  have htrace : WordTrace (prefixWord ++ tailWord_2368339) baseStart_2368339 baseEnd_2368339 := by
    simpa [prefixWord, tailWord_2368339, baseEnd_2368339] using wordTrace_append hprefix tailTrace_2368339
  have hstable : (prefixWord ++ tailWord_2368339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368339).length < 2 ^ (prefixWord ++ tailWord_2368339).sum := by decide
  have hdescent : baseEnd_2368339 < baseStart_2368339 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368383 : List Nat := [1, 1, 2, 2, 1, 1, 7, 3, 1, 4]
def baseStart_2368383 : Nat := 118140960795 + 2368383 * 2 ^ 59
def prefixEnd_2368383 : Nat := 4983230072969 + 3 ^ 40 * 2368383 * 2
def baseEnd_2368383 : Nat := 405372950979170808106837

theorem tailTrace_2368383 : CollatzResearch.WordTrace tailWord_2368383 prefixEnd_2368383 405372950979170808106837 := by
  unfold tailWord_2368383
  simp only [CollatzResearch.WordTrace]
  refine ⟨86382024578760353458605803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57588016385840235639070535 86382024578760353458605803)
  ·
    refine ⟨129573036868140530187908705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86382024578760353458605803 129573036868140530187908705)
    ·
      refine ⟨97179777651105397640931529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129573036868140530187908705 97179777651105397640931529)
      ·
        refine ⟨72884833238329048230698647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97179777651105397640931529 72884833238329048230698647)
        ·
          refine ⟨109327249857493572346047971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72884833238329048230698647 109327249857493572346047971)
          ·
            refine ⟨163990874786240358519071957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109327249857493572346047971 163990874786240358519071957)
            ·
              refine ⟨3843536127802508402790749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 163990874786240358519071957 3843536127802508402790749)
              ·
                refine ⟨1441326047925940651046531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3843536127802508402790749 1441326047925940651046531)
                ·
                  refine ⟨2161989071888910976569797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1441326047925940651046531 2161989071888910976569797)
                  ·
                    refine ⟨405372950979170808106837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2161989071888910976569797 405372950979170808106837)
                    ·
                      rfl

theorem cell23_2368383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 3, 1, 4].length) (baseStart_2368383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2368383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2368383 prefixEnd_2368383 := by exact prefixLift 2368383
  have htrace : WordTrace (prefixWord ++ tailWord_2368383) baseStart_2368383 baseEnd_2368383 := by
    simpa [prefixWord, tailWord_2368383, baseEnd_2368383] using wordTrace_append hprefix tailTrace_2368383
  have hstable : (prefixWord ++ tailWord_2368383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368383).length < 2 ^ (prefixWord ++ tailWord_2368383).sum := by decide
  have hdescent : baseEnd_2368383 < baseStart_2368383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368409 : List Nat := [1, 2, 1, 2, 1, 3, 1, 4, 3, 5]
def baseStart_2368409 : Nat := 118140960795 + 2368409 * 2 ^ 59
def prefixEnd_2368409 : Nat := 4983230072969 + 3 ^ 40 * 2368409 * 2
def baseEnd_2368409 : Nat := 405377401144843107531797

theorem tailTrace_2368409 : CollatzResearch.WordTrace tailWord_2368409 prefixEnd_2368409 405377401144843107531797 := by
  unfold tailWord_2368409
  simp only [CollatzResearch.WordTrace]
  refine ⟨86382972876666159899052281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57588648584444106599368187 86382972876666159899052281)
  ·
    refine ⟨64787229657499619924289211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86382972876666159899052281 64787229657499619924289211)
    ·
      refine ⟨97180844486249429886433817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64787229657499619924289211 97180844486249429886433817)
      ·
        refine ⟨72885633364687072414825363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97180844486249429886433817 72885633364687072414825363)
        ·
          refine ⟨109328450047030608622238045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72885633364687072414825363 109328450047030608622238045)
          ·
            refine ⟨40998168767636478233339267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109328450047030608622238045 40998168767636478233339267)
            ·
              refine ⟨61497253151454717350008901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40998168767636478233339267 61497253151454717350008901)
              ·
                refine ⟨11530734965897759503126669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61497253151454717350008901 11530734965897759503126669)
                ·
                  refine ⟨4324025612211659813672501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11530734965897759503126669 4324025612211659813672501)
                  ·
                    refine ⟨405377401144843107531797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4324025612211659813672501 405377401144843107531797)
                    ·
                      rfl

theorem cell23_2368409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4, 3, 5].length) (baseStart_2368409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2368409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2368409 prefixEnd_2368409 := by exact prefixLift 2368409
  have htrace : WordTrace (prefixWord ++ tailWord_2368409) baseStart_2368409 baseEnd_2368409 := by
    simpa [prefixWord, tailWord_2368409, baseEnd_2368409] using wordTrace_append hprefix tailTrace_2368409
  have hstable : (prefixWord ++ tailWord_2368409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368409).length < 2 ^ (prefixWord ++ tailWord_2368409).sum := by decide
  have hdescent : baseEnd_2368409 < baseStart_2368409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368416 : List Nat := [2, 1, 1, 4, 1, 1, 2, 1, 3, 5, 2]
def baseStart_2368416 : Nat := 118140960795 + 2368416 * 2 ^ 59
def prefixEnd_2368416 : Nat := 4983230072969 + 3 ^ 40 * 2368416 * 2
def baseEnd_2368416 : Nat := 1216135797799110795207859

theorem tailTrace_2368416 : CollatzResearch.WordTrace tailWord_2368416 prefixEnd_2368416 1216135797799110795207859 := by
  unfold tailWord_2368416
  simp only [CollatzResearch.WordTrace]
  refine ⟨43191614093820400047278551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57588818791760533396371401 43191614093820400047278551)
  ·
    refine ⟨64787421140730600070917827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43191614093820400047278551 64787421140730600070917827)
    ·
      refine ⟨97181131711095900106376741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64787421140730600070917827 97181131711095900106376741)
      ·
        refine ⟨18221462195830481269945639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 97181131711095900106376741 18221462195830481269945639)
        ·
          refine ⟨27332193293745721904918459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18221462195830481269945639 27332193293745721904918459)
          ·
            refine ⟨40998289940618582857377689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27332193293745721904918459 40998289940618582857377689)
            ·
              refine ⟨30748717455463937143033267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40998289940618582857377689 30748717455463937143033267)
              ·
                refine ⟨46123076183195905714549901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30748717455463937143033267 46123076183195905714549901)
                ·
                  refine ⟨17296153568698464642956213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46123076183195905714549901 17296153568698464642956213)
                  ·
                    refine ⟨1621514397065481060277145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17296153568698464642956213 1621514397065481060277145)
                    ·
                      refine ⟨1216135797799110795207859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1621514397065481060277145 1216135797799110795207859)
                      ·
                        rfl

theorem cell23_2368416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 3, 5, 2].length) (baseStart_2368416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2368416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2368416 prefixEnd_2368416 := by exact prefixLift 2368416
  have htrace : WordTrace (prefixWord ++ tailWord_2368416) baseStart_2368416 baseEnd_2368416 := by
    simpa [prefixWord, tailWord_2368416, baseEnd_2368416] using wordTrace_append hprefix tailTrace_2368416
  have hstable : (prefixWord ++ tailWord_2368416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368416).length < 2 ^ (prefixWord ++ tailWord_2368416).sum := by decide
  have hdescent : baseEnd_2368416 < baseStart_2368416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368439 : List Nat := [1, 1, 3, 1, 3, 1, 3, 1, 3, 6]
def baseStart_2368439 : Nat := 118140960795 + 2368439 * 2 ^ 59
def prefixEnd_2368439 : Nat := 4983230072969 + 3 ^ 40 * 2368439 * 2
def baseEnd_2368439 : Nat := 405382535951388068406751

theorem tailTrace_2368439 : CollatzResearch.WordTrace tailWord_2368439 prefixEnd_2368439 405382535951388068406751 := by
  unfold tailWord_2368439
  simp only [CollatzResearch.WordTrace]
  refine ⟨86384067066557475022644371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57589378044371650015096247 86384067066557475022644371)
  ·
    refine ⟨129576100599836212533966557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86384067066557475022644371 129576100599836212533966557)
    ·
      refine ⟨48591037724938579700237459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129576100599836212533966557 48591037724938579700237459)
      ·
        refine ⟨72886556587407869550356189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48591037724938579700237459 72886556587407869550356189)
        ·
          refine ⟨27332458720277951081383571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72886556587407869550356189 27332458720277951081383571)
          ·
            refine ⟨40998688080416926622075357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27332458720277951081383571 40998688080416926622075357)
            ·
              refine ⟨15374508030156347483278259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40998688080416926622075357 15374508030156347483278259)
              ·
                refine ⟨23061762045234521224917389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15374508030156347483278259 23061762045234521224917389)
                ·
                  refine ⟨8648160766962945459344021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23061762045234521224917389 8648160766962945459344021)
                  ·
                    refine ⟨405382535951388068406751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8648160766962945459344021 405382535951388068406751)
                    ·
                      rfl

theorem cell23_2368439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 3, 6].length) (baseStart_2368439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2368439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2368439 prefixEnd_2368439 := by exact prefixLift 2368439
  have htrace : WordTrace (prefixWord ++ tailWord_2368439) baseStart_2368439 baseEnd_2368439 := by
    simpa [prefixWord, tailWord_2368439, baseEnd_2368439] using wordTrace_append hprefix tailTrace_2368439
  have hstable : (prefixWord ++ tailWord_2368439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368439).length < 2 ^ (prefixWord ++ tailWord_2368439).sum := by decide
  have hdescent : baseEnd_2368439 < baseStart_2368439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368473 : List Nat := [1, 2, 1, 2, 5, 1, 2, 3, 2, 4]
def baseStart_2368473 : Nat := 118140960795 + 2368473 * 2 ^ 59
def prefixEnd_2368473 : Nat := 4983230072969 + 3 ^ 40 * 2368473 * 2
def baseEnd_2368473 : Nat := 405388355398805690731699

theorem tailTrace_2368473 : CollatzResearch.WordTrace tailWord_2368473 prefixEnd_2368473 405388355398805690731699 := by
  unfold tailWord_2368473
  simp only [CollatzResearch.WordTrace]
  refine ⟨86385307148434298829382073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57590204765622865886254715 86385307148434298829382073)
  ·
    refine ⟨64788980361325724122036555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86385307148434298829382073 64788980361325724122036555)
    ·
      refine ⟨97183470541988586183054833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64788980361325724122036555 97183470541988586183054833)
      ·
        refine ⟨72887602906491439637291125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97183470541988586183054833 72887602906491439637291125)
        ·
          refine ⟨6833212772483572465996043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 72887602906491439637291125 6833212772483572465996043)
          ·
            refine ⟨10249819158725358698994065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6833212772483572465996043 10249819158725358698994065)
            ·
              refine ⟨7687364369044019024245549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10249819158725358698994065 7687364369044019024245549)
              ·
                refine ⟨2882761638391507134092081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7687364369044019024245549 2882761638391507134092081)
                ·
                  refine ⟨2162071228793630350569061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2882761638391507134092081 2162071228793630350569061)
                  ·
                    refine ⟨405388355398805690731699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2162071228793630350569061 405388355398805690731699)
                    ·
                      rfl

theorem cell23_2368473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 3, 2, 4].length) (baseStart_2368473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2368473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2368473 prefixEnd_2368473 := by exact prefixLift 2368473
  have htrace : WordTrace (prefixWord ++ tailWord_2368473) baseStart_2368473 baseEnd_2368473 := by
    simpa [prefixWord, tailWord_2368473, baseEnd_2368473] using wordTrace_append hprefix tailTrace_2368473
  have hstable : (prefixWord ++ tailWord_2368473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368473).length < 2 ^ (prefixWord ++ tailWord_2368473).sum := by decide
  have hdescent : baseEnd_2368473 < baseStart_2368473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368483 : List Nat := [1, 1, 1, 6, 1, 1, 2, 4, 1, 2, 3]
def baseStart_2368483 : Nat := 118140960795 + 2368483 * 2 ^ 59
def prefixEnd_2368483 : Nat := 4983230072969 + 3 ^ 40 * 2368483 * 2
def baseEnd_2368483 : Nat := 1216170201002962033070051

theorem tailTrace_2368483 : CollatzResearch.WordTrace tailWord_2368483 prefixEnd_2368483 1216170201002962033070051 := by
  unfold tailWord_2368483
  simp only [CollatzResearch.WordTrace]
  refine ⟨86385671878398070537246103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57590447918932047024830735 86385671878398070537246103)
  ·
    refine ⟨129578507817597105805869155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86385671878398070537246103 129578507817597105805869155)
    ·
      refine ⟨194367761726395658708803733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129578507817597105805869155 194367761726395658708803733)
      ·
        refine ⟨9110988830924796501975175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 194367761726395658708803733 9110988830924796501975175)
        ·
          refine ⟨13666483246387194752962763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9110988830924796501975175 13666483246387194752962763)
          ·
            refine ⟨20499724869580792129444145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13666483246387194752962763 20499724869580792129444145)
            ·
              refine ⟨15374793652185594097083109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20499724869580792129444145 15374793652185594097083109)
              ·
                refine ⟨2882773809784798893203083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15374793652185594097083109 2882773809784798893203083)
                ·
                  refine ⟨4324160714677198339804625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2882773809784798893203083 4324160714677198339804625)
                  ·
                    refine ⟨3243120536007898754853469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4324160714677198339804625 3243120536007898754853469)
                    ·
                      refine ⟨1216170201002962033070051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3243120536007898754853469 1216170201002962033070051)
                      ·
                        rfl

theorem cell23_2368483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_2368483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2368483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2368483 prefixEnd_2368483 := by exact prefixLift 2368483
  have htrace : WordTrace (prefixWord ++ tailWord_2368483) baseStart_2368483 baseEnd_2368483 := by
    simpa [prefixWord, tailWord_2368483, baseEnd_2368483] using wordTrace_append hprefix tailTrace_2368483
  have hstable : (prefixWord ++ tailWord_2368483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368483).length < 2 ^ (prefixWord ++ tailWord_2368483).sum := by decide
  have hdescent : baseEnd_2368483 < baseStart_2368483 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368497 : List Nat := [1, 2, 2, 2, 4, 1, 1, 5, 1, 2, 2]
def baseStart_2368497 : Nat := 118140960795 + 2368497 * 2 ^ 59
def prefixEnd_2368497 : Nat := 4983230072969 + 3 ^ 40 * 2368497 * 2
def baseEnd_2368497 : Nat := 1216177389732124978294987

theorem tailTrace_2368497 : CollatzResearch.WordTrace tailWord_2368497 prefixEnd_2368497 1216177389732124978294987 := by
  unfold tailWord_2368497
  simp only [CollatzResearch.WordTrace]
  refine ⟨86386182500347350928255745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57590788333564900618837163 86386182500347350928255745)
  ·
    refine ⟨64789636875260513196191809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86386182500347350928255745 64789636875260513196191809)
    ·
      refine ⟨48592227656445384897143857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64789636875260513196191809 48592227656445384897143857)
      ·
        refine ⟨36444170742334038672857893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48592227656445384897143857 36444170742334038672857893)
        ·
          refine ⟨6833282014187632251160855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36444170742334038672857893 6833282014187632251160855)
          ·
            refine ⟨10249923021281448376741283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6833282014187632251160855 10249923021281448376741283)
            ·
              refine ⟨15374884531922172565111925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10249923021281448376741283 15374884531922172565111925)
              ·
                refine ⟨1441395424867703677979243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15374884531922172565111925 1441395424867703677979243)
                ·
                  refine ⟨2162093137301555516968865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1441395424867703677979243 2162093137301555516968865)
                  ·
                    refine ⟨1621569852976166637726649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2162093137301555516968865 1621569852976166637726649)
                    ·
                      refine ⟨1216177389732124978294987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1621569852976166637726649 1216177389732124978294987)
                      ·
                        rfl

theorem cell23_2368497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 5, 1, 2, 2].length) (baseStart_2368497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2368497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2368497 prefixEnd_2368497 := by exact prefixLift 2368497
  have htrace : WordTrace (prefixWord ++ tailWord_2368497) baseStart_2368497 baseEnd_2368497 := by
    simpa [prefixWord, tailWord_2368497, baseEnd_2368497] using wordTrace_append hprefix tailTrace_2368497
  have hstable : (prefixWord ++ tailWord_2368497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368497).length < 2 ^ (prefixWord ++ tailWord_2368497).sum := by decide
  have hdescent : baseEnd_2368497 < baseStart_2368497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368556 : List Nat := [2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 5]
def baseStart_2368556 : Nat := 118140960795 + 2368556 * 2 ^ 59
def prefixEnd_2368556 : Nat := 4983230072969 + 3 ^ 40 * 2368556 * 2
def baseEnd_2368556 : Nat := 1216207685090740247457215

theorem tailTrace_2368556 : CollatzResearch.WordTrace tailWord_2368556 prefixEnd_2368556 1216207685090740247457215 := by
  unfold tailWord_2368556
  simp only [CollatzResearch.WordTrace]
  refine ⟨43194167203566802002326761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57592222938089069336435681 43194167203566802002326761)
  ·
    refine ⟨32395625402675101501745071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43194167203566802002326761 32395625402675101501745071)
    ·
      refine ⟨48593438104012652252617607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32395625402675101501745071 48593438104012652252617607)
      ·
        refine ⟨72890157156018978378926411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48593438104012652252617607 72890157156018978378926411)
        ·
          refine ⟨109335235734028467568389617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72890157156018978378926411 109335235734028467568389617)
          ·
            refine ⟨82001426800521350676292213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109335235734028467568389617 82001426800521350676292213)
            ·
              refine ⟨7687633762548876625902395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 82001426800521350676292213 7687633762548876625902395)
              ·
                refine ⟨11531450643823314938853593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7687633762548876625902395 11531450643823314938853593)
                ·
                  refine ⟨8648587982867486204140195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11531450643823314938853593 8648587982867486204140195)
                  ·
                    refine ⟨12972881974301229306210293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8648587982867486204140195 12972881974301229306210293)
                    ·
                      refine ⟨1216207685090740247457215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12972881974301229306210293 1216207685090740247457215)
                      ·
                        rfl

theorem cell23_2368556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 5].length) (baseStart_2368556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2368556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2368556 prefixEnd_2368556 := by exact prefixLift 2368556
  have htrace : WordTrace (prefixWord ++ tailWord_2368556) baseStart_2368556 baseEnd_2368556 := by
    simpa [prefixWord, tailWord_2368556, baseEnd_2368556] using wordTrace_append hprefix tailTrace_2368556
  have hstable : (prefixWord ++ tailWord_2368556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368556).length < 2 ^ (prefixWord ++ tailWord_2368556).sum := by decide
  have hdescent : baseEnd_2368556 < baseStart_2368556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368570 : List Nat := [3, 1, 1, 1, 3, 1, 4, 1, 4, 2, 2]
def baseStart_2368570 : Nat := 118140960795 + 2368570 * 2 ^ 59
def prefixEnd_2368570 : Nat := 4983230072969 + 3 ^ 40 * 2368570 * 2
def baseEnd_2368570 : Nat := 1216214873819903192682151

theorem tailTrace_2368570 : CollatzResearch.WordTrace tailWord_2368570 prefixEnd_2368570 1216214873819903192682151 := by
  unfold tailWord_2368570
  simp only [CollatzResearch.WordTrace]
  refine ⟨21597211257270721098915791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57592563352721922930442109 21597211257270721098915791)
  ·
    refine ⟨32395816885906081648373687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21597211257270721098915791 32395816885906081648373687)
    ·
      refine ⟨48593725328859122472560531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32395816885906081648373687 48593725328859122472560531)
      ·
        refine ⟨72890587993288683708840797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48593725328859122472560531 72890587993288683708840797)
        ·
          refine ⟨27333970497483256390815299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72890587993288683708840797 27333970497483256390815299)
          ·
            refine ⟨41000955746224884586222949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27333970497483256390815299 41000955746224884586222949)
            ·
              refine ⟨7687679202417165859916803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41000955746224884586222949 7687679202417165859916803)
              ·
                refine ⟨11531518803625748789875205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7687679202417165859916803 11531518803625748789875205)
                ·
                  refine ⟨2162159775679827898101601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11531518803625748789875205 2162159775679827898101601)
                  ·
                    refine ⟨1621619831759870923576201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2162159775679827898101601 1621619831759870923576201)
                    ·
                      refine ⟨1216214873819903192682151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1621619831759870923576201 1216214873819903192682151)
                      ·
                        rfl

theorem cell23_2368570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 1, 4, 2, 2].length) (baseStart_2368570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2368570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2368570 prefixEnd_2368570 := by exact prefixLift 2368570
  have htrace : WordTrace (prefixWord ++ tailWord_2368570) baseStart_2368570 baseEnd_2368570 := by
    simpa [prefixWord, tailWord_2368570, baseEnd_2368570] using wordTrace_append hprefix tailTrace_2368570
  have hstable : (prefixWord ++ tailWord_2368570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368570).length < 2 ^ (prefixWord ++ tailWord_2368570).sum := by decide
  have hdescent : baseEnd_2368570 < baseStart_2368570 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368630 : List Nat := [5, 1, 1, 2, 1, 1, 1, 1, 1, 7, 2]
def baseStart_2368630 : Nat := 118140960795 + 2368630 * 2 ^ 59
def prefixEnd_2368630 : Nat := 4983230072969 + 3 ^ 40 * 2368630 * 2
def baseEnd_2368630 : Nat := 1216245682659172957931875

theorem tailTrace_2368630 : CollatzResearch.WordTrace tailWord_2368630 prefixEnd_2368630 1216245682659172957931875 := by
  unfold tailWord_2368630
  simp only [CollatzResearch.WordTrace]
  refine ⟨5399439588054094665177959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57594022272577009761898229 5399439588054094665177959)
  ·
    refine ⟨8099159382081141997766939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5399439588054094665177959 8099159382081141997766939)
    ·
      refine ⟨12148739073121712996650409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8099159382081141997766939 12148739073121712996650409)
      ·
        refine ⟨9111554304841284747487807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12148739073121712996650409 9111554304841284747487807)
        ·
          refine ⟨13667331457261927121231711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9111554304841284747487807 13667331457261927121231711)
          ·
            refine ⟨20500997185892890681847567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13667331457261927121231711 20500997185892890681847567)
            ·
              refine ⟨30751495778839336022771351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20500997185892890681847567 30751495778839336022771351)
              ·
                refine ⟨46127243668259004034157027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30751495778839336022771351 46127243668259004034157027)
                ·
                  refine ⟨69190865502388506051235541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46127243668259004034157027 69190865502388506051235541)
                  ·
                    refine ⟨1621660910212230610575833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 69190865502388506051235541 1621660910212230610575833)
                    ·
                      refine ⟨1216245682659172957931875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1621660910212230610575833 1216245682659172957931875)
                      ·
                        rfl

theorem cell23_2368630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 1, 7, 2].length) (baseStart_2368630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2368630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2368630 prefixEnd_2368630 := by exact prefixLift 2368630
  have htrace : WordTrace (prefixWord ++ tailWord_2368630) baseStart_2368630 baseEnd_2368630 := by
    simpa [prefixWord, tailWord_2368630, baseEnd_2368630] using wordTrace_append hprefix tailTrace_2368630
  have hstable : (prefixWord ++ tailWord_2368630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368630).length < 2 ^ (prefixWord ++ tailWord_2368630).sum := by decide
  have hdescent : baseEnd_2368630 < baseStart_2368630 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368656 : List Nat := [2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 4]
def baseStart_2368656 : Nat := 118140960795 + 2368656 * 2 ^ 59
def prefixEnd_2368656 : Nat := 4983230072969 + 3 ^ 40 * 2368656 * 2
def baseEnd_2368656 : Nat := 1216259033156189856206755

theorem tailTrace_2368656 : CollatzResearch.WordTrace tailWord_2368656 prefixEnd_2368656 1216259033156189856206755 := by
  unfold tailWord_2368656
  simp only [CollatzResearch.WordTrace]
  refine ⟨43195990853385660541646911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57594654471180880722195881 43195990853385660541646911)
  ·
    refine ⟨64793986280078490812470367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43195990853385660541646911 64793986280078490812470367)
    ·
      refine ⟨97190979420117736218705551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64793986280078490812470367 97190979420117736218705551)
      ·
        refine ⟨145786469130176604328058327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97190979420117736218705551 145786469130176604328058327)
        ·
          refine ⟨218679703695264906492087491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145786469130176604328058327 218679703695264906492087491)
          ·
            refine ⟨328019555542897359738131237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 218679703695264906492087491 328019555542897359738131237)
            ·
              refine ⟨61503666664293254950899607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 328019555542897359738131237 61503666664293254950899607)
              ·
                refine ⟨92255499996439882426349411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61503666664293254950899607 92255499996439882426349411)
                ·
                  refine ⟨138383249994659823639524117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 92255499996439882426349411 138383249994659823639524117)
                  ·
                    refine ⟨6486714843499679233102693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 138383249994659823639524117 6486714843499679233102693)
                    ·
                      refine ⟨1216259033156189856206755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6486714843499679233102693 1216259033156189856206755)
                      ·
                        rfl

theorem cell23_2368656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 4].length) (baseStart_2368656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2368656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2368656 prefixEnd_2368656 := by exact prefixLift 2368656
  have htrace : WordTrace (prefixWord ++ tailWord_2368656) baseStart_2368656 baseEnd_2368656 := by
    simpa [prefixWord, tailWord_2368656, baseEnd_2368656] using wordTrace_append hprefix tailTrace_2368656
  have hstable : (prefixWord ++ tailWord_2368656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368656).length < 2 ^ (prefixWord ++ tailWord_2368656).sum := by decide
  have hdescent : baseEnd_2368656 < baseStart_2368656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368696 : List Nat := [2, 1, 2, 1, 2, 1, 2, 1, 2, 9]
def baseStart_2368696 : Nat := 118140960795 + 2368696 * 2 ^ 59
def prefixEnd_2368696 : Nat := 4983230072969 + 3 ^ 40 * 2368696 * 2
def baseEnd_2368696 : Nat := 405426524127456566568857

theorem tailTrace_2368696 : CollatzResearch.WordTrace tailWord_2368696 prefixEnd_2368696 405426524127456566568857 := by
  unfold tailWord_2368696
  simp only [CollatzResearch.WordTrace]
  refine ⟨43196720313313203957374971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57595627084417605276499961 43196720313313203957374971)
  ·
    refine ⟨64795080469969805936062457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43196720313313203957374971 64795080469969805936062457)
    ·
      refine ⟨48596310352477354452046843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64795080469969805936062457 48596310352477354452046843)
      ·
        refine ⟨72894465528716031678070265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48596310352477354452046843 72894465528716031678070265)
        ·
          refine ⟨54670849146537023758552699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72894465528716031678070265 54670849146537023758552699)
          ·
            refine ⟨82006273719805535637829049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54670849146537023758552699 82006273719805535637829049)
            ·
              refine ⟨61504705289854151728371787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82006273719805535637829049 61504705289854151728371787)
              ·
                refine ⟨92257057934781227592557681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61504705289854151728371787 92257057934781227592557681)
                ·
                  refine ⟨69192793451085920694418261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 92257057934781227592557681 69192793451085920694418261)
                  ·
                    refine ⟨405426524127456566568857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 69192793451085920694418261 405426524127456566568857)
                    ·
                      rfl

theorem cell23_2368696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 9].length) (baseStart_2368696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2368696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2368696 prefixEnd_2368696 := by exact prefixLift 2368696
  have htrace : WordTrace (prefixWord ++ tailWord_2368696) baseStart_2368696 baseEnd_2368696 := by
    simpa [prefixWord, tailWord_2368696, baseEnd_2368696] using wordTrace_append hprefix tailTrace_2368696
  have hstable : (prefixWord ++ tailWord_2368696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368696).length < 2 ^ (prefixWord ++ tailWord_2368696).sum := by decide
  have hdescent : baseEnd_2368696 < baseStart_2368696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368737 : List Nat := [1, 2, 3, 1, 3, 3, 1, 2, 2, 3, 2]
def baseStart_2368737 : Nat := 118140960795 + 2368737 * 2 ^ 59
def prefixEnd_2368737 : Nat := 4983230072969 + 3 ^ 40 * 2368737 * 2
def baseEnd_2368737 : Nat := 1216300625089204039293883

theorem tailTrace_2368737 : CollatzResearch.WordTrace tailWord_2368737 prefixEnd_2368737 1216300625089204039293883 := by
  unfold tailWord_2368737
  simp only [CollatzResearch.WordTrace]
  refine ⟨86394936019477871916992465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57596624012985247944661643 86394936019477871916992465)
  ·
    refine ⟨64796202014608403937744349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86394936019477871916992465 64796202014608403937744349)
    ·
      refine ⟨24298575755478151476654131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64796202014608403937744349 24298575755478151476654131)
      ·
        refine ⟨36447863633217227214981197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24298575755478151476654131 36447863633217227214981197)
        ·
          refine ⟨13667948862456460205617949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36447863633217227214981197 13667948862456460205617949)
          ·
            refine ⟨5125480823421172577106731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13667948862456460205617949 5125480823421172577106731)
            ·
              refine ⟨7688221235131758865660097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5125480823421172577106731 7688221235131758865660097)
              ·
                refine ⟨5766165926348819149245073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7688221235131758865660097 5766165926348819149245073)
                ·
                  refine ⟨4324624444761614361933805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5766165926348819149245073 4324624444761614361933805)
                  ·
                    refine ⟨1621734166785605385725177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4324624444761614361933805 1621734166785605385725177)
                    ·
                      refine ⟨1216300625089204039293883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1621734166785605385725177 1216300625089204039293883)
                      ·
                        rfl

theorem cell23_2368737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 2, 2, 3, 2].length) (baseStart_2368737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2368737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2368737 prefixEnd_2368737 := by exact prefixLift 2368737
  have htrace : WordTrace (prefixWord ++ tailWord_2368737) baseStart_2368737 baseEnd_2368737 := by
    simpa [prefixWord, tailWord_2368737, baseEnd_2368737] using wordTrace_append hprefix tailTrace_2368737
  have hstable : (prefixWord ++ tailWord_2368737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368737).length < 2 ^ (prefixWord ++ tailWord_2368737).sum := by decide
  have hdescent : baseEnd_2368737 < baseStart_2368737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368753 : List Nat := [1, 2, 2, 2, 2, 1, 1, 1, 2, 6, 3]
def baseStart_2368753 : Nat := 118140960795 + 2368753 * 2 ^ 59
def prefixEnd_2368753 : Nat := 4983230072969 + 3 ^ 40 * 2368753 * 2
def baseEnd_2368753 : Nat := 1216308840779675976693809

theorem tailTrace_2368753 : CollatzResearch.WordTrace tailWord_2368753 prefixEnd_2368753 1216308840779675976693809 := by
  unfold tailWord_2368753
  simp only [CollatzResearch.WordTrace]
  refine ⟨86395519587419906649574913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57597013058279937766383275 86395519587419906649574913)
  ·
    refine ⟨64796639690564929987181185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86395519587419906649574913 64796639690564929987181185)
    ·
      refine ⟨48597479767923697490385889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64796639690564929987181185 48597479767923697490385889)
      ·
        refine ⟨36448109825942773117789417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48597479767923697490385889 36448109825942773117789417)
        ·
          refine ⟨27336082369457079838342063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36448109825942773117789417 27336082369457079838342063)
          ·
            refine ⟨41004123554185619757513095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27336082369457079838342063 41004123554185619757513095)
            ·
              refine ⟨61506185331278429636269643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41004123554185619757513095 61506185331278429636269643)
              ·
                refine ⟨92259277996917644454404465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61506185331278429636269643 92259277996917644454404465)
                ·
                  refine ⟨69194458497688233340803349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 92259277996917644454404465 69194458497688233340803349)
                  ·
                    refine ⟨3243490242079135937850157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 69194458497688233340803349 3243490242079135937850157)
                    ·
                      refine ⟨1216308840779675976693809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3243490242079135937850157 1216308840779675976693809)
                      ·
                        rfl

theorem cell23_2368753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 6, 3].length) (baseStart_2368753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2368753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2368753 prefixEnd_2368753 := by exact prefixLift 2368753
  have htrace : WordTrace (prefixWord ++ tailWord_2368753) baseStart_2368753 baseEnd_2368753 := by
    simpa [prefixWord, tailWord_2368753, baseEnd_2368753] using wordTrace_append hprefix tailTrace_2368753
  have hstable : (prefixWord ++ tailWord_2368753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368753).length < 2 ^ (prefixWord ++ tailWord_2368753).sum := by decide
  have hdescent : baseEnd_2368753 < baseStart_2368753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368764 : List Nat := [2, 2, 2, 1, 6, 1, 1, 2, 1, 5]
def baseStart_2368764 : Nat := 118140960795 + 2368764 * 2 ^ 59
def prefixEnd_2368764 : Nat := 4983230072969 + 3 ^ 40 * 2368764 * 2
def baseEnd_2368764 : Nat := 405438163022291811218753

theorem tailTrace_2368764 : CollatzResearch.WordTrace tailWord_2368764 prefixEnd_2368764 405438163022291811218753 := by
  unfold tailWord_2368764
  simp only [CollatzResearch.WordTrace]
  refine ⟨43197960395190027764112673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57597280526920037018816897 43197960395190027764112673)
  ·
    refine ⟨32398470296392520823084505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43197960395190027764112673 32398470296392520823084505)
    ·
      refine ⟨24298852722294390617313379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32398470296392520823084505 24298852722294390617313379)
      ·
        refine ⟨36448279083441585925970069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24298852722294390617313379 36448279083441585925970069)
        ·
          refine ⟨1708513082036324340279847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 36448279083441585925970069 1708513082036324340279847)
          ·
            refine ⟨2562769623054486510419771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1708513082036324340279847 2562769623054486510419771)
            ·
              refine ⟨3844154434581729765629657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2562769623054486510419771 3844154434581729765629657)
              ·
                refine ⟨2883115825936297324222243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3844154434581729765629657 2883115825936297324222243)
                ·
                  refine ⟨4324673738904445986333365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2883115825936297324222243 4324673738904445986333365)
                  ·
                    refine ⟨405438163022291811218753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4324673738904445986333365 405438163022291811218753)
                    ·
                      rfl

theorem cell23_2368764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 2, 1, 5].length) (baseStart_2368764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2368764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2368764 prefixEnd_2368764 := by exact prefixLift 2368764
  have htrace : WordTrace (prefixWord ++ tailWord_2368764) baseStart_2368764 baseEnd_2368764 := by
    simpa [prefixWord, tailWord_2368764, baseEnd_2368764] using wordTrace_append hprefix tailTrace_2368764
  have hstable : (prefixWord ++ tailWord_2368764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368764).length < 2 ^ (prefixWord ++ tailWord_2368764).sum := by decide
  have hdescent : baseEnd_2368764 < baseStart_2368764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368767 : List Nat := [1, 1, 2, 2, 1, 7, 1, 2, 1, 1, 4]
def baseStart_2368767 : Nat := 118140960795 + 2368767 * 2 ^ 59
def prefixEnd_2368767 : Nat := 4983230072969 + 3 ^ 40 * 2368767 * 2
def baseEnd_2368767 : Nat := 1216316029508838921918745

theorem tailTrace_2368767 : CollatzResearch.WordTrace tailWord_2368767 prefixEnd_2368767 1216316029508838921918745 := by
  unfold tailWord_2368767
  simp only [CollatzResearch.WordTrace]
  refine ⟨86396030209369187040584555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57597353472912791360389703 86396030209369187040584555)
  ·
    refine ⟨129594045314053780560876833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86396030209369187040584555 129594045314053780560876833)
    ·
      refine ⟨97195533985540335420657625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129594045314053780560876833 97195533985540335420657625)
      ·
        refine ⟨72896650489155251565493219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97195533985540335420657625 72896650489155251565493219)
        ·
          refine ⟨109344975733732877348239829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72896650489155251565493219 109344975733732877348239829)
          ·
            refine ⟨2562772868759364312849371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 109344975733732877348239829 2562772868759364312849371)
            ·
              refine ⟨3844159303139046469274057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2562772868759364312849371 3844159303139046469274057)
              ·
                refine ⟨2883119477354284851955543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3844159303139046469274057 2883119477354284851955543)
                ·
                  refine ⟨4324679216031427277933315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2883119477354284851955543 4324679216031427277933315)
                  ·
                    refine ⟨6487018824047140916899973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4324679216031427277933315 6487018824047140916899973)
                    ·
                      refine ⟨1216316029508838921918745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6487018824047140916899973 1216316029508838921918745)
                      ·
                        rfl

theorem cell23_2368767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 2, 1, 1, 4].length) (baseStart_2368767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2368767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2368767 prefixEnd_2368767 := by exact prefixLift 2368767
  have htrace : WordTrace (prefixWord ++ tailWord_2368767) baseStart_2368767 baseEnd_2368767 := by
    simpa [prefixWord, tailWord_2368767, baseEnd_2368767] using wordTrace_append hprefix tailTrace_2368767
  have hstable : (prefixWord ++ tailWord_2368767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368767).length < 2 ^ (prefixWord ++ tailWord_2368767).sum := by decide
  have hdescent : baseEnd_2368767 < baseStart_2368767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368780 : List Nat := [2, 2, 1, 2, 2, 4, 1, 2, 1, 2, 4]
def baseStart_2368780 : Nat := 118140960795 + 2368780 * 2 ^ 59
def prefixEnd_2368780 : Nat := 4983230072969 + 3 ^ 40 * 2368780 * 2
def baseEnd_2368780 : Nat := 1216322704757347371056185

theorem tailTrace_2368780 : CollatzResearch.WordTrace tailWord_2368780 prefixEnd_2368780 1216322704757347371056185 := by
  unfold tailWord_2368780
  simp only [CollatzResearch.WordTrace]
  refine ⟨43198252179161045130403897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57597669572214726840538529 43198252179161045130403897)
  ·
    refine ⟨32398689134370783847802923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43198252179161045130403897 32398689134370783847802923)
    ·
      refine ⟨48598033701556175771704385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32398689134370783847802923 48598033701556175771704385)
      ·
        refine ⟨36448525276167131828778289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48598033701556175771704385 36448525276167131828778289)
        ·
          refine ⟨27336393957125348871583717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36448525276167131828778289 27336393957125348871583717)
          ·
            refine ⟨5125573866961002913421947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27336393957125348871583717 5125573866961002913421947)
            ·
              refine ⟨7688360800441504370132921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5125573866961002913421947 7688360800441504370132921)
              ·
                refine ⟨5766270600331128277599691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7688360800441504370132921 5766270600331128277599691)
                ·
                  refine ⟨8649405900496692416399537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5766270600331128277599691 8649405900496692416399537)
                  ·
                    refine ⟨6487054425372519312299653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8649405900496692416399537 6487054425372519312299653)
                    ·
                      refine ⟨1216322704757347371056185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6487054425372519312299653 1216322704757347371056185)
                      ·
                        rfl

theorem cell23_2368780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 2, 1, 2, 4].length) (baseStart_2368780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2368780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2368780 prefixEnd_2368780 := by exact prefixLift 2368780
  have htrace : WordTrace (prefixWord ++ tailWord_2368780) baseStart_2368780 baseEnd_2368780 := by
    simpa [prefixWord, tailWord_2368780, baseEnd_2368780] using wordTrace_append hprefix tailTrace_2368780
  have hstable : (prefixWord ++ tailWord_2368780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368780).length < 2 ^ (prefixWord ++ tailWord_2368780).sum := by decide
  have hdescent : baseEnd_2368780 < baseStart_2368780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368803 : List Nat := [1, 1, 1, 4, 2, 3, 1, 1, 2, 7]
def baseStart_2368803 : Nat := 118140960795 + 2368803 * 2 ^ 59
def prefixEnd_2368803 : Nat := 4983230072969 + 3 ^ 40 * 2368803 * 2
def baseEnd_2368803 : Nat := 405444838270800260356193

theorem tailTrace_2368803 : CollatzResearch.WordTrace tailWord_2368803 prefixEnd_2368803 405444838270800260356193 := by
  unfold tailWord_2368803
  simp only [CollatzResearch.WordTrace]
  refine ⟨86397343237238765188895063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57598228824825843459263375 86397343237238765188895063)
  ·
    refine ⟨129596014855858147783342595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86397343237238765188895063 129596014855858147783342595)
    ·
      refine ⟨194394022283787221675013893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129596014855858147783342595 194394022283787221675013893)
      ·
        refine ⟨36448879178210104064065105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 194394022283787221675013893 36448879178210104064065105)
        ·
          refine ⟨27336659383657578048048829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36448879178210104064065105 27336659383657578048048829)
          ·
            refine ⟨10251247268871591768018311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27336659383657578048048829 10251247268871591768018311)
            ·
              refine ⟨15376870903307387652027467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10251247268871591768018311 15376870903307387652027467)
              ·
                refine ⟨23065306354961081478041201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15376870903307387652027467 23065306354961081478041201)
                ·
                  refine ⟨17298979766220811108530901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23065306354961081478041201 17298979766220811108530901)
                  ·
                    refine ⟨405444838270800260356193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17298979766220811108530901 405444838270800260356193)
                    ·
                      rfl

theorem cell23_2368803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 2, 7].length) (baseStart_2368803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2368803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2368803 prefixEnd_2368803 := by exact prefixLift 2368803
  have htrace : WordTrace (prefixWord ++ tailWord_2368803) baseStart_2368803 baseEnd_2368803 := by
    simpa [prefixWord, tailWord_2368803, baseEnd_2368803] using wordTrace_append hprefix tailTrace_2368803
  have hstable : (prefixWord ++ tailWord_2368803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368803).length < 2 ^ (prefixWord ++ tailWord_2368803).sum := by decide
  have hdescent : baseEnd_2368803 < baseStart_2368803 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368817 : List Nat := [1, 2, 2, 3, 3, 2, 2, 1, 1, 3, 3]
def baseStart_2368817 : Nat := 118140960795 + 2368817 * 2 ^ 59
def prefixEnd_2368817 : Nat := 4983230072969 + 3 ^ 40 * 2368817 * 2
def baseEnd_2368817 : Nat := 1216341703541563726293515

theorem tailTrace_2368817 : CollatzResearch.WordTrace tailWord_2368817 prefixEnd_2368817 1216341703541563726293515 := by
  unfold tailWord_2368817
  simp only [CollatzResearch.WordTrace]
  refine ⟨86397853859188045579904705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57598569239458697053269803 86397853859188045579904705)
  ·
    refine ⟨64798390394391034184928529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86397853859188045579904705 64798390394391034184928529)
    ·
      refine ⟨48598792795793275638696397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64798390394391034184928529 48598792795793275638696397)
      ·
        refine ⟨18224547298422478364511149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48598792795793275638696397 18224547298422478364511149)
        ·
          refine ⟨6834205236908429386691681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18224547298422478364511149 6834205236908429386691681)
          ·
            refine ⟨5125653927681322040018761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6834205236908429386691681 5125653927681322040018761)
            ·
              refine ⟨3844240445760991530014071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5125653927681322040018761 3844240445760991530014071)
              ·
                refine ⟨5766360668641487295021107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3844240445760991530014071 5766360668641487295021107)
                ·
                  refine ⟨8649541002962230942531661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5766360668641487295021107 8649541002962230942531661)
                  ·
                    refine ⟨3243577876110836603449373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8649541002962230942531661 3243577876110836603449373)
                    ·
                      refine ⟨1216341703541563726293515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3243577876110836603449373 1216341703541563726293515)
                      ·
                        rfl

theorem cell23_2368817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 1, 1, 3, 3].length) (baseStart_2368817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2368817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2368817 prefixEnd_2368817 := by exact prefixLift 2368817
  have htrace : WordTrace (prefixWord ++ tailWord_2368817) baseStart_2368817 baseEnd_2368817 := by
    simpa [prefixWord, tailWord_2368817, baseEnd_2368817] using wordTrace_append hprefix tailTrace_2368817
  have hstable : (prefixWord ++ tailWord_2368817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368817).length < 2 ^ (prefixWord ++ tailWord_2368817).sum := by decide
  have hdescent : baseEnd_2368817 < baseStart_2368817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368820 : List Nat := [2, 5, 1, 1, 1, 1, 1, 2, 2, 7]
def baseStart_2368820 : Nat := 118140960795 + 2368820 * 2 ^ 59
def prefixEnd_2368820 : Nat := 4983230072969 + 3 ^ 40 * 2368820 * 2
def baseEnd_2368820 : Nat := 405447747994509071518667

theorem tailTrace_2368820 : CollatzResearch.WordTrace tailWord_2368820 prefixEnd_2368820 405447747994509071518667 := by
  unfold tailWord_2368820
  simp only [CollatzResearch.WordTrace]
  refine ⟨43198981639088588546131957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57598642185451451394842609 43198981639088588546131957)
  ·
    refine ⟨4049904528664555176199871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43198981639088588546131957 4049904528664555176199871)
    ·
      refine ⟨6074856792996832764299807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4049904528664555176199871 6074856792996832764299807)
      ·
        refine ⟨9112285189495249146449711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6074856792996832764299807 9112285189495249146449711)
        ·
          refine ⟨13668427784242873719674567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9112285189495249146449711 13668427784242873719674567)
          ·
            refine ⟨20502641676364310579511851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13668427784242873719674567 20502641676364310579511851)
            ·
              refine ⟨30753962514546465869267777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20502641676364310579511851 30753962514546465869267777)
              ·
                refine ⟨23065471885909849401950833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30753962514546465869267777 23065471885909849401950833)
                ·
                  refine ⟨17299103914432387051463125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23065471885909849401950833 17299103914432387051463125)
                  ·
                    refine ⟨405447747994509071518667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17299103914432387051463125 405447747994509071518667)
                    ·
                      rfl

theorem cell23_2368820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_2368820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2368820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2368820 prefixEnd_2368820 := by exact prefixLift 2368820
  have htrace : WordTrace (prefixWord ++ tailWord_2368820) baseStart_2368820 baseEnd_2368820 := by
    simpa [prefixWord, tailWord_2368820, baseEnd_2368820] using wordTrace_append hprefix tailTrace_2368820
  have hstable : (prefixWord ++ tailWord_2368820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368820).length < 2 ^ (prefixWord ++ tailWord_2368820).sum := by decide
  have hdescent : baseEnd_2368820 < baseStart_2368820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368830 : List Nat := [4, 2, 1, 2, 1, 1, 2, 1, 2, 2, 5]
def baseStart_2368830 : Nat := 118140960795 + 2368830 * 2 ^ 59
def prefixEnd_2368830 : Nat := 4983230072969 + 3 ^ 40 * 2368830 * 2
def baseEnd_2368830 : Nat := 1216348378790072175430955

theorem tailTrace_2368830 : CollatzResearch.WordTrace tailWord_2368830 prefixEnd_2368830 1216348378790072175430955 := by
  unfold tailWord_2368830
  simp only [CollatzResearch.WordTrace]
  refine ⟨10799791001017618600015993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57598885338760632533418629 10799791001017618600015993)
  ·
    refine ⟨8099843250763213950011995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10799791001017618600015993 8099843250763213950011995)
    ·
      refine ⟨12149764876144820925017993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8099843250763213950011995 12149764876144820925017993)
      ·
        refine ⟨9112323657108615693763495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12149764876144820925017993 9112323657108615693763495)
        ·
          refine ⟨13668485485662923540645243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9112323657108615693763495 13668485485662923540645243)
          ·
            refine ⟨20502728228494385310967865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13668485485662923540645243 20502728228494385310967865)
            ·
              refine ⟨15377046171370788983225899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20502728228494385310967865 15377046171370788983225899)
              ·
                refine ⟨23065569257056183474838849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15377046171370788983225899 23065569257056183474838849)
                ·
                  refine ⟨17299176942792137606129137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23065569257056183474838849 17299176942792137606129137)
                  ·
                    refine ⟨12974382707094103204596853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17299176942792137606129137 12974382707094103204596853)
                    ·
                      refine ⟨1216348378790072175430955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12974382707094103204596853 1216348378790072175430955)
                      ·
                        rfl

theorem cell23_2368830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_2368830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2368830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2368830 prefixEnd_2368830 := by exact prefixLift 2368830
  have htrace : WordTrace (prefixWord ++ tailWord_2368830) baseStart_2368830 baseEnd_2368830 := by
    simpa [prefixWord, tailWord_2368830, baseEnd_2368830] using wordTrace_append hprefix tailTrace_2368830
  have hstable : (prefixWord ++ tailWord_2368830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368830).length < 2 ^ (prefixWord ++ tailWord_2368830).sum := by decide
  have hdescent : baseEnd_2368830 < baseStart_2368830 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368838 : List Nat := [6, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3]
def baseStart_2368838 : Nat := 118140960795 + 2368838 * 2 ^ 59
def prefixEnd_2368838 : Nat := 4983230072969 + 3 ^ 40 * 2368838 * 2
def baseEnd_2368838 : Nat := 1216352486635308144130919

theorem tailTrace_2368838 : CollatzResearch.WordTrace tailWord_2368838 prefixEnd_2368838 1216352486635308144130919 := by
  unfold tailWord_2368838
  simp only [CollatzResearch.WordTrace]
  refine ⟨2699956868503498942700599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 57599079861407977444279445 2699956868503498942700599)
  ·
    refine ⟨4049935302755248414050899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2699956868503498942700599 4049935302755248414050899)
    ·
      refine ⟨6074902954132872621076349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4049935302755248414050899 6074902954132872621076349)
      ·
        refine ⟨2278088607799827232903631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6074902954132872621076349 2278088607799827232903631)
        ·
          refine ⟨3417132911699740849355447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2278088607799827232903631 3417132911699740849355447)
          ·
            refine ⟨5125699367549611274033171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3417132911699740849355447 5125699367549611274033171)
            ·
              refine ⟨7688549051324416911049757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5125699367549611274033171 7688549051324416911049757)
              ·
                refine ⟨2883205894246656341643659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7688549051324416911049757 2883205894246656341643659)
                ·
                  refine ⟨4324808841369984512465489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2883205894246656341643659 4324808841369984512465489)
                  ·
                    refine ⟨3243606631027488384349117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4324808841369984512465489 3243606631027488384349117)
                    ·
                      refine ⟨1216352486635308144130919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3243606631027488384349117 1216352486635308144130919)
                      ·
                        rfl

theorem cell23_2368838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_2368838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2368838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2368838 prefixEnd_2368838 := by exact prefixLift 2368838
  have htrace : WordTrace (prefixWord ++ tailWord_2368838) baseStart_2368838 baseEnd_2368838 := by
    simpa [prefixWord, tailWord_2368838, baseEnd_2368838] using wordTrace_append hprefix tailTrace_2368838
  have hstable : (prefixWord ++ tailWord_2368838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368838).length < 2 ^ (prefixWord ++ tailWord_2368838).sum := by decide
  have hdescent : baseEnd_2368838 < baseStart_2368838 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368843 : List Nat := [1, 1, 1, 1, 3, 1, 1, 2, 6, 1, 5]
def baseStart_2368843 : Nat := 118140960795 + 2368843 * 2 ^ 59
def prefixEnd_2368843 : Nat := 4983230072969 + 3 ^ 40 * 2368843 * 2
def baseEnd_2368843 : Nat := 1216355054038580624568395

theorem tailTrace_2368843 : CollatzResearch.WordTrace tailWord_2368843 prefixEnd_2368843 1216355054038580624568395 := by
  unfold tailWord_2368843
  simp only [CollatzResearch.WordTrace]
  refine ⟨86398802157093852020351183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57599201438062568013567455 86398802157093852020351183)
  ·
    refine ⟨129598203235640778030526775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86398802157093852020351183 129598203235640778030526775)
    ·
      refine ⟨194397304853461167045790163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129598203235640778030526775 194397304853461167045790163)
      ·
        refine ⟨291595957280191750568685245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194397304853461167045790163 291595957280191750568685245)
        ·
          refine ⟨109348483980071906463256967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 291595957280191750568685245 109348483980071906463256967)
          ·
            refine ⟨164022725970107859694885451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109348483980071906463256967 164022725970107859694885451)
            ·
              refine ⟨246034088955161789542328177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164022725970107859694885451 246034088955161789542328177)
              ·
                refine ⟨184525566716371342156746133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 246034088955161789542328177 184525566716371342156746133)
                ·
                  refine ⟨8649635939829906663597475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 184525566716371342156746133 8649635939829906663597475)
                  ·
                    refine ⟨12974453909744859995396213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8649635939829906663597475 12974453909744859995396213)
                    ·
                      refine ⟨1216355054038580624568395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12974453909744859995396213 1216355054038580624568395)
                      ·
                        rfl

theorem cell23_2368843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 6, 1, 5].length) (baseStart_2368843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2368843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2368843 prefixEnd_2368843 := by exact prefixLift 2368843
  have htrace : WordTrace (prefixWord ++ tailWord_2368843) baseStart_2368843 baseEnd_2368843 := by
    simpa [prefixWord, tailWord_2368843, baseEnd_2368843] using wordTrace_append hprefix tailTrace_2368843
  have hstable : (prefixWord ++ tailWord_2368843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368843).length < 2 ^ (prefixWord ++ tailWord_2368843).sum := by decide
  have hdescent : baseEnd_2368843 < baseStart_2368843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368844 : List Nat := [2, 2, 1, 3, 2, 3, 1, 3, 1, 3, 2]
def baseStart_2368844 : Nat := 118140960795 + 2368844 * 2 ^ 59
def prefixEnd_2368844 : Nat := 4983230072969 + 3 ^ 40 * 2368844 * 2
def baseEnd_2368844 : Nat := 1216355567519235120655891

theorem tailTrace_2368844 : CollatzResearch.WordTrace tailWord_2368844 prefixEnd_2368844 1216355567519235120655891 := by
  unfold tailWord_2368844
  simp only [CollatzResearch.WordTrace]
  refine ⟨43199419315045114595568793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57599225753393486127425057 43199419315045114595568793)
  ·
    refine ⟨32399564486283835946676595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43199419315045114595568793 32399564486283835946676595)
    ·
      refine ⟨48599346729425753920014893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32399564486283835946676595 48599346729425753920014893)
      ·
        refine ⟨18224755023534657720005585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48599346729425753920014893 18224755023534657720005585)
        ·
          refine ⟨13668566267650993290004189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18224755023534657720005585 13668566267650993290004189)
          ·
            refine ⟨5125712350369122483751571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13668566267650993290004189 5125712350369122483751571)
            ·
              refine ⟨7688568525553683725627357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5125712350369122483751571 7688568525553683725627357)
              ·
                refine ⟨2883213197082631397110259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7688568525553683725627357 2883213197082631397110259)
                ·
                  refine ⟨4324819795623947095665389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2883213197082631397110259 4324819795623947095665389)
                  ·
                    refine ⟨1621807423358980160874521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4324819795623947095665389 1621807423358980160874521)
                    ·
                      refine ⟨1216355567519235120655891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1621807423358980160874521 1216355567519235120655891)
                      ·
                        rfl

theorem cell23_2368844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 3, 1, 3, 2].length) (baseStart_2368844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2368844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2368844 prefixEnd_2368844 := by exact prefixLift 2368844
  have htrace : WordTrace (prefixWord ++ tailWord_2368844) baseStart_2368844 baseEnd_2368844 := by
    simpa [prefixWord, tailWord_2368844, baseEnd_2368844] using wordTrace_append hprefix tailTrace_2368844
  have hstable : (prefixWord ++ tailWord_2368844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368844).length < 2 ^ (prefixWord ++ tailWord_2368844).sum := by decide
  have hdescent : baseEnd_2368844 < baseStart_2368844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368878 : List Nat := [4, 1, 2, 4, 1, 1, 2, 2, 1, 3, 2]
def baseStart_2368878 : Nat := 118140960795 + 2368878 * 2 ^ 59
def prefixEnd_2368878 : Nat := 4983230072969 + 3 ^ 40 * 2368878 * 2
def baseEnd_2368878 : Nat := 1216373025861487987630735

theorem tailTrace_2368878 : CollatzResearch.WordTrace tailWord_2368878 prefixEnd_2368878 1216373025861487987630735 := by
  unfold tailWord_2368878
  simp only [CollatzResearch.WordTrace]
  refine ⟨10800009838995881624734411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57600052474644701998583525 10800009838995881624734411)
  ·
    refine ⟨16200014758493822437101617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10800009838995881624734411 16200014758493822437101617)
    ·
      refine ⟨12150011068870366827826213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16200014758493822437101617 12150011068870366827826213)
      ·
        refine ⟨2278127075413193780217415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12150011068870366827826213 2278127075413193780217415)
        ·
          refine ⟨3417190613119790670326123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2278127075413193780217415 3417190613119790670326123)
          ·
            refine ⟨5125785919679686005489185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3417190613119790670326123 5125785919679686005489185)
            ·
              refine ⟨3844339439759764504116889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5125785919679686005489185 3844339439759764504116889)
              ·
                refine ⟨2883254579819823378087667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3844339439759764504116889 2883254579819823378087667)
                ·
                  refine ⟨4324881869729735067131501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2883254579819823378087667 4324881869729735067131501)
                  ·
                    refine ⟨1621830701148650650174313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4324881869729735067131501 1621830701148650650174313)
                    ·
                      refine ⟨1216373025861487987630735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1621830701148650650174313 1216373025861487987630735)
                      ·
                        rfl

theorem cell23_2368878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_2368878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2368878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2368878 prefixEnd_2368878 := by exact prefixLift 2368878
  have htrace : WordTrace (prefixWord ++ tailWord_2368878) baseStart_2368878 baseEnd_2368878 := by
    simpa [prefixWord, tailWord_2368878, baseEnd_2368878] using wordTrace_append hprefix tailTrace_2368878
  have hstable : (prefixWord ++ tailWord_2368878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368878).length < 2 ^ (prefixWord ++ tailWord_2368878).sum := by decide
  have hdescent : baseEnd_2368878 < baseStart_2368878 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368964 : List Nat := [2, 3, 3, 2, 1, 1, 2, 2, 2, 1, 4]
def baseStart_2368964 : Nat := 118140960795 + 2368964 * 2 ^ 59
def prefixEnd_2368964 : Nat := 4983230072969 + 3 ^ 40 * 2368964 * 2
def baseEnd_2368964 : Nat := 1216417185197774651155339

theorem tailTrace_2368964 : CollatzResearch.WordTrace tailWord_2368964 prefixEnd_2368964 1216417185197774651155339 := by
  unfold tailWord_2368964
  simp only [CollatzResearch.WordTrace]
  refine ⟨43201607694827744842752973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57602143593103659790337297 43201607694827744842752973)
  ·
    refine ⟨16200602885560404316032365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43201607694827744842752973 16200602885560404316032365)
    ·
      refine ⟨6075226082085151618512137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16200602885560404316032365 6075226082085151618512137)
      ·
        refine ⟨4556419561563863713884103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6075226082085151618512137 4556419561563863713884103)
        ·
          refine ⟨6834629342345795570826155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4556419561563863713884103 6834629342345795570826155)
          ·
            refine ⟨10251944013518693356239233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6834629342345795570826155 10251944013518693356239233)
            ·
              refine ⟨7688958010139020017179425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10251944013518693356239233 7688958010139020017179425)
              ·
                refine ⟨5766718507604265012884569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7688958010139020017179425 5766718507604265012884569)
                ·
                  refine ⟨4325038880703198759663427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5766718507604265012884569 4325038880703198759663427)
                  ·
                    refine ⟨6487558321054798139495141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4325038880703198759663427 6487558321054798139495141)
                    ·
                      refine ⟨1216417185197774651155339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6487558321054798139495141 1216417185197774651155339)
                      ·
                        rfl

theorem cell23_2368964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_2368964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2368964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2368964 prefixEnd_2368964 := by exact prefixLift 2368964
  have htrace : WordTrace (prefixWord ++ tailWord_2368964) baseStart_2368964 baseEnd_2368964 := by
    simpa [prefixWord, tailWord_2368964, baseEnd_2368964] using wordTrace_append hprefix tailTrace_2368964
  have hstable : (prefixWord ++ tailWord_2368964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368964).length < 2 ^ (prefixWord ++ tailWord_2368964).sum := by decide
  have hdescent : baseEnd_2368964 < baseStart_2368964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2368967 : List Nat := [1, 1, 4, 1, 1, 3, 1, 4, 2, 2, 3]
def baseStart_2368967 : Nat := 118140960795 + 2368967 * 2 ^ 59
def prefixEnd_2368967 : Nat := 4983230072969 + 3 ^ 40 * 2368967 * 2
def baseEnd_2368967 : Nat := 1216418725639738139417825

theorem tailTrace_2368967 : CollatzResearch.WordTrace tailWord_2368967 prefixEnd_2368967 1216418725639738139417825 := by
  unfold tailWord_2368967
  simp only [CollatzResearch.WordTrace]
  refine ⟨86403324808644621197865155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57602216539096414131910103 86403324808644621197865155)
  ·
    refine ⟨129604987212966931796797733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86403324808644621197865155 129604987212966931796797733)
    ·
      refine ⟨24300935102431299711899575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 129604987212966931796797733 24300935102431299711899575)
      ·
        refine ⟨36451402653646949567849363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24300935102431299711899575 36451402653646949567849363)
        ·
          refine ⟨54677103980470424351774045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36451402653646949567849363 54677103980470424351774045)
          ·
            refine ⟨20503913992676409131915267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54677103980470424351774045 20503913992676409131915267)
            ·
              refine ⟨30755870989014613697872901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20503913992676409131915267 30755870989014613697872901)
              ·
                refine ⟨5766725810440240068351169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30755870989014613697872901 5766725810440240068351169)
                ·
                  refine ⟨4325044357830180051263377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5766725810440240068351169 4325044357830180051263377)
                  ·
                    refine ⟨3243783268372635038447533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4325044357830180051263377 3243783268372635038447533)
                    ·
                      refine ⟨1216418725639738139417825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3243783268372635038447533 1216418725639738139417825)
                      ·
                        rfl

theorem cell23_2368967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 4, 2, 2, 3].length) (baseStart_2368967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2368967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2368967 prefixEnd_2368967 := by exact prefixLift 2368967
  have htrace : WordTrace (prefixWord ++ tailWord_2368967) baseStart_2368967 baseEnd_2368967 := by
    simpa [prefixWord, tailWord_2368967, baseEnd_2368967] using wordTrace_append hprefix tailTrace_2368967
  have hstable : (prefixWord ++ tailWord_2368967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2368967).length < 2 ^ (prefixWord ++ tailWord_2368967).sum := by decide
  have hdescent : baseEnd_2368967 < baseStart_2368967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2368967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369031 : List Nat := [1, 1, 4, 3, 2, 2, 2, 1, 3, 1, 3]
def baseStart_2369031 : Nat := 118140960795 + 2369031 * 2 ^ 59
def prefixEnd_2369031 : Nat := 4983230072969 + 3 ^ 40 * 2369031 * 2
def baseEnd_2369031 : Nat := 1216451588401625889017531

theorem tailTrace_2369031 : CollatzResearch.WordTrace tailWord_2369031 prefixEnd_2369031 1216451588401625889017531 := by
  unfold tailWord_2369031
  simp only [CollatzResearch.WordTrace]
  refine ⟨86405659080412760128194947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57603772720275173418796631 86405659080412760128194947)
  ·
    refine ⟨129608488620619140192292421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86405659080412760128194947 129608488620619140192292421)
    ·
      refine ⟨24301591616366088786054829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 129608488620619140192292421 24301591616366088786054829)
      ·
        refine ⟨9113096856137283294770561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24301591616366088786054829 9113096856137283294770561)
        ·
          refine ⟨6834822642102962471077921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9113096856137283294770561 6834822642102962471077921)
          ·
            refine ⟨5126116981577221853308441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6834822642102962471077921 5126116981577221853308441)
            ·
              refine ⟨3844587736182916389981331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5126116981577221853308441 3844587736182916389981331)
              ·
                refine ⟨5766881604274374584971997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3844587736182916389981331 5766881604274374584971997)
                ·
                  refine ⟨2162580601602890469364499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5766881604274374584971997 2162580601602890469364499)
                  ·
                    refine ⟨3243870902404335704046749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2162580601602890469364499 3243870902404335704046749)
                    ·
                      refine ⟨1216451588401625889017531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3243870902404335704046749 1216451588401625889017531)
                      ·
                        rfl

theorem cell23_2369031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_2369031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2369031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2369031 prefixEnd_2369031 := by exact prefixLift 2369031
  have htrace : WordTrace (prefixWord ++ tailWord_2369031) baseStart_2369031 baseEnd_2369031 := by
    simpa [prefixWord, tailWord_2369031, baseEnd_2369031] using wordTrace_append hprefix tailTrace_2369031
  have hstable : (prefixWord ++ tailWord_2369031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369031).length < 2 ^ (prefixWord ++ tailWord_2369031).sum := by decide
  have hdescent : baseEnd_2369031 < baseStart_2369031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369077 : List Nat := [1, 3, 3, 1, 1, 5, 9]
def baseStart_2369077 : Nat := 118140960795 + 2369077 * 2 ^ 59
def prefixEnd_2369077 : Nat := 4983230072969 + 3 ^ 40 * 2369077 * 2
def baseEnd_2369077 : Nat := 15018212450762132210399

theorem tailTrace_2369077 : CollatzResearch.WordTrace tailWord_2369077 prefixEnd_2369077 15018212450762132210399 := by
  unfold tailWord_2369077
  simp only [CollatzResearch.WordTrace]
  refine ⟨86407336838246109984369485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57604891225497406656246323 86407336838246109984369485)
  ·
    refine ⟨32402751314342291244138557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86407336838246109984369485 32402751314342291244138557)
    ·
      refine ⟨12151031742878359216551959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32402751314342291244138557 12151031742878359216551959)
      ·
        refine ⟨18226547614317538824827939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12151031742878359216551959 18226547614317538824827939)
        ·
          refine ⟨27339821421476308237241909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18226547614317538824827939 27339821421476308237241909)
          ·
            refine ⟨2563108258263403897241429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27339821421476308237241909 2563108258263403897241429)
            ·
              refine ⟨15018212450762132210399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2563108258263403897241429 15018212450762132210399)
              ·
                rfl

theorem cell23_2369077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 9].length) (baseStart_2369077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2369077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2369077 prefixEnd_2369077 := by exact prefixLift 2369077
  have htrace : WordTrace (prefixWord ++ tailWord_2369077) baseStart_2369077 baseEnd_2369077 := by
    simpa [prefixWord, tailWord_2369077, baseEnd_2369077] using wordTrace_append hprefix tailTrace_2369077
  have hstable : (prefixWord ++ tailWord_2369077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369077).length < 2 ^ (prefixWord ++ tailWord_2369077).sum := by decide
  have hdescent : baseEnd_2369077 < baseStart_2369077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369138 : List Nat := [3, 2, 1, 2, 3, 2, 2, 2, 2, 1, 3]
def baseStart_2369138 : Nat := 118140960795 + 2369138 * 2 ^ 59
def prefixEnd_2369138 : Nat := 4983230072969 + 3 ^ 40 * 2369138 * 2
def baseEnd_2369138 : Nat := 1216506530831656970379539

theorem tailTrace_2369138 : CollatzResearch.WordTrace tailWord_2369138 prefixEnd_2369138 1216506530831656970379539 := by
  unfold tailWord_2369138
  simp only [CollatzResearch.WordTrace]
  refine ⟨21602390422756279350585017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57606374460683411601560045 21602390422756279350585017)
  ·
    refine ⟨16201792817067209512938763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21602390422756279350585017 16201792817067209512938763)
    ·
      refine ⟨24302689225600814269408145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16201792817067209512938763 24302689225600814269408145)
      ·
        refine ⟨18227016919200610702056109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24302689225600814269408145 18227016919200610702056109)
        ·
          refine ⟨6835131344700229013271041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18227016919200610702056109 6835131344700229013271041)
          ·
            refine ⟨5126348508525171759953281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6835131344700229013271041 5126348508525171759953281)
            ·
              refine ⟨3844761381393878819964961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5126348508525171759953281 3844761381393878819964961)
              ·
                refine ⟨2883571036045409114973721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3844761381393878819964961 2883571036045409114973721)
                ·
                  refine ⟨2162678277034056836230291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2883571036045409114973721 2162678277034056836230291)
                  ·
                    refine ⟨3244017415551085254345437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2162678277034056836230291 3244017415551085254345437)
                    ·
                      refine ⟨1216506530831656970379539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3244017415551085254345437 1216506530831656970379539)
                      ·
                        rfl

theorem cell23_2369138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 2, 2, 1, 3].length) (baseStart_2369138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2369138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2369138 prefixEnd_2369138 := by exact prefixLift 2369138
  have htrace : WordTrace (prefixWord ++ tailWord_2369138) baseStart_2369138 baseEnd_2369138 := by
    simpa [prefixWord, tailWord_2369138, baseEnd_2369138] using wordTrace_append hprefix tailTrace_2369138
  have hstable : (prefixWord ++ tailWord_2369138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369138).length < 2 ^ (prefixWord ++ tailWord_2369138).sum := by decide
  have hdescent : baseEnd_2369138 < baseStart_2369138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369147 : List Nat := [1, 1, 1, 1, 1, 4, 3, 1, 1, 6, 3]
def baseStart_2369147 : Nat := 118140960795 + 2369147 * 2 ^ 59
def prefixEnd_2369147 : Nat := 4983230072969 + 3 ^ 40 * 2369147 * 2
def baseEnd_2369147 : Nat := 1216511152157547435166997

theorem tailTrace_2369147 : CollatzResearch.WordTrace tailWord_2369147 prefixEnd_2369147 1216511152157547435166997 := by
  unfold tailWord_2369147
  simp only [CollatzResearch.WordTrace]
  refine ⟨86409889947992511939417695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57606593298661674626278463 86409889947992511939417695)
  ·
    refine ⟨129614834921988767909126543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86409889947992511939417695 129614834921988767909126543)
    ·
      refine ⟨194422252382983151863689815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129614834921988767909126543 194422252382983151863689815)
      ·
        refine ⟨291633378574474727795534723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194422252382983151863689815 291633378574474727795534723)
        ·
          refine ⟨437450067861712091693302085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 291633378574474727795534723 437450067861712091693302085)
          ·
            refine ⟨82021887724071017192494141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 437450067861712091693302085 82021887724071017192494141)
            ·
              refine ⟨30758207896526631447185303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82021887724071017192494141 30758207896526631447185303)
              ·
                refine ⟨46137311844789947170777955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30758207896526631447185303 46137311844789947170777955)
                ·
                  refine ⟨69205967767184920756166933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46137311844789947170777955 69205967767184920756166933)
                  ·
                    refine ⟨3244029739086793160445325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 69205967767184920756166933 3244029739086793160445325)
                    ·
                      refine ⟨1216511152157547435166997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3244029739086793160445325 1216511152157547435166997)
                      ·
                        rfl

theorem cell23_2369147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 6, 3].length) (baseStart_2369147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2369147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2369147 prefixEnd_2369147 := by exact prefixLift 2369147
  have htrace : WordTrace (prefixWord ++ tailWord_2369147) baseStart_2369147 baseEnd_2369147 := by
    simpa [prefixWord, tailWord_2369147, baseEnd_2369147] using wordTrace_append hprefix tailTrace_2369147
  have hstable : (prefixWord ++ tailWord_2369147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369147).length < 2 ^ (prefixWord ++ tailWord_2369147).sum := by decide
  have hdescent : baseEnd_2369147 < baseStart_2369147 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369182 : List Nat := [4, 3, 1, 1, 1, 4, 2, 1, 1, 3, 2]
def baseStart_2369182 : Nat := 118140960795 + 2369182 * 2 ^ 59
def prefixEnd_2369182 : Nat := 4983230072969 + 3 ^ 40 * 2369182 * 2
def baseEnd_2369182 : Nat := 1216529123980454798229337

theorem tailTrace_2369182 : CollatzResearch.WordTrace tailWord_2369182 prefixEnd_2369182 1216529123980454798229337 := by
  unfold tailWord_2369182
  simp only [CollatzResearch.WordTrace]
  refine ⟨10801395812858214114617725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57607444335243808611294533 10801395812858214114617725)
  ·
    refine ⟨4050523429821830292981647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10801395812858214114617725 4050523429821830292981647)
    ·
      refine ⟨6075785144732745439472471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4050523429821830292981647 6075785144732745439472471)
      ·
        refine ⟨9113677717099118159208707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6075785144732745439472471 9113677717099118159208707)
        ·
          refine ⟨13670516575648677238813061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9113677717099118159208707 13670516575648677238813061)
          ·
            refine ⟨2563221857934126982277449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13670516575648677238813061 2563221857934126982277449)
            ·
              refine ⟨1922416393450595236708087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2563221857934126982277449 1922416393450595236708087)
              ·
                refine ⟨2883624590175892855062131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1922416393450595236708087 2883624590175892855062131)
                ·
                  refine ⟨4325436885263839282593197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2883624590175892855062131 4325436885263839282593197)
                  ·
                    refine ⟨1622038831973939730972449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4325436885263839282593197 1622038831973939730972449)
                    ·
                      refine ⟨1216529123980454798229337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1622038831973939730972449 1216529123980454798229337)
                      ·
                        rfl

theorem cell23_2369182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 2, 1, 1, 3, 2].length) (baseStart_2369182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2369182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2369182 prefixEnd_2369182 := by exact prefixLift 2369182
  have htrace : WordTrace (prefixWord ++ tailWord_2369182) baseStart_2369182 baseEnd_2369182 := by
    simpa [prefixWord, tailWord_2369182, baseEnd_2369182] using wordTrace_append hprefix tailTrace_2369182
  have hstable : (prefixWord ++ tailWord_2369182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369182).length < 2 ^ (prefixWord ++ tailWord_2369182).sum := by decide
  have hdescent : baseEnd_2369182 < baseStart_2369182 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369214 : List Nat := [4, 2, 1, 1, 2, 2, 1, 2, 1, 7]
def baseStart_2369214 : Nat := 118140960795 + 2369214 * 2 ^ 59
def prefixEnd_2369214 : Nat := 4983230072969 + 3 ^ 40 * 2369214 * 2
def baseEnd_2369214 : Nat := 405515185120466224343063

theorem tailTrace_2369214 : CollatzResearch.WordTrace tailWord_2369214 prefixEnd_2369214 405515185120466224343063 := by
  unfold tailWord_2369214
  simp only [CollatzResearch.WordTrace]
  refine ⟨10801541704843722797763337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57608222425833188254737797 10801541704843722797763337)
  ·
    refine ⟨8101156278632792098322503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10801541704843722797763337 8101156278632792098322503)
    ·
      refine ⟨12151734417949188147483755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8101156278632792098322503 12151734417949188147483755)
      ·
        refine ⟨18227601626923782221225633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12151734417949188147483755 18227601626923782221225633)
        ·
          refine ⟨13670701220192836665919225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18227601626923782221225633 13670701220192836665919225)
          ·
            refine ⟨10253025915144627499439419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13670701220192836665919225 10253025915144627499439419)
            ·
              refine ⟨15379538872716941249159129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10253025915144627499439419 15379538872716941249159129)
              ·
                refine ⟨11534654154537705936869347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15379538872716941249159129 11534654154537705936869347)
                ·
                  refine ⟨17301981231806558905304021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11534654154537705936869347 17301981231806558905304021)
                  ·
                    refine ⟨405515185120466224343063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17301981231806558905304021 405515185120466224343063)
                    ·
                      rfl

theorem cell23_2369214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 2, 1, 7].length) (baseStart_2369214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2369214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2369214 prefixEnd_2369214 := by exact prefixLift 2369214
  have htrace : WordTrace (prefixWord ++ tailWord_2369214) baseStart_2369214 baseEnd_2369214 := by
    simpa [prefixWord, tailWord_2369214, baseEnd_2369214] using wordTrace_append hprefix tailTrace_2369214
  have hstable : (prefixWord ++ tailWord_2369214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369214).length < 2 ^ (prefixWord ++ tailWord_2369214).sum := by decide
  have hdescent : baseEnd_2369214 < baseStart_2369214 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369375 : List Nat := [1, 1, 2, 3, 1, 5, 2, 1, 3, 2, 2]
def baseStart_2369375 : Nat := 118140960795 + 2369375 * 2 ^ 59
def prefixEnd_2369375 : Nat := 4983230072969 + 3 ^ 40 * 2369375 * 2
def baseEnd_2369375 : Nat := 1216628225746772543115949

theorem tailTrace_2369375 : CollatzResearch.WordTrace tailWord_2369375 prefixEnd_2369375 1216628225746772543115949 := by
  unfold tailWord_2369375
  simp only [CollatzResearch.WordTrace]
  refine ⟨86418205791166506878717579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57612137194111004585811719 86418205791166506878717579)
  ·
    refine ⟨129627308686749760318076369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86418205791166506878717579 129627308686749760318076369)
    ·
      refine ⟨97220481515062320238557277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129627308686749760318076369 97220481515062320238557277)
      ·
        refine ⟨36457680568148370089458979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97220481515062320238557277 36457680568148370089458979)
        ·
          refine ⟨54686520852222555134188469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36457680568148370089458979 54686520852222555134188469)
          ·
            refine ⟨5126861329895864543830169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54686520852222555134188469 5126861329895864543830169)
            ·
              refine ⟨3845145997421898407872627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5126861329895864543830169 3845145997421898407872627)
              ·
                refine ⟨5767718996132847611808941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3845145997421898407872627 5767718996132847611808941)
                ·
                  refine ⟨2162894623549817854428353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5767718996132847611808941 2162894623549817854428353)
                  ·
                    refine ⟨1622170967662363390821265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2162894623549817854428353 1622170967662363390821265)
                    ·
                      refine ⟨1216628225746772543115949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1622170967662363390821265 1216628225746772543115949)
                      ·
                        rfl

theorem cell23_2369375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 1, 3, 2, 2].length) (baseStart_2369375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2369375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2369375 prefixEnd_2369375 := by exact prefixLift 2369375
  have htrace : WordTrace (prefixWord ++ tailWord_2369375) baseStart_2369375 baseEnd_2369375 := by
    simpa [prefixWord, tailWord_2369375, baseEnd_2369375] using wordTrace_append hprefix tailTrace_2369375
  have hstable : (prefixWord ++ tailWord_2369375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369375).length < 2 ^ (prefixWord ++ tailWord_2369375).sum := by decide
  have hdescent : baseEnd_2369375 < baseStart_2369375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369378 : List Nat := [3, 3, 2, 1, 2, 2, 1, 2, 1, 1, 5]
def baseStart_2369378 : Nat := 118140960795 + 2369378 * 2 ^ 59
def prefixEnd_2369378 : Nat := 4983230072969 + 3 ^ 40 * 2369378 * 2
def baseEnd_2369378 : Nat := 1216629766188736031378435

theorem tailTrace_2369378 : CollatzResearch.WordTrace tailWord_2369378 prefixEnd_2369378 1216629766188736031378435 := by
  unfold tailWord_2369378
  simp only [CollatzResearch.WordTrace]
  refine ⟨21604578802538909597769197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57612210140103758927384525 21604578802538909597769197)
  ·
    refine ⟨8101717050952091099163449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21604578802538909597769197 8101717050952091099163449)
    ·
      refine ⟨6076287788214068324372587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8101717050952091099163449 6076287788214068324372587)
      ·
        refine ⟨9114431682321102486558881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6076287788214068324372587 9114431682321102486558881)
        ·
          refine ⟨6835823761740826864919161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9114431682321102486558881 6835823761740826864919161)
          ·
            refine ⟨5126867821305620148689371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6835823761740826864919161 5126867821305620148689371)
            ·
              refine ⟨7690301731958430223034057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5126867821305620148689371 7690301731958430223034057)
              ·
                refine ⟨5767726298968822667275543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7690301731958430223034057 5767726298968822667275543)
                ·
                  refine ⟨8651589448453234000913315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5767726298968822667275543 8651589448453234000913315)
                  ·
                    refine ⟨12977384172679851001369973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8651589448453234000913315 12977384172679851001369973)
                    ·
                      refine ⟨1216629766188736031378435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12977384172679851001369973 1216629766188736031378435)
                      ·
                        rfl

theorem cell23_2369378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_2369378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2369378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2369378 prefixEnd_2369378 := by exact prefixLift 2369378
  have htrace : WordTrace (prefixWord ++ tailWord_2369378) baseStart_2369378 baseEnd_2369378 := by
    simpa [prefixWord, tailWord_2369378, baseEnd_2369378] using wordTrace_append hprefix tailTrace_2369378
  have hstable : (prefixWord ++ tailWord_2369378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369378).length < 2 ^ (prefixWord ++ tailWord_2369378).sum := by decide
  have hdescent : baseEnd_2369378 < baseStart_2369378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369388 : List Nat := [2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 4]
def baseStart_2369388 : Nat := 118140960795 + 2369388 * 2 ^ 59
def prefixEnd_2369388 : Nat := 4983230072969 + 3 ^ 40 * 2369388 * 2
def baseEnd_2369388 : Nat := 1216634900995280992253389

theorem tailTrace_2369388 : CollatzResearch.WordTrace tailWord_2369388 prefixEnd_2369388 1216634900995280992253389 := by
  unfold tailWord_2369388
  simp only [CollatzResearch.WordTrace]
  refine ⟨43209339970059705049470409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57612453293412940065960545 43209339970059705049470409)
  ·
    refine ⟨32407004977544778787102807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43209339970059705049470409 32407004977544778787102807)
    ·
      refine ⟨48610507466317168180654211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32407004977544778787102807 48610507466317168180654211)
      ·
        refine ⟨72915761199475752270981317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48610507466317168180654211 72915761199475752270981317)
        ·
          refine ⟨13671705224901703550808997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72915761199475752270981317 13671705224901703550808997)
          ·
            refine ⟨2563444729669069415776687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13671705224901703550808997 2563444729669069415776687)
            ·
              refine ⟨3845167094503604123665031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2563444729669069415776687 3845167094503604123665031)
              ·
                refine ⟨5767750641755406185497547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3845167094503604123665031 5767750641755406185497547)
                ·
                  refine ⟨8651625962633109278246321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5767750641755406185497547 8651625962633109278246321)
                  ·
                    refine ⟨6488719471974831958684741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8651625962633109278246321 6488719471974831958684741)
                    ·
                      refine ⟨1216634900995280992253389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6488719471974831958684741 1216634900995280992253389)
                      ·
                        rfl

theorem cell23_2369388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 4].length) (baseStart_2369388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2369388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2369388 prefixEnd_2369388 := by exact prefixLift 2369388
  have htrace : WordTrace (prefixWord ++ tailWord_2369388) baseStart_2369388 baseEnd_2369388 := by
    simpa [prefixWord, tailWord_2369388, baseEnd_2369388] using wordTrace_append hprefix tailTrace_2369388
  have hstable : (prefixWord ++ tailWord_2369388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369388).length < 2 ^ (prefixWord ++ tailWord_2369388).sum := by decide
  have hdescent : baseEnd_2369388 < baseStart_2369388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369398 : List Nat := [5, 1, 1, 3, 2, 1, 1, 9]
def baseStart_2369398 : Nat := 118140960795 + 2369398 * 2 ^ 59
def prefixEnd_2369398 : Nat := 4983230072969 + 3 ^ 40 * 2369398 * 2
def baseEnd_2369398 : Nat := 45060742066734294560309

theorem tailTrace_2369398 : CollatzResearch.WordTrace tailWord_2369398 prefixEnd_2369398 45060742066734294560309 := by
  unfold tailWord_2369398
  simp only [CollatzResearch.WordTrace]
  refine ⟨5401190291880198862925303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57612696446722121204536565 5401190291880198862925303)
  ·
    refine ⟨8101785437820298294387955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5401190291880198862925303 8101785437820298294387955)
    ·
      refine ⟨12152678156730447441581933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8101785437820298294387955 12152678156730447441581933)
      ·
        refine ⟨4557254308773917790593225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12152678156730447441581933 4557254308773917790593225)
        ·
          refine ⟨3417940731580438342944919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4557254308773917790593225 3417940731580438342944919)
          ·
            refine ⟨5126911097370657514417379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3417940731580438342944919 5126911097370657514417379)
            ·
              refine ⟨7690366646055986271626069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5126911097370657514417379 7690366646055986271626069)
              ·
                refine ⟨45060742066734294560309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7690366646055986271626069 45060742066734294560309)
                ·
                  rfl

theorem cell23_2369398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 9].length) (baseStart_2369398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2369398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2369398 prefixEnd_2369398 := by exact prefixLift 2369398
  have htrace : WordTrace (prefixWord ++ tailWord_2369398) baseStart_2369398 baseEnd_2369398 := by
    simpa [prefixWord, tailWord_2369398, baseEnd_2369398] using wordTrace_append hprefix tailTrace_2369398
  have hstable : (prefixWord ++ tailWord_2369398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369398).length < 2 ^ (prefixWord ++ tailWord_2369398).sum := by decide
  have hdescent : baseEnd_2369398 < baseStart_2369398 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369426 : List Nat := [3, 2, 3, 2, 1, 2, 3, 2, 1, 2, 2]
def baseStart_2369426 : Nat := 118140960795 + 2369426 * 2 ^ 59
def prefixEnd_2369426 : Nat := 4983230072969 + 3 ^ 40 * 2369426 * 2
def baseEnd_2369426 : Nat := 1216654413260151843578215

theorem tailTrace_2369426 : CollatzResearch.WordTrace tailWord_2369426 prefixEnd_2369426 1216654413260151843578215 := by
  unfold tailWord_2369426
  simp only [CollatzResearch.WordTrace]
  refine ⟨21605016478495435647206033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57613377275987828392549421 21605016478495435647206033)
  ·
    refine ⟨16203762358871576735404525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21605016478495435647206033 16203762358871576735404525)
    ·
      refine ⟨6076410884576841275776697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16203762358871576735404525 6076410884576841275776697)
      ·
        refine ⟨4557308163432630956832523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6076410884576841275776697 4557308163432630956832523)
        ·
          refine ⟨6835962245148946435248785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4557308163432630956832523 6835962245148946435248785)
          ·
            refine ⟨5126971683861709826436589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6835962245148946435248785 5126971683861709826436589)
            ·
              refine ⟨1922614381448141184913721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5126971683861709826436589 1922614381448141184913721)
              ·
                refine ⟨1441960786086105888685291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1922614381448141184913721 1441960786086105888685291)
                ·
                  refine ⟨2162941179129158833027937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1441960786086105888685291 2162941179129158833027937)
                  ·
                    refine ⟨1622205884346869124770953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2162941179129158833027937 1622205884346869124770953)
                    ·
                      refine ⟨1216654413260151843578215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1622205884346869124770953 1216654413260151843578215)
                      ·
                        rfl

theorem cell23_2369426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_2369426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2369426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2369426 prefixEnd_2369426 := by exact prefixLift 2369426
  have htrace : WordTrace (prefixWord ++ tailWord_2369426) baseStart_2369426 baseEnd_2369426 := by
    simpa [prefixWord, tailWord_2369426, baseEnd_2369426] using wordTrace_append hprefix tailTrace_2369426
  have hstable : (prefixWord ++ tailWord_2369426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369426).length < 2 ^ (prefixWord ++ tailWord_2369426).sum := by decide
  have hdescent : baseEnd_2369426 < baseStart_2369426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369442 : List Nat := [3, 3, 1, 2, 3, 1, 1, 3, 2, 1, 3]
def baseStart_2369442 : Nat := 118140960795 + 2369442 * 2 ^ 59
def prefixEnd_2369442 : Nat := 4983230072969 + 3 ^ 40 * 2369442 * 2
def baseEnd_2369442 : Nat := 1216662628950623780978141

theorem tailTrace_2369442 : CollatzResearch.WordTrace tailWord_2369442 prefixEnd_2369442 1216662628950623780978141 := by
  unfold tailWord_2369442
  simp only [CollatzResearch.WordTrace]
  refine ⟨21605162370480944330351645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57613766321282518214271053 21605162370480944330351645)
  ·
    refine ⟨8101935888930354123881867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21605162370480944330351645 8101935888930354123881867)
    ·
      refine ⟨12152903833395531185822801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8101935888930354123881867 12152903833395531185822801)
      ·
        refine ⟨9114677875046648389367101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12152903833395531185822801 9114677875046648389367101)
        ·
          refine ⟨3418004203142493146012663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9114677875046648389367101 3418004203142493146012663)
          ·
            refine ⟨5127006304713739719018995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3418004203142493146012663 5127006304713739719018995)
            ·
              refine ⟨7690509457070609578528493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5127006304713739719018995 7690509457070609578528493)
              ·
                refine ⟨2883941046401478591948185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7690509457070609578528493 2883941046401478591948185)
                ·
                  refine ⟨2162955784801108943961139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2883941046401478591948185 2162955784801108943961139)
                  ·
                    refine ⟨3244433677201663415941709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2162955784801108943961139 3244433677201663415941709)
                    ·
                      refine ⟨1216662628950623780978141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3244433677201663415941709 1216662628950623780978141)
                      ·
                        rfl

theorem cell23_2369442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_2369442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2369442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2369442 prefixEnd_2369442 := by exact prefixLift 2369442
  have htrace : WordTrace (prefixWord ++ tailWord_2369442) baseStart_2369442 baseEnd_2369442 := by
    simpa [prefixWord, tailWord_2369442, baseEnd_2369442] using wordTrace_append hprefix tailTrace_2369442
  have hstable : (prefixWord ++ tailWord_2369442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369442).length < 2 ^ (prefixWord ++ tailWord_2369442).sum := by decide
  have hdescent : baseEnd_2369442 < baseStart_2369442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369481 : List Nat := [1, 2, 1, 1, 2, 1, 2, 3, 4, 3, 3]
def baseStart_2369481 : Nat := 118140960795 + 2369481 * 2 ^ 59
def prefixEnd_2369481 : Nat := 4983230072969 + 3 ^ 40 * 2369481 * 2
def baseEnd_2369481 : Nat := 1216682654696149128390461

theorem tailTrace_2369481 : CollatzResearch.WordTrace tailWord_2369481 prefixEnd_2369481 1216682654696149128390461 := by
  unfold tailWord_2369481
  simp only [CollatzResearch.WordTrace]
  refine ⟨86422071928782486982076297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57614714619188324654717531 86422071928782486982076297)
  ·
    refine ⟨64816553946586865236557223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86422071928782486982076297 64816553946586865236557223)
    ·
      refine ⟨97224830919880297854835835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64816553946586865236557223 97224830919880297854835835)
      ·
        refine ⟨145837246379820446782253753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97224830919880297854835835 145837246379820446782253753)
        ·
          refine ⟨109377934784865335086690315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145837246379820446782253753 109377934784865335086690315)
          ·
            refine ⟨164066902177298002630035473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109377934784865335086690315 164066902177298002630035473)
            ·
              refine ⟨123050176632973501972526605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 164066902177298002630035473 123050176632973501972526605)
              ·
                refine ⟨46143816237365063239697477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 123050176632973501972526605 46143816237365063239697477)
                ·
                  refine ⟨8651965544505949357443277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46143816237365063239697477 8651965544505949357443277)
                  ·
                    refine ⟨3244487079189731009041229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8651965544505949357443277 3244487079189731009041229)
                    ·
                      refine ⟨1216682654696149128390461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3244487079189731009041229 1216682654696149128390461)
                      ·
                        rfl

theorem cell23_2369481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 4, 3, 3].length) (baseStart_2369481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2369481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2369481 prefixEnd_2369481 := by exact prefixLift 2369481
  have htrace : WordTrace (prefixWord ++ tailWord_2369481) baseStart_2369481 baseEnd_2369481 := by
    simpa [prefixWord, tailWord_2369481, baseEnd_2369481] using wordTrace_append hprefix tailTrace_2369481
  have hstable : (prefixWord ++ tailWord_2369481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369481).length < 2 ^ (prefixWord ++ tailWord_2369481).sum := by decide
  have hdescent : baseEnd_2369481 < baseStart_2369481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369508 : List Nat := [2, 3, 1, 1, 1, 1, 3, 2, 2, 5, 2]
def baseStart_2369508 : Nat := 118140960795 + 2369508 * 2 ^ 59
def prefixEnd_2369508 : Nat := 4983230072969 + 3 ^ 40 * 2369508 * 2
def baseEnd_2369508 : Nat := 1216696518673820522752837

theorem tailTrace_2369508 : CollatzResearch.WordTrace tailWord_2369508 prefixEnd_2369508 1216696518673820522752837 := by
  unfold tailWord_2369508
  simp only [CollatzResearch.WordTrace]
  refine ⟨43211528349842335296654589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57615371133123113728872785 43211528349842335296654589)
  ·
    refine ⟨16204323131190875736245471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43211528349842335296654589 16204323131190875736245471)
    ·
      refine ⟨24306484696786313604368207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16204323131190875736245471 24306484696786313604368207)
      ·
        refine ⟨36459727045179470406552311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24306484696786313604368207 36459727045179470406552311)
        ·
          refine ⟨54689590567769205609828467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36459727045179470406552311 54689590567769205609828467)
          ·
            refine ⟨82034385851653808414742701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54689590567769205609828467 82034385851653808414742701)
            ·
              refine ⟨30762894694370178155528513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82034385851653808414742701 30762894694370178155528513)
              ·
                refine ⟨23072171020777633616646385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30762894694370178155528513 23072171020777633616646385)
                ·
                  refine ⟨17304128265583225212484789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23072171020777633616646385 17304128265583225212484789)
                  ·
                    refine ⟨1622262024898427363670449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17304128265583225212484789 1622262024898427363670449)
                    ·
                      refine ⟨1216696518673820522752837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1622262024898427363670449 1216696518673820522752837)
                      ·
                        rfl

theorem cell23_2369508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 2, 5, 2].length) (baseStart_2369508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2369508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2369508 prefixEnd_2369508 := by exact prefixLift 2369508
  have htrace : WordTrace (prefixWord ++ tailWord_2369508) baseStart_2369508 baseEnd_2369508 := by
    simpa [prefixWord, tailWord_2369508, baseEnd_2369508] using wordTrace_append hprefix tailTrace_2369508
  have hstable : (prefixWord ++ tailWord_2369508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369508).length < 2 ^ (prefixWord ++ tailWord_2369508).sum := by decide
  have hdescent : baseEnd_2369508 < baseStart_2369508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369518 : List Nat := [4, 1, 2, 1, 3, 2, 1, 1, 1, 7]
def baseStart_2369518 : Nat := 118140960795 + 2369518 * 2 ^ 59
def prefixEnd_2369518 : Nat := 4983230072969 + 3 ^ 40 * 2369518 * 2
def baseEnd_2369518 : Nat := 405567217826788494542597

theorem tailTrace_2369518 : CollatzResearch.WordTrace tailWord_2369518 prefixEnd_2369518 405567217826788494542597 := by
  unfold tailWord_2369518
  simp only [CollatzResearch.WordTrace]
  refine ⟨10802927678706055287646651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57615614286432294867448805 10802927678706055287646651)
  ·
    refine ⟨16204391518059082931469977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10802927678706055287646651 16204391518059082931469977)
    ·
      refine ⟨12153293638544312198602483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16204391518059082931469977 12153293638544312198602483)
      ·
        refine ⟨18229940457816468297903725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12153293638544312198602483 18229940457816468297903725)
        ·
          refine ⟨6836227671681175611713897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18229940457816468297903725 6836227671681175611713897)
          ·
            refine ⟨5127170753760881708785423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6836227671681175611713897 5127170753760881708785423)
            ·
              refine ⟨7690756130641322563178135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5127170753760881708785423 7690756130641322563178135)
              ·
                refine ⟨11536134195961983844767203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7690756130641322563178135 11536134195961983844767203)
                ·
                  refine ⟨17304201293942975767150805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11536134195961983844767203 17304201293942975767150805)
                  ·
                    refine ⟨405567217826788494542597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17304201293942975767150805 405567217826788494542597)
                    ·
                      rfl

theorem cell23_2369518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 1, 1, 7].length) (baseStart_2369518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2369518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2369518 prefixEnd_2369518 := by exact prefixLift 2369518
  have htrace : WordTrace (prefixWord ++ tailWord_2369518) baseStart_2369518 baseEnd_2369518 := by
    simpa [prefixWord, tailWord_2369518, baseEnd_2369518] using wordTrace_append hprefix tailTrace_2369518
  have hstable : (prefixWord ++ tailWord_2369518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369518).length < 2 ^ (prefixWord ++ tailWord_2369518).sum := by decide
  have hdescent : baseEnd_2369518 < baseStart_2369518 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369565 : List Nat := [1, 4, 2, 2, 2, 1, 2, 2, 3, 4]
def baseStart_2369565 : Nat := 118140960795 + 2369565 * 2 ^ 59
def prefixEnd_2369565 : Nat := 4983230072969 + 3 ^ 40 * 2369565 * 2
def baseEnd_2369565 : Nat := 405575262357042266580025

theorem tailTrace_2369565 : CollatzResearch.WordTrace tailWord_2369565 prefixEnd_2369565 405575262357042266580025 := by
  unfold tailWord_2369565
  simp only [CollatzResearch.WordTrace]
  refine ⟨86425135660478169328134149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57616757106985446218756099 86425135660478169328134149)
  ·
    refine ⟨16204712936339656749025153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86425135660478169328134149 16204712936339656749025153)
    ·
      refine ⟨12153534702254742561768865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16204712936339656749025153 12153534702254742561768865)
      ·
        refine ⟨9115151026691056921326649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12153534702254742561768865 9115151026691056921326649)
        ·
          refine ⟨6836363270018292690994987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9115151026691056921326649 6836363270018292690994987)
          ·
            refine ⟨10254544905027439036492481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6836363270018292690994987 10254544905027439036492481)
            ·
              refine ⟨7690908678770579277369361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10254544905027439036492481 7690908678770579277369361)
              ·
                refine ⟨5768181509077934458027021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7690908678770579277369361 5768181509077934458027021)
                ·
                  refine ⟨2163068065904225421760133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5768181509077934458027021 2163068065904225421760133)
                  ·
                    refine ⟨405575262357042266580025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2163068065904225421760133 405575262357042266580025)
                    ·
                      rfl

theorem cell23_2369565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 2, 3, 4].length) (baseStart_2369565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2369565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2369565 prefixEnd_2369565 := by exact prefixLift 2369565
  have htrace : WordTrace (prefixWord ++ tailWord_2369565) baseStart_2369565 baseEnd_2369565 := by
    simpa [prefixWord, tailWord_2369565, baseEnd_2369565] using wordTrace_append hprefix tailTrace_2369565
  have hstable : (prefixWord ++ tailWord_2369565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369565).length < 2 ^ (prefixWord ++ tailWord_2369565).sum := by decide
  have hdescent : baseEnd_2369565 < baseStart_2369565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369578 : List Nat := [3, 1, 4, 1, 2, 1, 1, 2, 8]
def baseStart_2369578 : Nat := 118140960795 + 2369578 * 2 ^ 59
def prefixEnd_2369578 : Nat := 4983230072969 + 3 ^ 40 * 2369578 * 2
def baseEnd_2369578 : Nat := 135192495813292805430835

theorem tailTrace_2369578 : CollatzResearch.WordTrace tailWord_2369578 prefixEnd_2369578 135192495813292805430835 := by
  unfold tailWord_2369578
  simp only [CollatzResearch.WordTrace]
  refine ⟨21606402452357768137089347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57617073206287381698904925 21606402452357768137089347)
  ·
    refine ⟨32409603678536652205634021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21606402452357768137089347 32409603678536652205634021)
    ·
      refine ⟨6076800689725622288556379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32409603678536652205634021 6076800689725622288556379)
      ·
        refine ⟨9115201034588433432834569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6076800689725622288556379 9115201034588433432834569)
        ·
          refine ⟨6836400775941325074625927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9115201034588433432834569 6836400775941325074625927)
          ·
            refine ⟨10254601163911987611938891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6836400775941325074625927 10254601163911987611938891)
            ·
              refine ⟨15381901745867981417908337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10254601163911987611938891 15381901745867981417908337)
              ·
                refine ⟨11536426309400986063431253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15381901745867981417908337 11536426309400986063431253)
                ·
                  refine ⟨135192495813292805430835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11536426309400986063431253 135192495813292805430835)
                  ·
                    rfl

theorem cell23_2369578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 2, 8].length) (baseStart_2369578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2369578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2369578 prefixEnd_2369578 := by exact prefixLift 2369578
  have htrace : WordTrace (prefixWord ++ tailWord_2369578) baseStart_2369578 baseEnd_2369578 := by
    simpa [prefixWord, tailWord_2369578, baseEnd_2369578] using wordTrace_append hprefix tailTrace_2369578
  have hstable : (prefixWord ++ tailWord_2369578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369578).length < 2 ^ (prefixWord ++ tailWord_2369578).sum := by decide
  have hdescent : baseEnd_2369578 < baseStart_2369578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369632 : List Nat := [2, 1, 1, 3, 2, 4, 2, 1, 2, 3, 2]
def baseStart_2369632 : Nat := 118140960795 + 2369632 * 2 ^ 59
def prefixEnd_2369632 : Nat := 4983230072969 + 3 ^ 40 * 2369632 * 2
def baseEnd_2369632 : Nat := 1216760190274978037602267

theorem tailTrace_2369632 : CollatzResearch.WordTrace tailWord_2369632 prefixEnd_2369632 1216760190274978037602267 := by
  unfold tailWord_2369632
  simp only [CollatzResearch.WordTrace]
  refine ⟨43213789675617719885411575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57618386234156959847215433 43213789675617719885411575)
  ·
    refine ⟨64820684513426579828117363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43213789675617719885411575 64820684513426579828117363)
    ·
      refine ⟨97231026770139869742176045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64820684513426579828117363 97231026770139869742176045)
      ·
        refine ⟨36461635038802451153316017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97231026770139869742176045 36461635038802451153316017)
        ·
          refine ⟨27346226279101838364987013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36461635038802451153316017 27346226279101838364987013)
          ·
            refine ⟨5127417427331594693435065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27346226279101838364987013 5127417427331594693435065)
            ·
              refine ⟨3845563070498696020076299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5127417427331594693435065 3845563070498696020076299)
              ·
                refine ⟨5768344605748044030114449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3845563070498696020076299 5768344605748044030114449)
                ·
                  refine ⟨4326258454311033022585837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5768344605748044030114449 4326258454311033022585837)
                  ·
                    refine ⟨1622346920366637383469689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4326258454311033022585837 1622346920366637383469689)
                    ·
                      refine ⟨1216760190274978037602267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1622346920366637383469689 1216760190274978037602267)
                      ·
                        rfl

theorem cell23_2369632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 1, 2, 3, 2].length) (baseStart_2369632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2369632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2369632 prefixEnd_2369632 := by exact prefixLift 2369632
  have htrace : WordTrace (prefixWord ++ tailWord_2369632) baseStart_2369632 baseEnd_2369632 := by
    simpa [prefixWord, tailWord_2369632, baseEnd_2369632] using wordTrace_append hprefix tailTrace_2369632
  have hstable : (prefixWord ++ tailWord_2369632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369632).length < 2 ^ (prefixWord ++ tailWord_2369632).sum := by decide
  have hdescent : baseEnd_2369632 < baseStart_2369632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369655 : List Nat := [1, 1, 3, 1, 1, 5, 1, 4, 2, 4]
def baseStart_2369655 : Nat := 118140960795 + 2369655 * 2 ^ 59
def prefixEnd_2369655 : Nat := 4983230072969 + 3 ^ 40 * 2369655 * 2
def baseEnd_2369655 : Nat := 405590666776677149204887

theorem tailTrace_2369655 : CollatzResearch.WordTrace tailWord_2369655 prefixEnd_2369655 405590666776677149204887 := by
  unfold tailWord_2369655
  simp only [CollatzResearch.WordTrace]
  refine ⟨86428418230152114698910419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57618945486768076465940279 86428418230152114698910419)
  ·
    refine ⟨129642627345228172048365629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86428418230152114698910419 129642627345228172048365629)
    ·
      refine ⟨48615985254460564518137111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129642627345228172048365629 48615985254460564518137111)
      ·
        refine ⟨72923977881690846777205667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48615985254460564518137111 72923977881690846777205667)
        ·
          refine ⟨109385966822536270165808501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72923977881690846777205667 109385966822536270165808501)
          ·
            refine ⟨10254934389612775328044547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 109385966822536270165808501 10254934389612775328044547)
            ·
              refine ⟨15382401584419162992066821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10254934389612775328044547 15382401584419162992066821)
              ·
                refine ⟨2884200297078593061012529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15382401584419162992066821 2884200297078593061012529)
                ·
                  refine ⟨2163150222808944795759397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2884200297078593061012529 2163150222808944795759397)
                  ·
                    refine ⟨405590666776677149204887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2163150222808944795759397 405590666776677149204887)
                    ·
                      rfl

theorem cell23_2369655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 4, 2, 4].length) (baseStart_2369655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2369655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2369655 prefixEnd_2369655 := by exact prefixLift 2369655
  have htrace : WordTrace (prefixWord ++ tailWord_2369655) baseStart_2369655 baseEnd_2369655 := by
    simpa [prefixWord, tailWord_2369655, baseEnd_2369655] using wordTrace_append hprefix tailTrace_2369655
  have hstable : (prefixWord ++ tailWord_2369655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369655).length < 2 ^ (prefixWord ++ tailWord_2369655).sum := by decide
  have hdescent : baseEnd_2369655 < baseStart_2369655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369672 : List Nat := [2, 1, 3, 4, 1, 1, 2, 3, 2, 4]
def baseStart_2369672 : Nat := 118140960795 + 2369672 * 2 ^ 59
def prefixEnd_2369672 : Nat := 4983230072969 + 3 ^ 40 * 2369672 * 2
def baseEnd_2369672 : Nat := 405593576500385960367361

theorem tailTrace_2369672 : CollatzResearch.WordTrace tailWord_2369672 prefixEnd_2369672 405593576500385960367361 := by
  unfold tailWord_2369672
  simp only [CollatzResearch.WordTrace]
  refine ⟨43214519135545263301139635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57619358847393684401519513 43214519135545263301139635)
  ·
    refine ⟨64821778703317894951709453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43214519135545263301139635 64821778703317894951709453)
    ·
      refine ⟨24308167013744210606891045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64821778703317894951709453 24308167013744210606891045)
      ·
        refine ⟨4557781315077039488792071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24308167013744210606891045 4557781315077039488792071)
        ·
          refine ⟨6836671972615559233188107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4557781315077039488792071 6836671972615559233188107)
          ·
            refine ⟨10255007958923338849782161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6836671972615559233188107 10255007958923338849782161)
            ·
              refine ⟨7691255969192504137336621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10255007958923338849782161 7691255969192504137336621)
              ·
                refine ⟨2884220988447189051501233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7691255969192504137336621 2884220988447189051501233)
                ·
                  refine ⟨2163165741335391788625925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2884220988447189051501233 2163165741335391788625925)
                  ·
                    refine ⟨405593576500385960367361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2163165741335391788625925 405593576500385960367361)
                    ·
                      rfl

theorem cell23_2369672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 3, 2, 4].length) (baseStart_2369672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2369672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2369672 prefixEnd_2369672 := by exact prefixLift 2369672
  have htrace : WordTrace (prefixWord ++ tailWord_2369672) baseStart_2369672 baseEnd_2369672 := by
    simpa [prefixWord, tailWord_2369672, baseEnd_2369672] using wordTrace_append hprefix tailTrace_2369672
  have hstable : (prefixWord ++ tailWord_2369672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369672).length < 2 ^ (prefixWord ++ tailWord_2369672).sum := by decide
  have hdescent : baseEnd_2369672 < baseStart_2369672 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369682 : List Nat := [3, 2, 3, 1, 1, 1, 2, 4, 1, 2, 3]
def baseStart_2369682 : Nat := 118140960795 + 2369682 * 2 ^ 59
def prefixEnd_2369682 : Nat := 4983230072969 + 3 ^ 40 * 2369682 * 2
def baseEnd_2369682 : Nat := 1216785864307702841977037

theorem tailTrace_2369682 : CollatzResearch.WordTrace tailWord_2369682 prefixEnd_2369682 1216785864307702841977037 := by
  unfold tailWord_2369682
  simp only [CollatzResearch.WordTrace]
  refine ⟨21607350750263574577535825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57619602000702865540095533 21607350750263574577535825)
  ·
    refine ⟨16205513062697680933151869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21607350750263574577535825 16205513062697680933151869)
    ·
      refine ⟨6077067398511630349931951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16205513062697680933151869 6077067398511630349931951)
      ·
        refine ⟨9115601097767445524897927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6077067398511630349931951 9115601097767445524897927)
        ·
          refine ⟨13673401646651168287346891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9115601097767445524897927 13673401646651168287346891)
          ·
            refine ⟨20510102469976752431020337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13673401646651168287346891 20510102469976752431020337)
            ·
              refine ⟨15382576852482564323265253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20510102469976752431020337 15382576852482564323265253)
              ·
                refine ⟨2884233159840480810612235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15382576852482564323265253 2884233159840480810612235)
                ·
                  refine ⟨4326349739760721215918353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2884233159840480810612235 4326349739760721215918353)
                  ·
                    refine ⟨3244762304820540911938765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4326349739760721215918353 3244762304820540911938765)
                    ·
                      refine ⟨1216785864307702841977037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3244762304820540911938765 1216785864307702841977037)
                      ·
                        rfl

theorem cell23_2369682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_2369682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2369682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2369682 prefixEnd_2369682 := by exact prefixLift 2369682
  have htrace : WordTrace (prefixWord ++ tailWord_2369682) baseStart_2369682 baseEnd_2369682 := by
    simpa [prefixWord, tailWord_2369682, baseEnd_2369682] using wordTrace_append hprefix tailTrace_2369682
  have hstable : (prefixWord ++ tailWord_2369682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369682).length < 2 ^ (prefixWord ++ tailWord_2369682).sum := by decide
  have hdescent : baseEnd_2369682 < baseStart_2369682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369696 : List Nat := [2, 1, 1, 4, 2, 3, 2, 3, 1, 2, 2]
def baseStart_2369696 : Nat := 118140960795 + 2369696 * 2 ^ 59
def prefixEnd_2369696 : Nat := 4983230072969 + 3 ^ 40 * 2369696 * 2
def baseEnd_2369696 : Nat := 1216793053036865787201973

theorem tailTrace_2369696 : CollatzResearch.WordTrace tailWord_2369696 prefixEnd_2369696 1216793053036865787201973 := by
  unfold tailWord_2369696
  simp only [CollatzResearch.WordTrace]
  refine ⟨43214956811501789350576471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57619942415335719134101961 43214956811501789350576471)
  ·
    refine ⟨64822435217252684025864707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43214956811501789350576471 64822435217252684025864707)
    ·
      refine ⟨97233652825879026038797061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64822435217252684025864707 97233652825879026038797061)
      ·
        refine ⟨18231309904852317382274449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 97233652825879026038797061 18231309904852317382274449)
        ·
          refine ⟨13673482428639238036705837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18231309904852317382274449 13673482428639238036705837)
          ·
            refine ⟨5127555910739714263764689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13673482428639238036705837 5127555910739714263764689)
            ·
              refine ⟨3845666933054785697823517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5127555910739714263764689 3845666933054785697823517)
              ·
                refine ⟨1442125099895544636683819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3845666933054785697823517 1442125099895544636683819)
                ·
                  refine ⟨2163187649843316955025729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1442125099895544636683819 2163187649843316955025729)
                  ·
                    refine ⟨1622390737382487716269297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2163187649843316955025729 1622390737382487716269297)
                    ·
                      refine ⟨1216793053036865787201973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1622390737382487716269297 1216793053036865787201973)
                      ·
                        rfl

theorem cell23_2369696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 3, 1, 2, 2].length) (baseStart_2369696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2369696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2369696 prefixEnd_2369696 := by exact prefixLift 2369696
  have htrace : WordTrace (prefixWord ++ tailWord_2369696) baseStart_2369696 baseEnd_2369696 := by
    simpa [prefixWord, tailWord_2369696, baseEnd_2369696] using wordTrace_append hprefix tailTrace_2369696
  have hstable : (prefixWord ++ tailWord_2369696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369696).length < 2 ^ (prefixWord ++ tailWord_2369696).sum := by decide
  have hdescent : baseEnd_2369696 < baseStart_2369696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369706 : List Nat := [3, 1, 5, 1, 2, 2, 1, 2, 2, 4]
def baseStart_2369706 : Nat := 118140960795 + 2369706 * 2 ^ 59
def prefixEnd_2369706 : Nat := 4983230072969 + 3 ^ 40 * 2369706 * 2
def baseEnd_2369706 : Nat := 405599395947803582692309

theorem tailTrace_2369706 : CollatzResearch.WordTrace tailWord_2369706 prefixEnd_2369706 405599395947803582692309 := by
  unfold tailWord_2369706
  simp only [CollatzResearch.WordTrace]
  refine ⟨21607569588241837602254243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57620185568644900272677981 21607569588241837602254243)
  ·
    refine ⟨32411354382362756403381365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21607569588241837602254243 32411354382362756403381365)
    ·
      refine ⟨3038564473346508412817003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32411354382362756403381365 3038564473346508412817003)
      ·
        refine ⟨4557846710019762619225505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3038564473346508412817003 4557846710019762619225505)
        ·
          refine ⟨3418385032514821964419129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4557846710019762619225505 3418385032514821964419129)
          ·
            refine ⟨2563788774386116473314347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3418385032514821964419129 2563788774386116473314347)
            ·
              refine ⟨3845683161579174709971521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2563788774386116473314347 3845683161579174709971521)
              ·
                refine ⟨2884262371184381032478641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3845683161579174709971521 2884262371184381032478641)
                ·
                  refine ⟨2163196778388285774358981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2884262371184381032478641 2163196778388285774358981)
                  ·
                    refine ⟨405599395947803582692309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2163196778388285774358981 405599395947803582692309)
                    ·
                      rfl

theorem cell23_2369706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_2369706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2369706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2369706 prefixEnd_2369706 := by exact prefixLift 2369706
  have htrace : WordTrace (prefixWord ++ tailWord_2369706) baseStart_2369706 baseEnd_2369706 := by
    simpa [prefixWord, tailWord_2369706, baseEnd_2369706] using wordTrace_append hprefix tailTrace_2369706
  have hstable : (prefixWord ++ tailWord_2369706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369706).length < 2 ^ (prefixWord ++ tailWord_2369706).sum := by decide
  have hdescent : baseEnd_2369706 < baseStart_2369706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369716 : List Nat := [2, 5, 3, 1, 1, 1, 1, 2, 1, 1, 5]
def baseStart_2369716 : Nat := 118140960795 + 2369716 * 2 ^ 59
def prefixEnd_2369716 : Nat := 4983230072969 + 3 ^ 40 * 2369716 * 2
def baseEnd_2369716 : Nat := 1216803322649955708951881

theorem tailTrace_2369716 : CollatzResearch.WordTrace tailWord_2369716 prefixEnd_2369716 1216803322649955708951881 := by
  unfold tailWord_2369716
  simp only [CollatzResearch.WordTrace]
  refine ⟨43215321541465561058440501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57620428721954081411254001 43215321541465561058440501)
  ·
    refine ⟨4051436394512396349228797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43215321541465561058440501 4051436394512396349228797)
    ·
      refine ⟨1519288647942148630960799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4051436394512396349228797 1519288647942148630960799)
      ·
        refine ⟨2278932971913222946441199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1519288647942148630960799 2278932971913222946441199)
        ·
          refine ⟨3418399457869834419661799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2278932971913222946441199 3418399457869834419661799)
          ·
            refine ⟨5127599186804751629492699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3418399457869834419661799 5127599186804751629492699)
            ·
              refine ⟨7691398780207127444239049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5127599186804751629492699 7691398780207127444239049)
              ·
                refine ⟨5768549085155345583179287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7691398780207127444239049 5768549085155345583179287)
                ·
                  refine ⟨8652823627733018374768931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5768549085155345583179287 8652823627733018374768931)
                  ·
                    refine ⟨12979235441599527562153397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8652823627733018374768931 12979235441599527562153397)
                    ·
                      refine ⟨1216803322649955708951881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12979235441599527562153397 1216803322649955708951881)
                      ·
                        rfl

theorem cell23_2369716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_2369716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2369716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2369716 prefixEnd_2369716 := by exact prefixLift 2369716
  have htrace : WordTrace (prefixWord ++ tailWord_2369716) baseStart_2369716 baseEnd_2369716 := by
    simpa [prefixWord, tailWord_2369716, baseEnd_2369716] using wordTrace_append hprefix tailTrace_2369716
  have hstable : (prefixWord ++ tailWord_2369716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369716).length < 2 ^ (prefixWord ++ tailWord_2369716).sum := by decide
  have hdescent : baseEnd_2369716 < baseStart_2369716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369775 : List Nat := [1, 1, 2, 1, 6, 1, 3, 1, 7]
def baseStart_2369775 : Nat := 118140960795 + 2369775 * 2 ^ 59
def prefixEnd_2369775 : Nat := 4983230072969 + 3 ^ 40 * 2369775 * 2
def baseEnd_2369775 : Nat := 135203735334285664234901

theorem tailTrace_2369775 : CollatzResearch.WordTrace tailWord_2369775 prefixEnd_2369775 135203735334285664234901 := by
  unfold tailWord_2369775
  simp only [CollatzResearch.WordTrace]
  refine ⟨86432794989717375193278779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57621863326478250128852519 86432794989717375193278779)
  ·
    refine ⟨129649192484576062789918169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86432794989717375193278779 129649192484576062789918169)
    ·
      refine ⟨97236894363432047092438627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129649192484576062789918169 97236894363432047092438627)
      ·
        refine ⟨145855341545148070638657941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97236894363432047092438627 145855341545148070638657941)
        ·
          refine ⟨6836969134928815811187091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 145855341545148070638657941 6836969134928815811187091)
          ·
            refine ⟨10255453702393223716780637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6836969134928815811187091 10255453702393223716780637)
            ·
              refine ⟨3845795138397458893792739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10255453702393223716780637 3845795138397458893792739)
              ·
                refine ⟨5768692707596188340689109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3845795138397458893792739 5768692707596188340689109)
                ·
                  refine ⟨135203735334285664234901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5768692707596188340689109 135203735334285664234901)
                  ·
                    rfl

theorem cell23_2369775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 1, 7].length) (baseStart_2369775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2369775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2369775 prefixEnd_2369775 := by exact prefixLift 2369775
  have htrace : WordTrace (prefixWord ++ tailWord_2369775) baseStart_2369775 baseEnd_2369775 := by
    simpa [prefixWord, tailWord_2369775, baseEnd_2369775] using wordTrace_append hprefix tailTrace_2369775
  have hstable : (prefixWord ++ tailWord_2369775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369775).length < 2 ^ (prefixWord ++ tailWord_2369775).sum := by decide
  have hdescent : baseEnd_2369775 < baseStart_2369775 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369786 : List Nat := [3, 1, 1, 1, 1, 5, 4, 1, 2, 2, 2]
def baseStart_2369786 : Nat := 118140960795 + 2369786 * 2 ^ 59
def prefixEnd_2369786 : Nat := 4983230072969 + 3 ^ 40 * 2369786 * 2
def baseEnd_2369786 : Nat := 1216839266295770435076559

theorem tailTrace_2369786 : CollatzResearch.WordTrace tailWord_2369786 prefixEnd_2369786 1216839266295770435076559 := by
  unfold tailWord_2369786
  simp only [CollatzResearch.WordTrace]
  refine ⟨21608299048169381017982303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57622130795118349381286141 21608299048169381017982303)
  ·
    refine ⟨32412448572254071526973455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21608299048169381017982303 32412448572254071526973455)
    ·
      refine ⟨48618672858381107290460183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32412448572254071526973455 48618672858381107290460183)
      ·
        refine ⟨72928009287571660935690275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48618672858381107290460183 72928009287571660935690275)
        ·
          refine ⟨109392013931357491403535413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72928009287571660935690275 109392013931357491403535413)
          ·
            refine ⟨10255501306064764819081445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 109392013931357491403535413 10255501306064764819081445)
            ·
              refine ⟨1922906494887143403577771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10255501306064764819081445 1922906494887143403577771)
              ·
                refine ⟨2884359742330715105366657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1922906494887143403577771 2884359742330715105366657)
                ·
                  refine ⟨2163269806748036329024993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2884359742330715105366657 2163269806748036329024993)
                  ·
                    refine ⟨1622452355061027246768745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2163269806748036329024993 1622452355061027246768745)
                    ·
                      refine ⟨1216839266295770435076559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1622452355061027246768745 1216839266295770435076559)
                      ·
                        rfl

theorem cell23_2369786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 4, 1, 2, 2, 2].length) (baseStart_2369786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2369786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2369786 prefixEnd_2369786 := by exact prefixLift 2369786
  have htrace : WordTrace (prefixWord ++ tailWord_2369786) baseStart_2369786 baseEnd_2369786 := by
    simpa [prefixWord, tailWord_2369786, baseEnd_2369786] using wordTrace_append hprefix tailTrace_2369786
  have hstable : (prefixWord ++ tailWord_2369786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369786).length < 2 ^ (prefixWord ++ tailWord_2369786).sum := by decide
  have hdescent : baseEnd_2369786 < baseStart_2369786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369815 : List Nat := [1, 1, 3, 4, 1, 2, 1, 2, 1, 2, 5]
def baseStart_2369815 : Nat := 118140960795 + 2369815 * 2 ^ 59
def prefixEnd_2369815 : Nat := 4983230072969 + 3 ^ 40 * 2369815 * 2
def baseEnd_2369815 : Nat := 1216854157234750821613925

theorem tailTrace_2369815 : CollatzResearch.WordTrace tailWord_2369815 prefixEnd_2369815 1216854157234750821613925 := by
  unfold tailWord_2369815
  simp only [CollatzResearch.WordTrace]
  refine ⟨86434253909572462024734899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57622835939714974683156599 86434253909572462024734899)
  ·
    refine ⟨129651380864358693037102349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86434253909572462024734899 129651380864358693037102349)
    ·
      refine ⟨48619267824134509888913381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129651380864358693037102349 48619267824134509888913381)
      ·
        refine ⟨9116112717025220604171259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48619267824134509888913381 9116112717025220604171259)
        ·
          refine ⟨13674169075537830906256889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9116112717025220604171259 13674169075537830906256889)
          ·
            refine ⟨10255626806653373179692667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13674169075537830906256889 10255626806653373179692667)
            ·
              refine ⟨15383440209980059769539001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10255626806653373179692667 15383440209980059769539001)
              ·
                refine ⟨11537580157485044827154251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15383440209980059769539001 11537580157485044827154251)
                ·
                  refine ⟨17306370236227567240731377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11537580157485044827154251 17306370236227567240731377)
                  ·
                    refine ⟨12979777677170675430548533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17306370236227567240731377 12979777677170675430548533)
                    ·
                      refine ⟨1216854157234750821613925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12979777677170675430548533 1216854157234750821613925)
                      ·
                        rfl

theorem cell23_2369815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_2369815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2369815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2369815 prefixEnd_2369815 := by exact prefixLift 2369815
  have htrace : WordTrace (prefixWord ++ tailWord_2369815) baseStart_2369815 baseEnd_2369815 := by
    simpa [prefixWord, tailWord_2369815, baseEnd_2369815] using wordTrace_append hprefix tailTrace_2369815
  have hstable : (prefixWord ++ tailWord_2369815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369815).length < 2 ^ (prefixWord ++ tailWord_2369815).sum := by decide
  have hdescent : baseEnd_2369815 < baseStart_2369815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369826 : List Nat := [3, 3, 1, 1, 3, 3, 2, 2, 5]
def baseStart_2369826 : Nat := 118140960795 + 2369826 * 2 ^ 59
def prefixEnd_2369826 : Nat := 4983230072969 + 3 ^ 40 * 2369826 * 2
def baseEnd_2369826 : Nat := 135206645057994475397375

theorem tailTrace_2369826 : CollatzResearch.WordTrace tailWord_2369826 prefixEnd_2369826 135206645057994475397375 := by
  unfold tailWord_2369826
  simp only [CollatzResearch.WordTrace]
  refine ⟨21608663778133152725846333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57623103408355073935590221 21608663778133152725846333)
  ·
    refine ⟨8103248916799932272192375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21608663778133152725846333 8103248916799932272192375)
    ·
      refine ⟨12154873375199898408288563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8103248916799932272192375 12154873375199898408288563)
      ·
        refine ⟨18232310062799847612432845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12154873375199898408288563 18232310062799847612432845)
        ·
          refine ⟨6837116273549942854662317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18232310062799847612432845 6837116273549942854662317)
          ·
            refine ⟨2563918602581228570498369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6837116273549942854662317 2563918602581228570498369)
            ·
              refine ⟨1922938951935921427873777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2563918602581228570498369 1922938951935921427873777)
              ·
                refine ⟨1442204213951941070905333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1922938951935921427873777 1442204213951941070905333)
                ·
                  refine ⟨135206645057994475397375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1442204213951941070905333 135206645057994475397375)
                  ·
                    rfl

theorem cell23_2369826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 2, 2, 5].length) (baseStart_2369826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2369826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2369826 prefixEnd_2369826 := by exact prefixLift 2369826
  have htrace : WordTrace (prefixWord ++ tailWord_2369826) baseStart_2369826 baseEnd_2369826 := by
    simpa [prefixWord, tailWord_2369826, baseEnd_2369826] using wordTrace_append hprefix tailTrace_2369826
  have hstable : (prefixWord ++ tailWord_2369826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369826).length < 2 ^ (prefixWord ++ tailWord_2369826).sum := by decide
  have hdescent : baseEnd_2369826 < baseStart_2369826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369852 : List Nat := [2, 2, 2, 2, 1, 2, 3, 2, 3, 4]
def baseStart_2369852 : Nat := 118140960795 + 2369852 * 2 ^ 59
def prefixEnd_2369852 : Nat := 4983230072969 + 3 ^ 40 * 2369852 * 2
def baseEnd_2369852 : Nat := 405624385339655725617085

theorem tailTrace_2369852 : CollatzResearch.WordTrace tailWord_2369852 prefixEnd_2369852 405624385339655725617085 := by
  unfold tailWord_2369852
  simp only [CollatzResearch.WordTrace]
  refine ⟨43217801705219208671915905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57623735606958944895887873 43217801705219208671915905)
  ·
    refine ⟨32413351278914406503936929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43217801705219208671915905 32413351278914406503936929)
    ·
      refine ⟨24310013459185804877952697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32413351278914406503936929 24310013459185804877952697)
      ·
        refine ⟨18232510094389353658464523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24310013459185804877952697 18232510094389353658464523)
        ·
          refine ⟨27348765141584030487696785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18232510094389353658464523 27348765141584030487696785)
          ·
            refine ⟨20511573856188022865772589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27348765141584030487696785 20511573856188022865772589)
            ·
              refine ⟨7691840196070508574664721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20511573856188022865772589 7691840196070508574664721)
              ·
                refine ⟨5768880147052881430998541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7691840196070508574664721 5768880147052881430998541)
                ·
                  refine ⟨2163330055144830536624453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5768880147052881430998541 2163330055144830536624453)
                  ·
                    refine ⟨405624385339655725617085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2163330055144830536624453 405624385339655725617085)
                    ·
                      rfl

theorem cell23_2369852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 2, 3, 4].length) (baseStart_2369852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2369852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2369852 prefixEnd_2369852 := by exact prefixLift 2369852
  have htrace : WordTrace (prefixWord ++ tailWord_2369852) baseStart_2369852 baseEnd_2369852 := by
    simpa [prefixWord, tailWord_2369852, baseEnd_2369852] using wordTrace_append hprefix tailTrace_2369852
  have hstable : (prefixWord ++ tailWord_2369852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369852).length < 2 ^ (prefixWord ++ tailWord_2369852).sum := by decide
  have hdescent : baseEnd_2369852 < baseStart_2369852 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369925 : List Nat := [1, 3, 1, 1, 3, 1, 1, 3, 3, 6]
def baseStart_2369925 : Nat := 118140960795 + 2369925 * 2 ^ 59
def prefixEnd_2369925 : Nat := 4983230072969 + 3 ^ 40 * 2369925 * 2
def baseEnd_2369925 : Nat := 405636880035581797079473

theorem tailTrace_2369925 : CollatzResearch.WordTrace tailWord_2369925 prefixEnd_2369925 405636880035581797079473 := by
  unfold tailWord_2369925
  simp only [CollatzResearch.WordTrace]
  refine ⟨86438265939173950811239229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57625510626115967207492819 86438265939173950811239229)
  ·
    refine ⟨32414349727190231554214711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86438265939173950811239229 32414349727190231554214711)
    ·
      refine ⟨48621524590785347331322067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32414349727190231554214711 48621524590785347331322067)
      ·
        refine ⟨72932286886178020996983101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48621524590785347331322067 72932286886178020996983101)
        ·
          refine ⟨27349607582316757873868663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72932286886178020996983101 27349607582316757873868663)
          ·
            refine ⟨41024411373475136810802995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27349607582316757873868663 41024411373475136810802995)
            ·
              refine ⟨61536617060212705216204493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41024411373475136810802995 61536617060212705216204493)
              ·
                refine ⟨23076231397579764456076685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61536617060212705216204493 23076231397579764456076685)
                ·
                  refine ⟨8653586774092411671028757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23076231397579764456076685 8653586774092411671028757)
                  ·
                    refine ⟨405636880035581797079473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8653586774092411671028757 405636880035581797079473)
                    ·
                      rfl

theorem cell23_2369925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 3, 6].length) (baseStart_2369925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2369925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2369925 prefixEnd_2369925 := by exact prefixLift 2369925
  have htrace : WordTrace (prefixWord ++ tailWord_2369925) baseStart_2369925 baseEnd_2369925 := by
    simpa [prefixWord, tailWord_2369925, baseEnd_2369925] using wordTrace_append hprefix tailTrace_2369925
  have hstable : (prefixWord ++ tailWord_2369925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369925).length < 2 ^ (prefixWord ++ tailWord_2369925).sum := by decide
  have hdescent : baseEnd_2369925 < baseStart_2369925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369945 : List Nat := [1, 2, 1, 2, 1, 4, 1, 1, 3, 1, 6]
def baseStart_2369945 : Nat := 118140960795 + 2369945 * 2 ^ 59
def prefixEnd_2369945 : Nat := 4983230072969 + 3 ^ 40 * 2369945 * 2
def baseEnd_2369945 : Nat := 1216920909719835312988327

theorem tailTrace_2369945 : CollatzResearch.WordTrace tailWord_2369945 prefixEnd_2369945 1216920909719835312988327 := by
  unfold tailWord_2369945
  simp only [CollatzResearch.WordTrace]
  refine ⟨86438995399101494226967289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57625996932734329484644859 86438995399101494226967289)
  ·
    refine ⟨64829246549326120670225467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86438995399101494226967289 64829246549326120670225467)
    ·
      refine ⟨97243869823989181005338201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64829246549326120670225467 97243869823989181005338201)
      ·
        refine ⟨72932902367991885754003651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97243869823989181005338201 72932902367991885754003651)
        ·
          refine ⟨109399353551987828631005477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72932902367991885754003651 109399353551987828631005477)
          ·
            refine ⟨20512378790997717868313527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 109399353551987828631005477 20512378790997717868313527)
            ·
              refine ⟨30768568186496576802470291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20512378790997717868313527 30768568186496576802470291)
              ·
                refine ⟨46152852279744865203705437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30768568186496576802470291 46152852279744865203705437)
                ·
                  refine ⟨17307319604904324451389539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46152852279744865203705437 17307319604904324451389539)
                  ·
                    refine ⟨25960979407356486677084309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17307319604904324451389539 25960979407356486677084309)
                    ·
                      refine ⟨1216920909719835312988327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25960979407356486677084309 1216920909719835312988327)
                      ·
                        rfl

theorem cell23_2369945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3, 1, 6].length) (baseStart_2369945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2369945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2369945 prefixEnd_2369945 := by exact prefixLift 2369945
  have htrace : WordTrace (prefixWord ++ tailWord_2369945) baseStart_2369945 baseEnd_2369945 := by
    simpa [prefixWord, tailWord_2369945, baseEnd_2369945] using wordTrace_append hprefix tailTrace_2369945
  have hstable : (prefixWord ++ tailWord_2369945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369945).length < 2 ^ (prefixWord ++ tailWord_2369945).sum := by decide
  have hdescent : baseEnd_2369945 < baseStart_2369945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369952 : List Nat := [2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 5]
def baseStart_2369952 : Nat := 118140960795 + 2369952 * 2 ^ 59
def prefixEnd_2369952 : Nat := 4983230072969 + 3 ^ 40 * 2369952 * 2
def baseEnd_2369952 : Nat := 1216924504084416785600795

theorem tailTrace_2369952 : CollatzResearch.WordTrace tailWord_2369952 prefixEnd_2369952 1216924504084416785600795 := by
  unfold tailWord_2369952
  simp only [CollatzResearch.WordTrace]
  refine ⟨43219625355038067211236055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57626167140050756281648073 43219625355038067211236055)
  ·
    refine ⟨64829438032557100816854083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43219625355038067211236055 64829438032557100816854083)
    ·
      refine ⟨97244157048835651225281125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64829438032557100816854083 97244157048835651225281125)
      ·
        refine ⟨18233279446656684604740211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 97244157048835651225281125 18233279446656684604740211)
        ·
          refine ⟨27349919169985026907110317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18233279446656684604740211 27349919169985026907110317)
          ·
            refine ⟨10256219688744385090166369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27349919169985026907110317 10256219688744385090166369)
            ·
              refine ⟨7692164766558288817624777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10256219688744385090166369 7692164766558288817624777)
              ·
                refine ⟨5769123574918716613218583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7692164766558288817624777 5769123574918716613218583)
                ·
                  refine ⟨8653685362378074919827875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5769123574918716613218583 8653685362378074919827875)
                  ·
                    refine ⟨12980528043567112379741813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8653685362378074919827875 12980528043567112379741813)
                    ·
                      refine ⟨1216924504084416785600795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12980528043567112379741813 1216924504084416785600795)
                      ·
                        rfl

theorem cell23_2369952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_2369952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2369952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2369952 prefixEnd_2369952 := by exact prefixLift 2369952
  have htrace : WordTrace (prefixWord ++ tailWord_2369952) baseStart_2369952 baseEnd_2369952 := by
    simpa [prefixWord, tailWord_2369952, baseEnd_2369952] using wordTrace_append hprefix tailTrace_2369952
  have hstable : (prefixWord ++ tailWord_2369952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369952).length < 2 ^ (prefixWord ++ tailWord_2369952).sum := by decide
  have hdescent : baseEnd_2369952 < baseStart_2369952 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369955 : List Nat := [1, 1, 1, 4, 1, 4, 1, 10]
def baseStart_2369955 : Nat := 118140960795 + 2369955 * 2 ^ 59
def prefixEnd_2369955 : Nat := 4983230072969 + 3 ^ 40 * 2369955 * 2
def baseEnd_2369955 : Nat := 45071334982458528661603

theorem tailTrace_2369955 : CollatzResearch.WordTrace tailWord_2369955 prefixEnd_2369955 45071334982458528661603 := by
  unfold tailWord_2369955
  simp only [CollatzResearch.WordTrace]
  refine ⟨86439360129065265934831319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57626240086043510623220879 86439360129065265934831319)
  ·
    refine ⟨129659040193597898902246979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86439360129065265934831319 129659040193597898902246979)
    ·
      refine ⟨194488560290396848353370469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129659040193597898902246979 194488560290396848353370469)
      ·
        refine ⟨36466605054449409066256963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 194488560290396848353370469 36466605054449409066256963)
        ·
          refine ⟨54699907581674113599385445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36466605054449409066256963 54699907581674113599385445)
          ·
            refine ⟨10256232671563896299884771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54699907581674113599385445 10256232671563896299884771)
            ·
              refine ⟨15384349007345844449827157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10256232671563896299884771 15384349007345844449827157)
              ·
                refine ⟨45071334982458528661603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 15384349007345844449827157 45071334982458528661603)
                ·
                  rfl

theorem cell23_2369955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 10].length) (baseStart_2369955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2369955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2369955 prefixEnd_2369955 := by exact prefixLift 2369955
  have htrace : WordTrace (prefixWord ++ tailWord_2369955) baseStart_2369955 baseEnd_2369955 := by
    simpa [prefixWord, tailWord_2369955, baseEnd_2369955] using wordTrace_append hprefix tailTrace_2369955
  have hstable : (prefixWord ++ tailWord_2369955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369955).length < 2 ^ (prefixWord ++ tailWord_2369955).sum := by decide
  have hdescent : baseEnd_2369955 < baseStart_2369955 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2369969 : List Nat := [1, 2, 2, 4, 1, 3, 1, 1, 3, 2, 3]
def baseStart_2369969 : Nat := 118140960795 + 2369969 * 2 ^ 59
def prefixEnd_2369969 : Nat := 4983230072969 + 3 ^ 40 * 2369969 * 2
def baseEnd_2369969 : Nat := 1216933233255543219088217

theorem tailTrace_2369969 : CollatzResearch.WordTrace tailWord_2369969 prefixEnd_2369969 1216933233255543219088217 := by
  unfold tailWord_2369969
  simp only [CollatzResearch.WordTrace]
  refine ⟨86439870751014546325840961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57626580500676364217227307 86439870751014546325840961)
  ·
    refine ⟨64829903063260909744380721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86439870751014546325840961 64829903063260909744380721)
    ·
      refine ⟨48622427297445682308285541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64829903063260909744380721 48622427297445682308285541)
      ·
        refine ⟨9116705118271065432803539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48622427297445682308285541 9116705118271065432803539)
        ·
          refine ⟨13675057677406598149205309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9116705118271065432803539 13675057677406598149205309)
          ·
            refine ⟨5128146629027474305951991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13675057677406598149205309 5128146629027474305951991)
            ·
              refine ⟨7692219943541211458927987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5128146629027474305951991 7692219943541211458927987)
              ·
                refine ⟨11538329915311817188391981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7692219943541211458927987 11538329915311817188391981)
                ·
                  refine ⟨4326873718241931445646993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11538329915311817188391981 4326873718241931445646993)
                  ·
                    refine ⟨3245155288681448584235245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4326873718241931445646993 3245155288681448584235245)
                    ·
                      refine ⟨1216933233255543219088217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3245155288681448584235245 1216933233255543219088217)
                      ·
                        rfl

theorem cell23_2369969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_2369969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2369969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2369969 prefixEnd_2369969 := by exact prefixLift 2369969
  have htrace : WordTrace (prefixWord ++ tailWord_2369969) baseStart_2369969 baseEnd_2369969 := by
    simpa [prefixWord, tailWord_2369969, baseEnd_2369969] using wordTrace_append hprefix tailTrace_2369969
  have hstable : (prefixWord ++ tailWord_2369969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2369969).length < 2 ^ (prefixWord ++ tailWord_2369969).sum := by decide
  have hdescent : baseEnd_2369969 < baseStart_2369969 := by decide
  rcases family_descends (prefixWord ++ tailWord_2369969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2370009 : List Nat := [1, 2, 1, 2, 4, 1, 1, 1, 5, 3, 2]
def baseStart_2370009 : Nat := 118140960795 + 2370009 * 2 ^ 59
def prefixEnd_2370009 : Nat := 4983230072969 + 3 ^ 40 * 2370009 * 2
def baseEnd_2370009 : Nat := 1216953772481723062588033

theorem tailTrace_2370009 : CollatzResearch.WordTrace tailWord_2370009 prefixEnd_2370009 1216953772481723062588033 := by
  unfold tailWord_2370009
  simp only [CollatzResearch.WordTrace]
  refine ⟨86441329670869633157297081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57627553113913088771531387 86441329670869633157297081)
  ·
    refine ⟨64830997253152224867972811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86441329670869633157297081 64830997253152224867972811)
    ·
      refine ⟨97246495879728337301959217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64830997253152224867972811 97246495879728337301959217)
      ·
        refine ⟨72934871909796252976469413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97246495879728337301959217 72934871909796252976469413)
        ·
          refine ⟨13675288483086797433088015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72934871909796252976469413 13675288483086797433088015)
          ·
            refine ⟨20512932724630196149632023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13675288483086797433088015 20512932724630196149632023)
            ·
              refine ⟨30769399086945294224448035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20512932724630196149632023 30769399086945294224448035)
              ·
                refine ⟨46154098630417941336672053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30769399086945294224448035 46154098630417941336672053)
                ·
                  refine ⟨4326946746601682000313005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46154098630417941336672053 4326946746601682000313005)
                  ·
                    refine ⟨1622605029975630750117377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4326946746601682000313005 1622605029975630750117377)
                    ·
                      refine ⟨1216953772481723062588033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1622605029975630750117377 1216953772481723062588033)
                      ·
                        rfl

theorem cell23_2370009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 5, 3, 2].length) (baseStart_2370009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2370009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2370009 prefixEnd_2370009 := by exact prefixLift 2370009
  have htrace : WordTrace (prefixWord ++ tailWord_2370009) baseStart_2370009 baseEnd_2370009 := by
    simpa [prefixWord, tailWord_2370009, baseEnd_2370009] using wordTrace_append hprefix tailTrace_2370009
  have hstable : (prefixWord ++ tailWord_2370009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2370009).length < 2 ^ (prefixWord ++ tailWord_2370009).sum := by decide
  have hdescent : baseEnd_2370009 < baseStart_2370009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2370009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2370026 : List Nat := [3, 1, 3, 1, 3, 1, 2, 1, 3, 3, 2]
def baseStart_2370026 : Nat := 118140960795 + 2370026 * 2 ^ 59
def prefixEnd_2370026 : Nat := 4983230072969 + 3 ^ 40 * 2370026 * 2
def baseEnd_2370026 : Nat := 1216962501652849496075455

theorem tailTrace_2370026 : CollatzResearch.WordTrace tailWord_2370026 prefixEnd_2370026 1216962501652849496075455 := by
  unfold tailWord_2370026
  simp only [CollatzResearch.WordTrace]
  refine ⟨21610487427952011265166483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57627966474538696707110621 21610487427952011265166483)
  ·
    refine ⟨32415731141928016897749725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21610487427952011265166483 32415731141928016897749725)
    ·
      refine ⟨12155899178223006336656147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32415731141928016897749725 12155899178223006336656147)
      ·
        refine ⟨18233848767334509504984221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12155899178223006336656147 18233848767334509504984221)
        ·
          refine ⟨6837693287750441064369083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18233848767334509504984221 6837693287750441064369083)
          ·
            refine ⟨10256539931625661596553625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6837693287750441064369083 10256539931625661596553625)
            ·
              refine ⟨7692404948719246197415219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10256539931625661596553625 7692404948719246197415219)
              ·
                refine ⟨11538607423078869296122829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7692404948719246197415219 11538607423078869296122829)
                ·
                  refine ⟨4326977783654575986046061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11538607423078869296122829 4326977783654575986046061)
                  ·
                    refine ⟨1622616668870465994767273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4326977783654575986046061 1622616668870465994767273)
                    ·
                      refine ⟨1216962501652849496075455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1622616668870465994767273 1216962501652849496075455)
                      ·
                        rfl

theorem cell23_2370026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 1, 3, 3, 2].length) (baseStart_2370026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2370026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2370026 prefixEnd_2370026 := by exact prefixLift 2370026
  have htrace : WordTrace (prefixWord ++ tailWord_2370026) baseStart_2370026 baseEnd_2370026 := by
    simpa [prefixWord, tailWord_2370026, baseEnd_2370026] using wordTrace_append hprefix tailTrace_2370026
  have hstable : (prefixWord ++ tailWord_2370026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2370026).length < 2 ^ (prefixWord ++ tailWord_2370026).sum := by decide
  have hdescent : baseEnd_2370026 < baseStart_2370026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2370026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2370037 : List Nat := [1, 3, 5, 1, 3, 1, 2, 1, 1, 2, 3]
def baseStart_2370037 : Nat := 118140960795 + 2370037 * 2 ^ 59
def prefixEnd_2370037 : Nat := 4983230072969 + 3 ^ 40 * 2370037 * 2
def baseEnd_2370037 : Nat := 1216968149940048953037905

theorem tailTrace_2370037 : CollatzResearch.WordTrace tailWord_2370037 prefixEnd_2370037 1216968149940048953037905 := by
  unfold tailWord_2370037
  simp only [CollatzResearch.WordTrace]
  refine ⟨86442350914768193939316365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57628233943178795959544243 86442350914768193939316365)
  ·
    refine ⟨32415881593038072727243637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86442350914768193939316365 32415881593038072727243637)
    ·
      refine ⟨3038988899347319318179091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32415881593038072727243637 3038988899347319318179091)
      ·
        refine ⟨4558483349020978977268637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3038988899347319318179091 4558483349020978977268637)
        ·
          refine ⟨1709431255882867116475739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4558483349020978977268637 1709431255882867116475739)
          ·
            refine ⟨2564146883824300674713609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1709431255882867116475739 2564146883824300674713609)
            ·
              refine ⟨1923110162868225506035207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2564146883824300674713609 1923110162868225506035207)
              ·
                refine ⟨2884665244302338259052811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1923110162868225506035207 2884665244302338259052811)
                ·
                  refine ⟨4326997866453507388579217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2884665244302338259052811 4326997866453507388579217)
                  ·
                    refine ⟨3245248399840130541434413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4326997866453507388579217 3245248399840130541434413)
                    ·
                      refine ⟨1216968149940048953037905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3245248399840130541434413 1216968149940048953037905)
                      ·
                        rfl

theorem cell23_2370037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_2370037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2370037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2370037 prefixEnd_2370037 := by exact prefixLift 2370037
  have htrace : WordTrace (prefixWord ++ tailWord_2370037) baseStart_2370037 baseEnd_2370037 := by
    simpa [prefixWord, tailWord_2370037, baseEnd_2370037] using wordTrace_append hprefix tailTrace_2370037
  have hstable : (prefixWord ++ tailWord_2370037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2370037).length < 2 ^ (prefixWord ++ tailWord_2370037).sum := by decide
  have hdescent : baseEnd_2370037 < baseStart_2370037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2370037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2370042 : List Nat := [3, 1, 1, 1, 1, 2, 2, 2, 1, 6, 3]
def baseStart_2370042 : Nat := 118140960795 + 2370042 * 2 ^ 59
def prefixEnd_2370042 : Nat := 4983230072969 + 3 ^ 40 * 2370042 * 2
def baseEnd_2370042 : Nat := 1216970717343321433475381

theorem tailTrace_2370042 : CollatzResearch.WordTrace tailWord_2370042 prefixEnd_2370042 1216970717343321433475381 := by
  unfold tailWord_2370042
  simp only [CollatzResearch.WordTrace]
  refine ⟨21610633319937519948312095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57628355519833386528832253 21610633319937519948312095)
  ·
    refine ⟨32415949979906279922468143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21610633319937519948312095 32415949979906279922468143)
    ·
      refine ⟨48623924969859419883702215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32415949979906279922468143 48623924969859419883702215)
      ·
        refine ⟨72935887454789129825553323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48623924969859419883702215 72935887454789129825553323)
        ·
          refine ⟨109403831182183694738329985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72935887454789129825553323 109403831182183694738329985)
          ·
            refine ⟨82052873386637771053747489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109403831182183694738329985 82052873386637771053747489)
            ·
              refine ⟨61539655039978328290310617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82052873386637771053747489 61539655039978328290310617)
              ·
                refine ⟨46154741279983746217732963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61539655039978328290310617 46154741279983746217732963)
                ·
                  refine ⟨69232111919975619326599445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46154741279983746217732963 69232111919975619326599445)
                  ·
                    refine ⟨3245255246248857155934349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 69232111919975619326599445 3245255246248857155934349)
                    ·
                      refine ⟨1216970717343321433475381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3245255246248857155934349 1216970717343321433475381)
                      ·
                        rfl

theorem cell23_2370042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 1, 6, 3].length) (baseStart_2370042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2370042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2370042 prefixEnd_2370042 := by exact prefixLift 2370042
  have htrace : WordTrace (prefixWord ++ tailWord_2370042) baseStart_2370042 baseEnd_2370042 := by
    simpa [prefixWord, tailWord_2370042, baseEnd_2370042] using wordTrace_append hprefix tailTrace_2370042
  have hstable : (prefixWord ++ tailWord_2370042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2370042).length < 2 ^ (prefixWord ++ tailWord_2370042).sum := by decide
  have hdescent : baseEnd_2370042 < baseStart_2370042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2370042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2370092 : List Nat := [2, 2, 1, 1, 1, 2, 1, 2, 6, 5]
def baseStart_2370092 : Nat := 118140960795 + 2370092 * 2 ^ 59
def prefixEnd_2370092 : Nat := 4983230072969 + 3 ^ 40 * 2370092 * 2
def baseEnd_2370092 : Nat := 405665463792015412616717

theorem tailTrace_2370092 : CollatzResearch.WordTrace tailWord_2370092 prefixEnd_2370092 405665463792015412616717 := by
  unfold tailWord_2370092
  simp only [CollatzResearch.WordTrace]
  refine ⟨43222178464784469166284265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57629571286379292221712353 43222178464784469166284265)
  ·
    refine ⟨32416633848588351874713199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43222178464784469166284265 32416633848588351874713199)
    ·
      refine ⟨48624950772882527812069799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32416633848588351874713199 48624950772882527812069799)
      ·
        refine ⟨72937426159323791718104699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48624950772882527812069799 72937426159323791718104699)
        ·
          refine ⟨109406139238985687577157049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72937426159323791718104699 109406139238985687577157049)
          ·
            refine ⟨82054604429239265682867787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109406139238985687577157049 82054604429239265682867787)
            ·
              refine ⟨123081906643858898524301681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82054604429239265682867787 123081906643858898524301681)
              ·
                refine ⟨92311429982894173893226261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 123081906643858898524301681 92311429982894173893226261)
                ·
                  refine ⟨4327098280448164401244981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 92311429982894173893226261 4327098280448164401244981)
                  ·
                    refine ⟨405665463792015412616717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4327098280448164401244981 405665463792015412616717)
                    ·
                      rfl

theorem cell23_2370092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 5].length) (baseStart_2370092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2370092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2370092 prefixEnd_2370092 := by exact prefixLift 2370092
  have htrace : WordTrace (prefixWord ++ tailWord_2370092) baseStart_2370092 baseEnd_2370092 := by
    simpa [prefixWord, tailWord_2370092, baseEnd_2370092] using wordTrace_append hprefix tailTrace_2370092
  have hstable : (prefixWord ++ tailWord_2370092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2370092).length < 2 ^ (prefixWord ++ tailWord_2370092).sum := by decide
  have hdescent : baseEnd_2370092 < baseStart_2370092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2370092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2370109 : List Nat := [1, 4, 1, 3, 2, 1, 1, 1, 4, 5]
def baseStart_2370109 : Nat := 118140960795 + 2370109 * 2 ^ 59
def prefixEnd_2370109 : Nat := 4983230072969 + 3 ^ 40 * 2370109 * 2
def baseEnd_2370109 : Nat := 405668373515724223779191

theorem tailTrace_2370109 : CollatzResearch.WordTrace tailWord_2370109 prefixEnd_2370109 405668373515724223779191 := by
  unfold tailWord_2370109
  simp only [CollatzResearch.WordTrace]
  refine ⟨86444976970507350235937381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57629984647004900157291587 86444976970507350235937381)
  ·
    refine ⟨16208433181970128169238259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86444976970507350235937381 16208433181970128169238259)
    ·
      refine ⟨24312649772955192253857389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16208433181970128169238259 24312649772955192253857389)
      ·
        refine ⟨9117243664858197095196521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24312649772955192253857389 9117243664858197095196521)
        ·
          refine ⟨6837932748643647821397391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9117243664858197095196521 6837932748643647821397391)
          ·
            refine ⟨10256899122965471732096087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6837932748643647821397391 10256899122965471732096087)
            ·
              refine ⟨15385348684448207598144131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10256899122965471732096087 15385348684448207598144131)
              ·
                refine ⟨23078023026672311397216197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15385348684448207598144131 23078023026672311397216197)
                ·
                  refine ⟨4327129317501058386978037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23078023026672311397216197 4327129317501058386978037)
                  ·
                    refine ⟨405668373515724223779191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4327129317501058386978037 405668373515724223779191)
                    ·
                      rfl

theorem cell23_2370109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 4, 5].length) (baseStart_2370109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2370109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2370109 prefixEnd_2370109 := by exact prefixLift 2370109
  have htrace : WordTrace (prefixWord ++ tailWord_2370109) baseStart_2370109 baseEnd_2370109 := by
    simpa [prefixWord, tailWord_2370109, baseEnd_2370109] using wordTrace_append hprefix tailTrace_2370109
  have hstable : (prefixWord ++ tailWord_2370109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2370109).length < 2 ^ (prefixWord ++ tailWord_2370109).sum := by decide
  have hdescent : baseEnd_2370109 < baseStart_2370109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2370109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2370113 : List Nat := [1, 2, 5, 1, 1, 3, 3, 2, 5]
def baseStart_2370113 : Nat := 118140960795 + 2370113 * 2 ^ 59
def prefixEnd_2370113 : Nat := 4983230072969 + 3 ^ 40 * 2370113 * 2
def baseEnd_2370113 : Nat := 135223019385532295076395

theorem tailTrace_2370113 : CollatzResearch.WordTrace tailWord_2370113 prefixEnd_2370113 135223019385532295076395 := by
  unfold tailWord_2370113
  simp only [CollatzResearch.WordTrace]
  refine ⟨86445122862492858919082993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57630081908328572612721995 86445122862492858919082993)
  ·
    refine ⟨64833842146869644189312245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86445122862492858919082993 64833842146869644189312245)
    ·
      refine ⟨6078172701269029142748023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 64833842146869644189312245 6078172701269029142748023)
      ·
        refine ⟨9117259051903543714122035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6078172701269029142748023 9117259051903543714122035)
        ·
          refine ⟨13675888577855315571183053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9117259051903543714122035 13675888577855315571183053)
          ·
            refine ⟨5128458216695743339193645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13675888577855315571183053 5128458216695743339193645)
            ·
              refine ⟨1923171831260903752197617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5128458216695743339193645 1923171831260903752197617)
              ·
                refine ⟨1442378873445677814148213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1923171831260903752197617 1442378873445677814148213)
                ·
                  refine ⟨135223019385532295076395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1442378873445677814148213 135223019385532295076395)
                  ·
                    rfl

theorem cell23_2370113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 3, 2, 5].length) (baseStart_2370113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2370113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2370113 prefixEnd_2370113 := by exact prefixLift 2370113
  have htrace : WordTrace (prefixWord ++ tailWord_2370113) baseStart_2370113 baseEnd_2370113 := by
    simpa [prefixWord, tailWord_2370113, baseEnd_2370113] using wordTrace_append hprefix tailTrace_2370113
  have hstable : (prefixWord ++ tailWord_2370113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2370113).length < 2 ^ (prefixWord ++ tailWord_2370113).sum := by decide
  have hdescent : baseEnd_2370113 < baseStart_2370113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2370113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2370119 : List Nat := [1, 1, 4, 1, 4, 2, 1, 1, 1, 2, 5]
def baseStart_2370119 : Nat := 118140960795 + 2370119 * 2 ^ 59
def prefixEnd_2370119 : Nat := 4983230072969 + 3 ^ 40 * 2370119 * 2
def baseEnd_2370119 : Nat := 1217010255353717632212527

theorem tailTrace_2370119 : CollatzResearch.WordTrace tailWord_2370119 prefixEnd_2370119 1217010255353717632212527 := by
  unfold tailWord_2370119
  simp only [CollatzResearch.WordTrace]
  refine ⟨86445341700471121943801411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57630227800314081295867607 86445341700471121943801411)
  ·
    refine ⟨129668012550706682915702117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86445341700471121943801411 129668012550706682915702117)
    ·
      refine ⟨24312752353257503046694147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 129668012550706682915702117 24312752353257503046694147)
      ·
        refine ⟨36469128529886254570041221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24312752353257503046694147 36469128529886254570041221)
        ·
          refine ⟨6837961599353672731882729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36469128529886254570041221 6837961599353672731882729)
          ·
            refine ⟨5128471199515254548912047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6837961599353672731882729 5128471199515254548912047)
            ·
              refine ⟨7692706799272881823368071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5128471199515254548912047 7692706799272881823368071)
              ·
                refine ⟨11539060198909322735052107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7692706799272881823368071 11539060198909322735052107)
                ·
                  refine ⟨17308590298363984102578161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11539060198909322735052107 17308590298363984102578161)
                  ·
                    refine ⟨12981442723772988076933621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17308590298363984102578161 12981442723772988076933621)
                    ·
                      refine ⟨1217010255353717632212527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12981442723772988076933621 1217010255353717632212527)
                      ·
                        rfl

theorem cell23_2370119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 1, 1, 2, 5].length) (baseStart_2370119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2370119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2370119 prefixEnd_2370119 := by exact prefixLift 2370119
  have htrace : WordTrace (prefixWord ++ tailWord_2370119) baseStart_2370119 baseEnd_2370119 := by
    simpa [prefixWord, tailWord_2370119, baseEnd_2370119] using wordTrace_append hprefix tailTrace_2370119
  have hstable : (prefixWord ++ tailWord_2370119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2370119).length < 2 ^ (prefixWord ++ tailWord_2370119).sum := by decide
  have hdescent : baseEnd_2370119 < baseStart_2370119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2370119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2370169 : List Nat := [1, 2, 1, 3, 3, 2, 1, 4, 6]
def baseStart_2370169 : Nat := 118140960795 + 2370169 * 2 ^ 59
def prefixEnd_2370169 : Nat := 4983230072969 + 3 ^ 40 * 2370169 * 2
def baseEnd_2370169 : Nat := 135226214376271381843033

theorem tailTrace_2370169 : CollatzResearch.WordTrace tailWord_2370169 prefixEnd_2370169 135226214376271381843033 := by
  unfold tailWord_2370169
  simp only [CollatzResearch.WordTrace]
  refine ⟨86447165350289980483121561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57631443566859986988747707 86447165350289980483121561)
  ·
    refine ⟨64835374012717485362341171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86447165350289980483121561 64835374012717485362341171)
    ·
      refine ⟨97253061019076228043511757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64835374012717485362341171 97253061019076228043511757)
      ·
        refine ⟨36469897882153585516316909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97253061019076228043511757 36469897882153585516316909)
        ·
          refine ⟨13676211705807594568618841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36469897882153585516316909 13676211705807594568618841)
          ·
            refine ⟨10257158779355695926464131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13676211705807594568618841 10257158779355695926464131)
            ·
              refine ⟨15385738169033543889696197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10257158779355695926464131 15385738169033543889696197)
              ·
                refine ⟨2884825906693789479318037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15385738169033543889696197 2884825906693789479318037)
                ·
                  refine ⟨135226214376271381843033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2884825906693789479318037 135226214376271381843033)
                  ·
                    rfl

theorem cell23_2370169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 4, 6].length) (baseStart_2370169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2370169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2370169 prefixEnd_2370169 := by exact prefixLift 2370169
  have htrace : WordTrace (prefixWord ++ tailWord_2370169) baseStart_2370169 baseEnd_2370169 := by
    simpa [prefixWord, tailWord_2370169, baseEnd_2370169] using wordTrace_append hprefix tailTrace_2370169
  have hstable : (prefixWord ++ tailWord_2370169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2370169).length < 2 ^ (prefixWord ++ tailWord_2370169).sum := by decide
  have hdescent : baseEnd_2370169 < baseStart_2370169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2370169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2370199 : List Nat := [1, 1, 3, 3, 2, 1, 1, 3, 3, 5]
def baseStart_2370199 : Nat := 118140960795 + 2370199 * 2 ^ 59
def prefixEnd_2370199 : Nat := 4983230072969 + 3 ^ 40 * 2370199 * 2
def baseEnd_2370199 : Nat := 405683777935359106404053

theorem tailTrace_2370199 : CollatzResearch.WordTrace tailWord_2370199 prefixEnd_2370199 405683777935359106404053 := by
  unfold tailWord_2370199
  simp only [CollatzResearch.WordTrace]
  refine ⟨86448259540181295606713651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57632173026787530404475767 86448259540181295606713651)
  ·
    refine ⟨129672389310271943410070477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86448259540181295606713651 129672389310271943410070477)
    ·
      refine ⟨48627145991351978778776429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129672389310271943410070477 48627145991351978778776429)
      ·
        refine ⟨18235179746756992042041161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48627145991351978778776429 18235179746756992042041161)
        ·
          refine ⟨13676384810067744031530871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18235179746756992042041161 13676384810067744031530871)
          ·
            refine ⟨20514577215101616047296307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13676384810067744031530871 20514577215101616047296307)
            ·
              refine ⟨30771865822652424070944461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20514577215101616047296307 30771865822652424070944461)
              ·
                refine ⟨11539449683494659026604173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30771865822652424070944461 11539449683494659026604173)
                ·
                  refine ⟨4327293631310497134976565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11539449683494659026604173 4327293631310497134976565)
                  ·
                    refine ⟨405683777935359106404053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4327293631310497134976565 405683777935359106404053)
                    ·
                      rfl

theorem cell23_2370199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3, 3, 5].length) (baseStart_2370199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2370199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2370199 prefixEnd_2370199 := by exact prefixLift 2370199
  have htrace : WordTrace (prefixWord ++ tailWord_2370199) baseStart_2370199 baseEnd_2370199 := by
    simpa [prefixWord, tailWord_2370199, baseEnd_2370199] using wordTrace_append hprefix tailTrace_2370199
  have hstable : (prefixWord ++ tailWord_2370199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2370199).length < 2 ^ (prefixWord ++ tailWord_2370199).sum := by decide
  have hdescent : baseEnd_2370199 < baseStart_2370199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2370199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2370239 : List Nat := [1, 1, 2, 2, 2, 4, 1, 1, 3, 1, 5]
def baseStart_2370239 : Nat := 118140960795 + 2370239 * 2 ^ 59
def prefixEnd_2370239 : Nat := 4983230072969 + 3 ^ 40 * 2370239 * 2
def baseEnd_2370239 : Nat := 1217071873032257162711975

theorem tailTrace_2370239 : CollatzResearch.WordTrace tailWord_2370239 prefixEnd_2370239 1217071873032257162711975 := by
  unfold tailWord_2370239
  simp only [CollatzResearch.WordTrace]
  refine ⟨86449718460036382438169771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57633145640024254958779847 86449718460036382438169771)
  ·
    refine ⟨129674577690054573657254657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86449718460036382438169771 129674577690054573657254657)
    ·
      refine ⟨97255933267540930242940993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129674577690054573657254657 97255933267540930242940993)
      ·
        refine ⟨72941949950655697682205745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97255933267540930242940993 72941949950655697682205745)
        ·
          refine ⟨54706462462991773261654309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72941949950655697682205745 54706462462991773261654309)
          ·
            refine ⟨10257461711810957486560183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54706462462991773261654309 10257461711810957486560183)
            ·
              refine ⟨15386192567716436229840275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10257461711810957486560183 15386192567716436229840275)
              ·
                refine ⟨23079288851574654344760413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15386192567716436229840275 23079288851574654344760413)
                ·
                  refine ⟨8654733319340495379285155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23079288851574654344760413 8654733319340495379285155)
                  ·
                    refine ⟨12982099979010743068927733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8654733319340495379285155 12982099979010743068927733)
                    ·
                      refine ⟨1217071873032257162711975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12982099979010743068927733 1217071873032257162711975)
                      ·
                        rfl

theorem cell23_2370239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 3, 1, 5].length) (baseStart_2370239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2370239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2370239 prefixEnd_2370239 := by exact prefixLift 2370239
  have htrace : WordTrace (prefixWord ++ tailWord_2370239) baseStart_2370239 baseEnd_2370239 := by
    simpa [prefixWord, tailWord_2370239, baseEnd_2370239] using wordTrace_append hprefix tailTrace_2370239
  have hstable : (prefixWord ++ tailWord_2370239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2370239).length < 2 ^ (prefixWord ++ tailWord_2370239).sum := by decide
  have hdescent : baseEnd_2370239 < baseStart_2370239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2370239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2370273 : List Nat := [1, 2, 3, 1, 4, 1, 2, 3, 1, 2, 3]
def baseStart_2370273 : Nat := 118140960795 + 2370273 * 2 ^ 59
def prefixEnd_2370273 : Nat := 4983230072969 + 3 ^ 40 * 2370273 * 2
def baseEnd_2370273 : Nat := 1217089331374510029686819

theorem tailTrace_2370273 : CollatzResearch.WordTrace tailWord_2370273 prefixEnd_2370273 1217089331374510029686819 := by
  unfold tailWord_2370273
  simp only [CollatzResearch.WordTrace]
  refine ⟨86450958541913206244907473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57633972361275470829938315 86450958541913206244907473)
  ·
    refine ⟨64838218906434904683680605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86450958541913206244907473 64838218906434904683680605)
    ·
      refine ⟨24314332089913089256380227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64838218906434904683680605 24314332089913089256380227)
      ·
        refine ⟨36471498134869633884570341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24314332089913089256380227 36471498134869633884570341)
        ·
          refine ⟨6838405900288056353356939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36471498134869633884570341 6838405900288056353356939)
          ·
            refine ⟨10257608850432084530035409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6838405900288056353356939 10257608850432084530035409)
            ·
              refine ⟨7693206637824063397526557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10257608850432084530035409 7693206637824063397526557)
              ·
                refine ⟨2884952489184023774072459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7693206637824063397526557 2884952489184023774072459)
                ·
                  refine ⟨4327428733776035661108689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2884952489184023774072459 4327428733776035661108689)
                  ·
                    refine ⟨3245571550332026745831517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4327428733776035661108689 3245571550332026745831517)
                    ·
                      refine ⟨1217089331374510029686819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3245571550332026745831517 1217089331374510029686819)
                      ·
                        rfl

theorem cell23_2370273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 3, 1, 2, 3].length) (baseStart_2370273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2370273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2370273 prefixEnd_2370273 := by exact prefixLift 2370273
  have htrace : WordTrace (prefixWord ++ tailWord_2370273) baseStart_2370273 baseEnd_2370273 := by
    simpa [prefixWord, tailWord_2370273, baseEnd_2370273] using wordTrace_append hprefix tailTrace_2370273
  have hstable : (prefixWord ++ tailWord_2370273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2370273).length < 2 ^ (prefixWord ++ tailWord_2370273).sum := by decide
  have hdescent : baseEnd_2370273 < baseStart_2370273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2370273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2370289 : List Nat := [1, 2, 2, 2, 2, 2, 2, 1, 2, 7]
def baseStart_2370289 : Nat := 118140960795 + 2370289 * 2 ^ 59
def prefixEnd_2370289 : Nat := 4983230072969 + 3 ^ 40 * 2370289 * 2
def baseEnd_2370289 : Nat := 405699182354993989028915

theorem tailTrace_2370289 : CollatzResearch.WordTrace tailWord_2370289 prefixEnd_2370289 405699182354993989028915 := by
  unfold tailWord_2370289
  simp only [CollatzResearch.WordTrace]
  refine ⟨86451542109855240977489921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57634361406570160651659947 86451542109855240977489921)
  ·
    refine ⟨64838656582391430733117441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86451542109855240977489921 64838656582391430733117441)
    ·
      refine ⟨48628992436793573049838081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64838656582391430733117441 48628992436793573049838081)
      ·
        refine ⟨36471744327595179787378561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48628992436793573049838081 36471744327595179787378561)
        ·
          refine ⟨27353808245696384840533921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36471744327595179787378561 27353808245696384840533921)
          ·
            refine ⟨20515356184272288630400441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27353808245696384840533921 20515356184272288630400441)
            ·
              refine ⟨15386517138204216472800331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20515356184272288630400441 15386517138204216472800331)
              ·
                refine ⟨23079775707306324709200497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15386517138204216472800331 23079775707306324709200497)
                ·
                  refine ⟨17309831780479743531900373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23079775707306324709200497 17309831780479743531900373)
                  ·
                    refine ⟨405699182354993989028915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17309831780479743531900373 405699182354993989028915)
                    ·
                      rfl

theorem cell23_2370289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 7].length) (baseStart_2370289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2370289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2370289 prefixEnd_2370289 := by exact prefixLift 2370289
  have htrace : WordTrace (prefixWord ++ tailWord_2370289) baseStart_2370289 baseEnd_2370289 := by
    simpa [prefixWord, tailWord_2370289, baseEnd_2370289] using wordTrace_append hprefix tailTrace_2370289
  have hstable : (prefixWord ++ tailWord_2370289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2370289).length < 2 ^ (prefixWord ++ tailWord_2370289).sum := by decide
  have hdescent : baseEnd_2370289 < baseStart_2370289 := by decide
  rcases family_descends (prefixWord ++ tailWord_2370289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2370329 : List Nat := [1, 2, 1, 2, 1, 1, 1, 5, 1, 3, 5]
def baseStart_2370329 : Nat := 118140960795 + 2370329 * 2 ^ 59
def prefixEnd_2370329 : Nat := 4983230072969 + 3 ^ 40 * 2370329 * 2
def baseEnd_2370329 : Nat := 1217118086291161810586561

theorem tailTrace_2370329 : CollatzResearch.WordTrace tailWord_2370329 prefixEnd_2370329 1217118086291161810586561 := by
  unfold tailWord_2370329
  simp only [CollatzResearch.WordTrace]
  refine ⟨86453001029710327808946041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57635334019806885205964027 86453001029710327808946041)
  ·
    refine ⟨64839750772282745856709531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86453001029710327808946041 64839750772282745856709531)
    ·
      refine ⟨97259626158424118785064297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64839750772282745856709531 97259626158424118785064297)
      ·
        refine ⟨72944719618818089088798223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97259626158424118785064297 72944719618818089088798223)
        ·
          refine ⟨109417079428227133633197335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72944719618818089088798223 109417079428227133633197335)
          ·
            refine ⟨164125619142340700449796003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109417079428227133633197335 164125619142340700449796003)
            ·
              refine ⟨246188428713511050674694005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164125619142340700449796003 246188428713511050674694005)
              ·
                refine ⟨23080165191891661000752563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 246188428713511050674694005 23080165191891661000752563)
                ·
                  refine ⟨34620247787837491501128845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23080165191891661000752563 34620247787837491501128845)
                  ·
                    refine ⟨12982592920439059312923317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34620247787837491501128845 12982592920439059312923317)
                    ·
                      refine ⟨1217118086291161810586561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12982592920439059312923317 1217118086291161810586561)
                      ·
                        rfl

theorem cell23_2370329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 3, 5].length) (baseStart_2370329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2370329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2370329 prefixEnd_2370329 := by exact prefixLift 2370329
  have htrace : WordTrace (prefixWord ++ tailWord_2370329) baseStart_2370329 baseEnd_2370329 := by
    simpa [prefixWord, tailWord_2370329, baseEnd_2370329] using wordTrace_append hprefix tailTrace_2370329
  have hstable : (prefixWord ++ tailWord_2370329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2370329).length < 2 ^ (prefixWord ++ tailWord_2370329).sum := by decide
  have hdescent : baseEnd_2370329 < baseStart_2370329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2370329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2370339 : List Nat := [1, 1, 1, 4, 2, 1, 1, 1, 2, 3, 6]
def baseStart_2370339 : Nat := 118140960795 + 2370339 * 2 ^ 59
def prefixEnd_2370339 : Nat := 4983230072969 + 3 ^ 40 * 2370339 * 2
def baseEnd_2370339 : Nat := 1217123221097706771461515

theorem tailTrace_2370339 : CollatzResearch.WordTrace tailWord_2370339 prefixEnd_2370339 1217123221097706771461515 := by
  unfold tailWord_2370339
  simp only [CollatzResearch.WordTrace]
  refine ⟨86453365759674099516810071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57635577173116066344540047 86453365759674099516810071)
  ·
    refine ⟨129680048639511149275215107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86453365759674099516810071 129680048639511149275215107)
    ·
      refine ⟨194520072959266723912822661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129680048639511149275215107 194520072959266723912822661)
      ·
        refine ⟨36472513679862510733654249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 194520072959266723912822661 36472513679862510733654249)
        ·
          refine ⟨27354385259896883050240687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36472513679862510733654249 27354385259896883050240687)
          ·
            refine ⟨41031577889845324575361031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27354385259896883050240687 41031577889845324575361031)
            ·
              refine ⟨61547366834767986863041547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41031577889845324575361031 61547366834767986863041547)
              ·
                refine ⟨92321050252151980294562321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61547366834767986863041547 92321050252151980294562321)
                ·
                  refine ⟨69240787689113985220921741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 92321050252151980294562321 69240787689113985220921741)
                  ·
                    refine ⟨25965295383417744457845653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 69240787689113985220921741 25965295383417744457845653)
                    ·
                      refine ⟨1217123221097706771461515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25965295383417744457845653 1217123221097706771461515)
                      ·
                        rfl

theorem cell23_2370339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 3, 6].length) (baseStart_2370339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2370339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2370339 prefixEnd_2370339 := by exact prefixLift 2370339
  have htrace : WordTrace (prefixWord ++ tailWord_2370339) baseStart_2370339 baseEnd_2370339 := by
    simpa [prefixWord, tailWord_2370339, baseEnd_2370339] using wordTrace_append hprefix tailTrace_2370339
  have hstable : (prefixWord ++ tailWord_2370339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2370339).length < 2 ^ (prefixWord ++ tailWord_2370339).sum := by decide
  have hdescent : baseEnd_2370339 < baseStart_2370339 := by decide
  rcases family_descends (prefixWord ++ tailWord_2370339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2370360 : List Nat := [2, 1, 2, 1, 3, 2, 1, 5, 2, 2, 2]
def baseStart_2370360 : Nat := 118140960795 + 2370360 * 2 ^ 59
def prefixEnd_2370360 : Nat := 4983230072969 + 3 ^ 40 * 2370360 * 2
def baseEnd_2370360 : Nat := 1217134004191451189298919

theorem tailTrace_2370360 : CollatzResearch.WordTrace tailWord_2370360 prefixEnd_2370360 1217134004191451189298919 := by
  unfold tailWord_2370360
  simp only [CollatzResearch.WordTrace]
  refine ⟨43227065846299010051662267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57636087795065346735549689 43227065846299010051662267)
  ·
    refine ⟨64840598769448515077493401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43227065846299010051662267 64840598769448515077493401)
    ·
      refine ⟨48630449077086386308120051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64840598769448515077493401 48630449077086386308120051)
      ·
        refine ⟨72945673615629579462180077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48630449077086386308120051 72945673615629579462180077)
        ·
          refine ⟨27354627605861092298317529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72945673615629579462180077 27354627605861092298317529)
          ·
            refine ⟨20515970704395819223738147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27354627605861092298317529 20515970704395819223738147)
            ·
              refine ⟨30773956056593728835607221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20515970704395819223738147 30773956056593728835607221)
              ·
                refine ⟨2885058380305662078338177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30773956056593728835607221 2885058380305662078338177)
                ·
                  refine ⟨2163793785229246558753633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2885058380305662078338177 2163793785229246558753633)
                  ·
                    refine ⟨1622845338921934919065225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2163793785229246558753633 1622845338921934919065225)
                    ·
                      refine ⟨1217134004191451189298919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1622845338921934919065225 1217134004191451189298919)
                      ·
                        rfl

theorem cell23_2370360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 5, 2, 2, 2].length) (baseStart_2370360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2370360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2370360 prefixEnd_2370360 := by exact prefixLift 2370360
  have htrace : WordTrace (prefixWord ++ tailWord_2370360) baseStart_2370360 baseEnd_2370360 := by
    simpa [prefixWord, tailWord_2370360, baseEnd_2370360] using wordTrace_append hprefix tailTrace_2370360
  have hstable : (prefixWord ++ tailWord_2370360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2370360).length < 2 ^ (prefixWord ++ tailWord_2370360).sum := by decide
  have hdescent : baseEnd_2370360 < baseStart_2370360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2370360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2370376 : List Nat := [2, 1, 3, 1, 1, 3, 1, 2, 1, 5, 3]
def baseStart_2370376 : Nat := 118140960795 + 2370376 * 2 ^ 59
def prefixEnd_2370376 : Nat := 4983230072969 + 3 ^ 40 * 2370376 * 2
def baseEnd_2370376 : Nat := 1217142219881923126698845

theorem tailTrace_2370376 : CollatzResearch.WordTrace tailWord_2370376 prefixEnd_2370376 1217142219881923126698845 := by
  unfold tailWord_2370376
  simp only [CollatzResearch.WordTrace]
  refine ⟨43227357630270027417953491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57636476840360036557271321 43227357630270027417953491)
  ·
    refine ⟨64841036445405041126930237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43227357630270027417953491 64841036445405041126930237)
    ·
      refine ⟨24315388667026890422598839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64841036445405041126930237 24315388667026890422598839)
      ·
        refine ⟨36473083000540335633898259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24315388667026890422598839 36473083000540335633898259)
        ·
          refine ⟨54709624500810503450847389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36473083000540335633898259 54709624500810503450847389)
          ·
            refine ⟨20516109187803938794067771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54709624500810503450847389 20516109187803938794067771)
            ·
              refine ⟨30774163781705908191101657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20516109187803938794067771 30774163781705908191101657)
              ·
                refine ⟨23080622836279431143326243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30774163781705908191101657 23080622836279431143326243)
                ·
                  refine ⟨34620934254419146714989365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23080622836279431143326243 34620934254419146714989365)
                  ·
                    refine ⟨3245712586351795004530253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34620934254419146714989365 3245712586351795004530253)
                    ·
                      refine ⟨1217142219881923126698845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3245712586351795004530253 1217142219881923126698845)
                      ·
                        rfl

theorem cell23_2370376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 1, 5, 3].length) (baseStart_2370376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2370376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2370376 prefixEnd_2370376 := by exact prefixLift 2370376
  have htrace : WordTrace (prefixWord ++ tailWord_2370376) baseStart_2370376 baseEnd_2370376 := by
    simpa [prefixWord, tailWord_2370376, baseEnd_2370376] using wordTrace_append hprefix tailTrace_2370376
  have hstable : (prefixWord ++ tailWord_2370376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2370376).length < 2 ^ (prefixWord ++ tailWord_2370376).sum := by decide
  have hdescent : baseEnd_2370376 < baseStart_2370376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2370376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2370381 : List Nat := [1, 6, 1, 2, 2, 2, 2, 1, 1, 3, 2]
def baseStart_2370381 : Nat := 118140960795 + 2370381 * 2 ^ 59
def prefixEnd_2370381 : Nat := 4983230072969 + 3 ^ 40 * 2370381 * 2
def baseEnd_2370381 : Nat := 1217144787285195607136323

theorem tailTrace_2370381 : CollatzResearch.WordTrace tailWord_2370381 prefixEnd_2370381 1217144787285195607136323 := by
  unfold tailWord_2370381
  simp only [CollatzResearch.WordTrace]
  refine ⟨86454897625521940689838997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57636598417014627126559331 86454897625521940689838997)
  ·
    refine ⟨4052573326196340969836203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 86454897625521940689838997 4052573326196340969836203)
    ·
      refine ⟨6078859989294511454754305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4052573326196340969836203 6078859989294511454754305)
      ·
        refine ⟨4559144991970883591065729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6078859989294511454754305 4559144991970883591065729)
        ·
          refine ⟨3419358743978162693299297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4559144991970883591065729 3419358743978162693299297)
          ·
            refine ⟨2564519057983622019974473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3419358743978162693299297 2564519057983622019974473)
            ·
              refine ⟨1923389293487716514980855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2564519057983622019974473 1923389293487716514980855)
              ·
                refine ⟨2885083940231574772471283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1923389293487716514980855 2885083940231574772471283)
                ·
                  refine ⟨4327625910347362158706925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2885083940231574772471283 4327625910347362158706925)
                  ·
                    refine ⟨1622859716380260809515097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4327625910347362158706925 1622859716380260809515097)
                    ·
                      refine ⟨1217144787285195607136323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1622859716380260809515097 1217144787285195607136323)
                      ·
                        rfl

theorem cell23_2370381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_2370381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2370381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2370381 prefixEnd_2370381 := by exact prefixLift 2370381
  have htrace : WordTrace (prefixWord ++ tailWord_2370381) baseStart_2370381 baseEnd_2370381 := by
    simpa [prefixWord, tailWord_2370381, baseEnd_2370381] using wordTrace_append hprefix tailTrace_2370381
  have hstable : (prefixWord ++ tailWord_2370381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2370381).length < 2 ^ (prefixWord ++ tailWord_2370381).sum := by decide
  have hdescent : baseEnd_2370381 < baseStart_2370381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2370381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2370416 : List Nat := [2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 4]
def baseStart_2370416 : Nat := 118140960795 + 2370416 * 2 ^ 59
def prefixEnd_2370416 : Nat := 4983230072969 + 3 ^ 40 * 2370416 * 2
def baseEnd_2370416 : Nat := 1217162759108102970198661

theorem tailTrace_2370416 : CollatzResearch.WordTrace tailWord_2370416 prefixEnd_2370416 1217162759108102970198661 := by
  unfold tailWord_2370416
  simp only [CollatzResearch.WordTrace]
  refine ⟨43228087090197570833681551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57637449453596761111575401 43228087090197570833681551)
  ·
    refine ⟨64842130635296356250522327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43228087090197570833681551 64842130635296356250522327)
    ·
      refine ⟨97263195952944534375783491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64842130635296356250522327 97263195952944534375783491)
      ·
        refine ⟨145894793929416801563675237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97263195952944534375783491 145894793929416801563675237)
        ·
          refine ⟨27355273861765650293189107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 145894793929416801563675237 27355273861765650293189107)
          ·
            refine ⟨41032910792648475439783661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27355273861765650293189107 41032910792648475439783661)
            ·
              refine ⟨15387341547243178289918873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41032910792648475439783661 15387341547243178289918873)
              ·
                refine ⟨11540506160432383717439155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15387341547243178289918873 11540506160432383717439155)
                ·
                  refine ⟨17310759240648575576158733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11540506160432383717439155 17310759240648575576158733)
                  ·
                    refine ⟨6491534715243215841059525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17310759240648575576158733 6491534715243215841059525)
                    ·
                      refine ⟨1217162759108102970198661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6491534715243215841059525 1217162759108102970198661)
                      ·
                        rfl

theorem cell23_2370416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 4].length) (baseStart_2370416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2370416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2370416 prefixEnd_2370416 := by exact prefixLift 2370416
  have htrace : WordTrace (prefixWord ++ tailWord_2370416) baseStart_2370416 baseEnd_2370416 := by
    simpa [prefixWord, tailWord_2370416, baseEnd_2370416] using wordTrace_append hprefix tailTrace_2370416
  have hstable : (prefixWord ++ tailWord_2370416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2370416).length < 2 ^ (prefixWord ++ tailWord_2370416).sum := by decide
  have hdescent : baseEnd_2370416 < baseStart_2370416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2370416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2370436 : List Nat := [2, 3, 2, 1, 1, 1, 1, 2, 2, 3, 5]
def baseStart_2370436 : Nat := 118140960795 + 2370436 * 2 ^ 59
def prefixEnd_2370436 : Nat := 4983230072969 + 3 ^ 40 * 2370436 * 2
def baseEnd_2370436 : Nat := 1217173028721192891948569

theorem tailTrace_2370436 : CollatzResearch.WordTrace tailWord_2370436 prefixEnd_2370436 1217173028721192891948569 := by
  unfold tailWord_2370436
  simp only [CollatzResearch.WordTrace]
  refine ⟨43228451820161342541545581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57637935760215123388727441 43228451820161342541545581)
  ·
    refine ⟨16210669432560503453079593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43228451820161342541545581 16210669432560503453079593)
    ·
      refine ⟨12158002074420377589809695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16210669432560503453079593 12158002074420377589809695)
      ·
        refine ⟨18237003111630566384714543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12158002074420377589809695 18237003111630566384714543)
        ·
          refine ⟨27355504667445849577071815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18237003111630566384714543 27355504667445849577071815)
          ·
            refine ⟨41033257001168774365607723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27355504667445849577071815 41033257001168774365607723)
            ·
              refine ⟨61549885501753161548411585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41033257001168774365607723 61549885501753161548411585)
              ·
                refine ⟨46162414126314871161308689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61549885501753161548411585 46162414126314871161308689)
                ·
                  refine ⟨34621810594736153370981517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46162414126314871161308689 34621810594736153370981517)
                  ·
                    refine ⟨12983178973026057514118069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34621810594736153370981517 12983178973026057514118069)
                    ·
                      refine ⟨1217173028721192891948569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12983178973026057514118069 1217173028721192891948569)
                      ·
                        rfl

theorem cell23_2370436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_2370436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2370436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2370436 prefixEnd_2370436 := by exact prefixLift 2370436
  have htrace : WordTrace (prefixWord ++ tailWord_2370436) baseStart_2370436 baseEnd_2370436 := by
    simpa [prefixWord, tailWord_2370436, baseEnd_2370436] using wordTrace_append hprefix tailTrace_2370436
  have hstable : (prefixWord ++ tailWord_2370436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2370436).length < 2 ^ (prefixWord ++ tailWord_2370436).sum := by decide
  have hdescent : baseEnd_2370436 < baseStart_2370436 := by decide
  rcases family_descends (prefixWord ++ tailWord_2370436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2370453 : List Nat := [1, 3, 2, 1, 1, 4, 1, 1, 4, 2, 3]
def baseStart_2370453 : Nat := 118140960795 + 2370453 * 2 ^ 59
def prefixEnd_2370453 : Nat := 4983230072969 + 3 ^ 40 * 2370453 * 2
def baseEnd_2370453 : Nat := 1217181757892319325435991

theorem tailTrace_2370453 : CollatzResearch.WordTrace tailWord_2370453 prefixEnd_2370453 1217181757892319325435991 := by
  unfold tailWord_2370453
  simp only [CollatzResearch.WordTrace]
  refine ⟨86457523681261096986460013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57638349120840731324306675 86457523681261096986460013)
  ·
    refine ⟨32421571380472911369922505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86457523681261096986460013 32421571380472911369922505)
    ·
      refine ⟨24316178535354683527441879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32421571380472911369922505 24316178535354683527441879)
      ·
        refine ⟨36474267803032025291162819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24316178535354683527441879 36474267803032025291162819)
        ·
          refine ⟨54711401704548037936744229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36474267803032025291162819 54711401704548037936744229)
          ·
            refine ⟨10258387819602757113139543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54711401704548037936744229 10258387819602757113139543)
            ·
              refine ⟨15387581729404135669709315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10258387819602757113139543 15387581729404135669709315)
              ·
                refine ⟨23081372594106203504563973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15387581729404135669709315 23081372594106203504563973)
                ·
                  refine ⟨4327757361394913157105745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23081372594106203504563973 4327757361394913157105745)
                  ·
                    refine ⟨3245818021046184867829309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4327757361394913157105745 3245818021046184867829309)
                    ·
                      refine ⟨1217181757892319325435991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3245818021046184867829309 1217181757892319325435991)
                      ·
                        rfl

theorem cell23_2370453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 4, 2, 3].length) (baseStart_2370453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2370453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2370453 prefixEnd_2370453 := by exact prefixLift 2370453
  have htrace : WordTrace (prefixWord ++ tailWord_2370453) baseStart_2370453 baseEnd_2370453 := by
    simpa [prefixWord, tailWord_2370453, baseEnd_2370453] using wordTrace_append hprefix tailTrace_2370453
  have hstable : (prefixWord ++ tailWord_2370453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2370453).length < 2 ^ (prefixWord ++ tailWord_2370453).sum := by decide
  have hdescent : baseEnd_2370453 < baseStart_2370453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2370453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2370503 : List Nat := [1, 1, 4, 1, 1, 2, 2, 5, 1, 5]
def baseStart_2370503 : Nat := 118140960795 + 2370503 * 2 ^ 59
def prefixEnd_2370503 : Nat := 4983230072969 + 3 ^ 40 * 2370503 * 2
def baseEnd_2370503 : Nat := 405735810641681376603587

theorem tailTrace_2370503 : CollatzResearch.WordTrace tailWord_2370503 prefixEnd_2370503 405735810641681376603587 := by
  unfold tailWord_2370503
  simp only [CollatzResearch.WordTrace]
  refine ⟨86459347331079955525780163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57639564887386637017186775 86459347331079955525780163)
  ·
    refine ⟨129689020996619933288670245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86459347331079955525780163 129689020996619933288670245)
    ·
      refine ⟨24316691436866237491625671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 129689020996619933288670245 24316691436866237491625671)
      ·
        refine ⟨36475037155299356237438507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24316691436866237491625671 36475037155299356237438507)
        ·
          refine ⟨54712555732949034356157761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36475037155299356237438507 54712555732949034356157761)
          ·
            refine ⟨41034416799711775767118321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54712555732949034356157761 41034416799711775767118321)
            ·
              refine ⟨30775812599783831825338741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41034416799711775767118321 30775812599783831825338741)
              ·
                refine ⟨2885232431229734233625507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30775812599783831825338741 2885232431229734233625507)
                ·
                  refine ⟨4327848646844601350438261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2885232431229734233625507 4327848646844601350438261)
                  ·
                    refine ⟨405735810641681376603587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4327848646844601350438261 405735810641681376603587)
                    ·
                      rfl

theorem cell23_2370503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 5, 1, 5].length) (baseStart_2370503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2370503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2370503 prefixEnd_2370503 := by exact prefixLift 2370503
  have htrace : WordTrace (prefixWord ++ tailWord_2370503) baseStart_2370503 baseEnd_2370503 := by
    simpa [prefixWord, tailWord_2370503, baseEnd_2370503] using wordTrace_append hprefix tailTrace_2370503
  have hstable : (prefixWord ++ tailWord_2370503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2370503).length < 2 ^ (prefixWord ++ tailWord_2370503).sum := by decide
  have hdescent : baseEnd_2370503 < baseStart_2370503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2370503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2370550 : List Nat := [5, 1, 1, 1, 3, 1, 2, 2, 1, 6]
def baseStart_2370550 : Nat := 118140960795 + 2370550 * 2 ^ 59
def prefixEnd_2370550 : Nat := 4983230072969 + 3 ^ 40 * 2370550 * 2
def baseEnd_2370550 : Nat := 405743855171935148641015

theorem tailTrace_2370550 : CollatzResearch.WordTrace tailWord_2370550 prefixEnd_2370550 405743855171935148641015 := by
  unfold tailWord_2370550
  simp only [CollatzResearch.WordTrace]
  refine ⟨5403816347619355159546319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57640707707939788368494069 5403816347619355159546319)
  ·
    refine ⟨8105724521429032739319479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5403816347619355159546319 8105724521429032739319479)
    ·
      refine ⟨12158586782143549108979219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8105724521429032739319479 12158586782143549108979219)
      ·
        refine ⟨18237880173215323663468829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12158586782143549108979219 18237880173215323663468829)
        ·
          refine ⟨6839205064955746373800811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18237880173215323663468829 6839205064955746373800811)
          ·
            refine ⟨10258807597433619560701217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6839205064955746373800811 10258807597433619560701217)
            ·
              refine ⟨7694105698075214670525913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10258807597433619560701217 7694105698075214670525913)
              ·
                refine ⟨5770579273556411002894435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7694105698075214670525913 5770579273556411002894435)
                ·
                  refine ⟨8655868910334616504341653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5770579273556411002894435 8655868910334616504341653)
                  ·
                    refine ⟨405743855171935148641015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8655868910334616504341653 405743855171935148641015)
                    ·
                      rfl

theorem cell23_2370550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 2, 1, 6].length) (baseStart_2370550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2370550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2370550 prefixEnd_2370550 := by exact prefixLift 2370550
  have htrace : WordTrace (prefixWord ++ tailWord_2370550) baseStart_2370550 baseEnd_2370550 := by
    simpa [prefixWord, tailWord_2370550, baseEnd_2370550] using wordTrace_append hprefix tailTrace_2370550
  have hstable : (prefixWord ++ tailWord_2370550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2370550).length < 2 ^ (prefixWord ++ tailWord_2370550).sum := by decide
  have hdescent : baseEnd_2370550 < baseStart_2370550 := by decide
  rcases family_descends (prefixWord ++ tailWord_2370550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2370553 : List Nat := [1, 2, 1, 3, 1, 3, 1, 4, 1, 2, 4]
def baseStart_2370553 : Nat := 118140960795 + 2370553 * 2 ^ 59
def prefixEnd_2370553 : Nat := 4983230072969 + 3 ^ 40 * 2370553 * 2
def baseEnd_2370553 : Nat := 1217233105957768934185531

theorem tailTrace_2370553 : CollatzResearch.WordTrace tailWord_2370553 prefixEnd_2370553 1217233105957768934185531 := by
  unfold tailWord_2370553
  simp only [CollatzResearch.WordTrace]
  refine ⟨86461170980898814065100313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57640780653932542710066875 86461170980898814065100313)
  ·
    refine ⟨64845878235674110548825235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86461170980898814065100313 64845878235674110548825235)
    ·
      refine ⟨97268817353511165823237853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64845878235674110548825235 97268817353511165823237853)
      ·
        refine ⟨36475806507566687183714195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97268817353511165823237853 36475806507566687183714195)
        ·
          refine ⟨54713709761350030775571293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36475806507566687183714195 54713709761350030775571293)
          ·
            refine ⟨20517641160506261540839235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54713709761350030775571293 20517641160506261540839235)
            ·
              refine ⟨30776461740759392311258853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20517641160506261540839235 30776461740759392311258853)
              ·
                refine ⟨5770586576392386058361035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30776461740759392311258853 5770586576392386058361035)
                ·
                  refine ⟨8655879864588579087541553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5770586576392386058361035 8655879864588579087541553)
                  ·
                    refine ⟨6491909898441434315656165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8655879864588579087541553 6491909898441434315656165)
                    ·
                      refine ⟨1217233105957768934185531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6491909898441434315656165 1217233105957768934185531)
                      ·
                        rfl

theorem cell23_2370553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 4, 1, 2, 4].length) (baseStart_2370553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2370553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2370553 prefixEnd_2370553 := by exact prefixLift 2370553
  have htrace : WordTrace (prefixWord ++ tailWord_2370553) baseStart_2370553 baseEnd_2370553 := by
    simpa [prefixWord, tailWord_2370553, baseEnd_2370553] using wordTrace_append hprefix tailTrace_2370553
  have hstable : (prefixWord ++ tailWord_2370553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2370553).length < 2 ^ (prefixWord ++ tailWord_2370553).sum := by decide
  have hdescent : baseEnd_2370553 < baseStart_2370553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2370553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2370574 : List Nat := [4, 1, 1, 2, 2, 3, 2, 1, 3, 2, 2]
def baseStart_2370574 : Nat := 118140960795 + 2370574 * 2 ^ 59
def prefixEnd_2370574 : Nat := 4983230072969 + 3 ^ 40 * 2370574 * 2
def baseEnd_2370574 : Nat := 1217243889051513352022935

theorem tailTrace_2370574 : CollatzResearch.WordTrace tailWord_2370574 prefixEnd_2370574 1217243889051513352022935 := by
  unfold tailWord_2370574
  simp only [CollatzResearch.WordTrace]
  refine ⟨10807742114227841831451847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57641291275881823101076517 10807742114227841831451847)
  ·
    refine ⟨16211613171341762747177771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10807742114227841831451847 16211613171341762747177771)
    ·
      refine ⟨24317419757012644120766657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16211613171341762747177771 24317419757012644120766657)
      ·
        refine ⟨18238064817759483090574993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24317419757012644120766657 18238064817759483090574993)
        ·
          refine ⟨13678548613319612317931245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18238064817759483090574993 13678548613319612317931245)
          ·
            refine ⟨5129455729994854619224217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13678548613319612317931245 5129455729994854619224217)
            ·
              refine ⟨3847091797496140964418163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5129455729994854619224217 3847091797496140964418163)
              ·
                refine ⟨5770637696244211446627245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3847091797496140964418163 5770637696244211446627245)
                ·
                  refine ⟨2163989136091579292485217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5770637696244211446627245 2163989136091579292485217)
                  ·
                    refine ⟨1622991852068684469363913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2163989136091579292485217 1622991852068684469363913)
                    ·
                      refine ⟨1217243889051513352022935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1622991852068684469363913 1217243889051513352022935)
                      ·
                        rfl

theorem cell23_2370574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 1, 3, 2, 2].length) (baseStart_2370574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2370574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2370574 prefixEnd_2370574 := by exact prefixLift 2370574
  have htrace : WordTrace (prefixWord ++ tailWord_2370574) baseStart_2370574 baseEnd_2370574 := by
    simpa [prefixWord, tailWord_2370574, baseEnd_2370574] using wordTrace_append hprefix tailTrace_2370574
  have hstable : (prefixWord ++ tailWord_2370574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2370574).length < 2 ^ (prefixWord ++ tailWord_2370574).sum := by decide
  have hdescent : baseEnd_2370574 < baseStart_2370574 := by decide
  rcases family_descends (prefixWord ++ tailWord_2370574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2370613 : List Nat := [1, 3, 3, 1, 1, 1, 1, 2, 1, 5, 4]
def baseStart_2370613 : Nat := 118140960795 + 2370613 * 2 ^ 59
def prefixEnd_2370613 : Nat := 4983230072969 + 3 ^ 40 * 2370613 * 2
def baseEnd_2370613 : Nat := 1217263914797038699435255

theorem tailTrace_2370613 : CollatzResearch.WordTrace tailWord_2370613 prefixEnd_2370613 1217263914797038699435255 := by
  unfold tailWord_2370613
  simp only [CollatzResearch.WordTrace]
  refine ⟨86463359360681444312284493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57642239573787629541522995 86463359360681444312284493)
  ·
    refine ⟨32423759760255541617106685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86463359360681444312284493 32423759760255541617106685)
    ·
      refine ⟨12158909910095828106415007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32423759760255541617106685 12158909910095828106415007)
      ·
        refine ⟨18238364865143742159622511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12158909910095828106415007 18238364865143742159622511)
        ·
          refine ⟨27357547297715613239433767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18238364865143742159622511 27357547297715613239433767)
          ·
            refine ⟨41036320946573419859150651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27357547297715613239433767 41036320946573419859150651)
            ·
              refine ⟨61554481419860129788725977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41036320946573419859150651 61554481419860129788725977)
              ·
                refine ⟨46165861064895097341544483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61554481419860129788725977 46165861064895097341544483)
                ·
                  refine ⟨69248791597342646012316725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46165861064895097341544483 69248791597342646012316725)
                  ·
                    refine ⟨6492074212250873063654693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 69248791597342646012316725 6492074212250873063654693)
                    ·
                      refine ⟨1217263914797038699435255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6492074212250873063654693 1217263914797038699435255)
                      ·
                        rfl

theorem cell23_2370613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_2370613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2370613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2370613 prefixEnd_2370613 := by exact prefixLift 2370613
  have htrace : WordTrace (prefixWord ++ tailWord_2370613) baseStart_2370613 baseEnd_2370613 := by
    simpa [prefixWord, tailWord_2370613, baseEnd_2370613] using wordTrace_append hprefix tailTrace_2370613
  have hstable : (prefixWord ++ tailWord_2370613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2370613).length < 2 ^ (prefixWord ++ tailWord_2370613).sum := by decide
  have hdescent : baseEnd_2370613 < baseStart_2370613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2370613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2370681 : List Nat := [1, 2, 1, 3, 5, 1, 2, 2, 2, 2, 2]
def baseStart_2370681 : Nat := 118140960795 + 2370681 * 2 ^ 59
def prefixEnd_2370681 : Nat := 4983230072969 + 3 ^ 40 * 2370681 * 2
def baseEnd_2370681 : Nat := 1217298831481544433384943

theorem tailTrace_2370681 : CollatzResearch.WordTrace tailWord_2370681 prefixEnd_2370681 1217298831481544433384943 := by
  unfold tailWord_2370681
  simp only [CollatzResearch.WordTrace]
  refine ⟨86465839524435091925759897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57643893016290061283839931 86465839524435091925759897)
  ·
    refine ⟨64849379643326318944319923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86465839524435091925759897 64849379643326318944319923)
    ·
      refine ⟨97274069464989478416479885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64849379643326318944319923 97274069464989478416479885)
      ·
        refine ⟨36477776049371054406179957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97274069464989478416479885 36477776049371054406179957)
        ·
          refine ⟨3419791504628536350579371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36477776049371054406179957 3419791504628536350579371)
          ·
            refine ⟨5129687256942804525869057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3419791504628536350579371 5129687256942804525869057)
            ·
              refine ⟨3847265442707103394401793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5129687256942804525869057 3847265442707103394401793)
              ·
                refine ⟨2885449082030327545801345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3847265442707103394401793 2885449082030327545801345)
                ·
                  refine ⟨2164086811522745659351009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2885449082030327545801345 2164086811522745659351009)
                  ·
                    refine ⟨1623065108642059244513257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2164086811522745659351009 1623065108642059244513257)
                    ·
                      refine ⟨1217298831481544433384943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1623065108642059244513257 1217298831481544433384943)
                      ·
                        rfl

theorem cell23_2370681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 2, 2, 2, 2].length) (baseStart_2370681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2370681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2370681 prefixEnd_2370681 := by exact prefixLift 2370681
  have htrace : WordTrace (prefixWord ++ tailWord_2370681) baseStart_2370681 baseEnd_2370681 := by
    simpa [prefixWord, tailWord_2370681, baseEnd_2370681] using wordTrace_append hprefix tailTrace_2370681
  have hstable : (prefixWord ++ tailWord_2370681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2370681).length < 2 ^ (prefixWord ++ tailWord_2370681).sum := by decide
  have hdescent : baseEnd_2370681 < baseStart_2370681 := by decide
  rcases family_descends (prefixWord ++ tailWord_2370681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2370703 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 2, 7, 4]
def baseStart_2370703 : Nat := 118140960795 + 2370703 * 2 ^ 59
def prefixEnd_2370703 : Nat := 4983230072969 + 3 ^ 40 * 2370703 * 2
def baseEnd_2370703 : Nat := 1217310128055943347309841

theorem tailTrace_2370703 : CollatzResearch.WordTrace tailWord_2370703 prefixEnd_2370703 1217310128055943347309841 := by
  unfold tailWord_2370703
  simp only [CollatzResearch.WordTrace]
  refine ⟨86466641930355389683060763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57644427953570259788707175 86466641930355389683060763)
  ·
    refine ⟨129699962895533084524591145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86466641930355389683060763 129699962895533084524591145)
    ·
      refine ⟨97274972171649813393443359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129699962895533084524591145 97274972171649813393443359)
      ·
        refine ⟨145912458257474720090165039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97274972171649813393443359 145912458257474720090165039)
        ·
          refine ⟨218868687386212080135247559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145912458257474720090165039 218868687386212080135247559)
          ·
            refine ⟨328303031079318120202871339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 218868687386212080135247559 328303031079318120202871339)
            ·
              refine ⟨492454546618977180304307009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 328303031079318120202871339 492454546618977180304307009)
              ·
                refine ⟨369340909964232885228230257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 492454546618977180304307009 369340909964232885228230257)
                ·
                  refine ⟨277005682473174663921172693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 369340909964232885228230257 277005682473174663921172693)
                  ·
                    refine ⟨6492320682965031185652485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 277005682473174663921172693 6492320682965031185652485)
                    ·
                      refine ⟨1217310128055943347309841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6492320682965031185652485 1217310128055943347309841)
                      ·
                        rfl

theorem cell23_2370703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 7, 4].length) (baseStart_2370703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2370703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2370703 prefixEnd_2370703 := by exact prefixLift 2370703
  have htrace : WordTrace (prefixWord ++ tailWord_2370703) baseStart_2370703 baseEnd_2370703 := by
    simpa [prefixWord, tailWord_2370703, baseEnd_2370703] using wordTrace_append hprefix tailTrace_2370703
  have hstable : (prefixWord ++ tailWord_2370703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2370703).length < 2 ^ (prefixWord ++ tailWord_2370703).sum := by decide
  have hdescent : baseEnd_2370703 < baseStart_2370703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2370703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2370720 : List Nat := [2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 4]
def baseStart_2370720 : Nat := 118140960795 + 2370720 * 2 ^ 59
def prefixEnd_2370720 : Nat := 4983230072969 + 3 ^ 40 * 2370720 * 2
def baseEnd_2370720 : Nat := 1217318857227069780797263

theorem tailTrace_2370720 : CollatzResearch.WordTrace tailWord_2370720 prefixEnd_2370720 1217318857227069780797263 := by
  unfold tailWord_2370720
  simp only [CollatzResearch.WordTrace]
  refine ⟨43233630985646900793214807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57644841314195867724286409 43233630985646900793214807)
  ·
    refine ⟨64850446478470351189822211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43233630985646900793214807 64850446478470351189822211)
    ·
      refine ⟨97275669717705526784733317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64850446478470351189822211 97275669717705526784733317)
      ·
        refine ⟨18239188072069786272137497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 97275669717705526784733317 18239188072069786272137497)
        ·
          refine ⟨13679391054052339704103123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18239188072069786272137497 13679391054052339704103123)
          ·
            refine ⟨20519086581078509556154685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13679391054052339704103123 20519086581078509556154685)
            ·
              refine ⟨7694657467904441083558007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20519086581078509556154685 7694657467904441083558007)
              ·
                refine ⟨11541986201856661625337011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7694657467904441083558007 11541986201856661625337011)
                ·
                  refine ⟨17312979302784992438005517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11541986201856661625337011 17312979302784992438005517)
                  ·
                    refine ⟨6492367238544372164252069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17312979302784992438005517 6492367238544372164252069)
                    ·
                      refine ⟨1217318857227069780797263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6492367238544372164252069 1217318857227069780797263)
                      ·
                        rfl

theorem cell23_2370720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_2370720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2370720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2370720 prefixEnd_2370720 := by exact prefixLift 2370720
  have htrace : WordTrace (prefixWord ++ tailWord_2370720) baseStart_2370720 baseEnd_2370720 := by
    simpa [prefixWord, tailWord_2370720, baseEnd_2370720] using wordTrace_append hprefix tailTrace_2370720
  have hstable : (prefixWord ++ tailWord_2370720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2370720).length < 2 ^ (prefixWord ++ tailWord_2370720).sum := by decide
  have hdescent : baseEnd_2370720 < baseStart_2370720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2370720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2370760 : List Nat := [2, 1, 3, 1, 2, 1, 2, 5, 6]
def baseStart_2370760 : Nat := 118140960795 + 2370760 * 2 ^ 59
def prefixEnd_2370760 : Nat := 4983230072969 + 3 ^ 40 * 2370760 * 2
def baseEnd_2370760 : Nat := 135259932939249958255231

theorem tailTrace_2370760 : CollatzResearch.WordTrace tailWord_2370760 prefixEnd_2370760 135259932939249958255231 := by
  unfold tailWord_2370760
  simp only [CollatzResearch.WordTrace]
  refine ⟨43234360445574444208942867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57645813927432592278590489 43234360445574444208942867)
  ·
    refine ⟨64851540668361666313414301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43234360445574444208942867 64851540668361666313414301)
    ·
      refine ⟨24319327750635624867530363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64851540668361666313414301 24319327750635624867530363)
      ·
        refine ⟨36478991625953437301295545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24319327750635624867530363 36478991625953437301295545)
        ·
          refine ⟨27359243719465077975971659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36478991625953437301295545 27359243719465077975971659)
          ·
            refine ⟨41038865579197616963957489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27359243719465077975971659 41038865579197616963957489)
            ·
              refine ⟨30779149184398212722968117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41038865579197616963957489 30779149184398212722968117)
              ·
                refine ⟨2885545236037332442778261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30779149184398212722968117 2885545236037332442778261)
                ·
                  refine ⟨135259932939249958255231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2885545236037332442778261 135259932939249958255231)
                  ·
                    rfl

theorem cell23_2370760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 5, 6].length) (baseStart_2370760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2370760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2370760 prefixEnd_2370760 := by exact prefixLift 2370760
  have htrace : WordTrace (prefixWord ++ tailWord_2370760) baseStart_2370760 baseEnd_2370760 := by
    simpa [prefixWord, tailWord_2370760, baseEnd_2370760] using wordTrace_append hprefix tailTrace_2370760
  have hstable : (prefixWord ++ tailWord_2370760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2370760).length < 2 ^ (prefixWord ++ tailWord_2370760).sum := by decide
  have hdescent : baseEnd_2370760 < baseStart_2370760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2370760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2370827 : List Nat := [1, 1, 1, 1, 5, 4, 1, 1, 3, 1, 4]
def baseStart_2370827 : Nat := 118140960795 + 2370827 * 2 ^ 59
def prefixEnd_2370827 : Nat := 4983230072969 + 3 ^ 40 * 2370827 * 2
def baseEnd_2370827 : Nat := 1217373799657100862159271

theorem tailTrace_2370827 : CollatzResearch.WordTrace tailWord_2370827 prefixEnd_2370827 1217373799657100862159271 := by
  unfold tailWord_2370827
  simp only [CollatzResearch.WordTrace]
  refine ⟨86471164581906158860574735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57647443054604105907049823 86471164581906158860574735)
  ·
    refine ⟨129706746872859238290862103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86471164581906158860574735 129706746872859238290862103)
    ·
      refine ⟨194560120309288857436293155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129706746872859238290862103 194560120309288857436293155)
      ·
        refine ⟨291840180463933286154439733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194560120309288857436293155 291840180463933286154439733)
        ·
          refine ⟨27360016918493745576978725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 291840180463933286154439733 27360016918493745576978725)
          ·
            refine ⟨5130003172217577295683511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27360016918493745576978725 5130003172217577295683511)
            ·
              refine ⟨7695004758326365943525267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5130003172217577295683511 7695004758326365943525267)
              ·
                refine ⟨11542507137489548915287901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7695004758326365943525267 11542507137489548915287901)
                ·
                  refine ⟨4328440176558580843232963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11542507137489548915287901 4328440176558580843232963)
                  ·
                    refine ⟨6492660264837871264849445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4328440176558580843232963 6492660264837871264849445)
                    ·
                      refine ⟨1217373799657100862159271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6492660264837871264849445 1217373799657100862159271)
                      ·
                        rfl

theorem cell23_2370827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 1, 3, 1, 4].length) (baseStart_2370827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2370827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2370827 prefixEnd_2370827 := by exact prefixLift 2370827
  have htrace : WordTrace (prefixWord ++ tailWord_2370827) baseStart_2370827 baseEnd_2370827 := by
    simpa [prefixWord, tailWord_2370827, baseEnd_2370827] using wordTrace_append hprefix tailTrace_2370827
  have hstable : (prefixWord ++ tailWord_2370827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2370827).length < 2 ^ (prefixWord ++ tailWord_2370827).sum := by decide
  have hdescent : baseEnd_2370827 < baseStart_2370827 := by decide
  rcases family_descends (prefixWord ++ tailWord_2370827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2370850 : List Nat := [3, 3, 1, 1, 15]
def baseStart_2370850 : Nat := 118140960795 + 2370850 * 2 ^ 59
def prefixEnd_2370850 : Nat := 4983230072969 + 3 ^ 40 * 2370850 * 2
def baseEnd_2370850 : Nat := 1669939107972776779385

theorem tailTrace_2370850 : CollatzResearch.WordTrace tailWord_2370850 prefixEnd_2370850 1669939107972776779385 := by
  unfold tailWord_2370850
  simp only [CollatzResearch.WordTrace]
  refine ⟨21618000865205708447165501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57648002307215222525774669 21618000865205708447165501)
  ·
    refine ⟨8106750324452140667687063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21618000865205708447165501 8106750324452140667687063)
    ·
      refine ⟨12160125486678211001530595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8106750324452140667687063 12160125486678211001530595)
      ·
        refine ⟨18240188230017316502295893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12160125486678211001530595 18240188230017316502295893)
        ·
          refine ⟨1669939107972776779385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 15 18240188230017316502295893 1669939107972776779385)
          ·
            rfl

theorem cell23_2370850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 15].length) (baseStart_2370850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2370850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2370850 prefixEnd_2370850 := by exact prefixLift 2370850
  have htrace : WordTrace (prefixWord ++ tailWord_2370850) baseStart_2370850 baseEnd_2370850 := by
    simpa [prefixWord, tailWord_2370850, baseEnd_2370850] using wordTrace_append hprefix tailTrace_2370850
  have hstable : (prefixWord ++ tailWord_2370850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2370850).length < 2 ^ (prefixWord ++ tailWord_2370850).sum := by decide
  have hdescent : baseEnd_2370850 < baseStart_2370850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2370850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2370867 : List Nat := [1, 1, 1, 2, 5, 4, 1, 8]
def baseStart_2370867 : Nat := 118140960795 + 2370867 * 2 ^ 59
def prefixEnd_2370867 : Nat := 4983230072969 + 3 ^ 40 * 2370867 * 2
def baseEnd_2370867 : Nat := 45088679217899285394781

theorem tailTrace_2370867 : CollatzResearch.WordTrace tailWord_2370867 prefixEnd_2370867 45088679217899285394781 := by
  unfold tailWord_2370867
  simp only [CollatzResearch.WordTrace]
  refine ⟨86472623501761245692030855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57648415667840830461353903 86472623501761245692030855)
  ·
    refine ⟨129708935252641868538046283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86472623501761245692030855 129708935252641868538046283)
    ·
      refine ⟨194563402878962802807069425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129708935252641868538046283 194563402878962802807069425)
      ·
        refine ⟨145922552159222102105302069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194563402878962802807069425 145922552159222102105302069)
        ·
          refine ⟨13680239264927072072372069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 145922552159222102105302069 13680239264927072072372069)
          ·
            refine ⟨2565044862173826013569763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13680239264927072072372069 2565044862173826013569763)
            ·
              refine ⟨3847567293260739020354645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2565044862173826013569763 3847567293260739020354645)
              ·
                refine ⟨45088679217899285394781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3847567293260739020354645 45088679217899285394781)
                ·
                  rfl

theorem cell23_2370867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 8].length) (baseStart_2370867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2370867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2370867 prefixEnd_2370867 := by exact prefixLift 2370867
  have htrace : WordTrace (prefixWord ++ tailWord_2370867) baseStart_2370867 baseEnd_2370867 := by
    simpa [prefixWord, tailWord_2370867, baseEnd_2370867] using wordTrace_append hprefix tailTrace_2370867
  have hstable : (prefixWord ++ tailWord_2370867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2370867).length < 2 ^ (prefixWord ++ tailWord_2370867).sum := by decide
  have hdescent : baseEnd_2370867 < baseStart_2370867 := by decide
  rcases family_descends (prefixWord ++ tailWord_2370867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2370880 : List Nat := [2, 1, 1, 2, 2, 1, 3, 2, 2, 7]
def baseStart_2370880 : Nat := 118140960795 + 2370880 * 2 ^ 59
def prefixEnd_2370880 : Nat := 4983230072969 + 3 ^ 40 * 2370880 * 2
def baseEnd_2370880 : Nat := 405800338043929718265509

theorem tailTrace_2370880 : CollatzResearch.WordTrace tailWord_2370880 prefixEnd_2370880 405800338043929718265509 := by
  unfold tailWord_2370880
  simp only [CollatzResearch.WordTrace]
  refine ⟨43236548825357074456127047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57648731767142765941502729 43236548825357074456127047)
  ·
    refine ⟨64854823238035611684190571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43236548825357074456127047 64854823238035611684190571)
    ·
      refine ⟨97282234857053417526285857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64854823238035611684190571 97282234857053417526285857)
      ·
        refine ⟨72961676142790063144714393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97282234857053417526285857 72961676142790063144714393)
        ·
          refine ⟨54721257107092547358535795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72961676142790063144714393 54721257107092547358535795)
          ·
            refine ⟨82081885660638821037803693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54721257107092547358535795 82081885660638821037803693)
            ·
              refine ⟨30780707122739557889176385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82081885660638821037803693 30780707122739557889176385)
              ·
                refine ⟨23085530342054668416882289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30780707122739557889176385 23085530342054668416882289)
                ·
                  refine ⟨17314147756541001312661717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23085530342054668416882289 17314147756541001312661717)
                  ·
                    refine ⟨405800338043929718265509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17314147756541001312661717 405800338043929718265509)
                    ·
                      rfl

theorem cell23_2370880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 2, 7].length) (baseStart_2370880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2370880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2370880 prefixEnd_2370880 := by exact prefixLift 2370880
  have htrace : WordTrace (prefixWord ++ tailWord_2370880) baseStart_2370880 baseEnd_2370880 := by
    simpa [prefixWord, tailWord_2370880, baseEnd_2370880] using wordTrace_append hprefix tailTrace_2370880
  have hstable : (prefixWord ++ tailWord_2370880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2370880).length < 2 ^ (prefixWord ++ tailWord_2370880).sum := by decide
  have hdescent : baseEnd_2370880 < baseStart_2370880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2370880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2370894 : List Nat := [4, 1, 1, 1, 1, 1, 4, 2, 4, 1, 3]
def baseStart_2370894 : Nat := 118140960795 + 2370894 * 2 ^ 59
def prefixEnd_2370894 : Nat := 4983230072969 + 3 ^ 40 * 2370894 * 2
def baseEnd_2370894 : Nat := 1217408202860952100021463

theorem tailTrace_2370894 : CollatzResearch.WordTrace tailWord_2370894 prefixEnd_2370894 1217408202860952100021463 := by
  unfold tailWord_2370894
  simp only [CollatzResearch.WordTrace]
  refine ⟨10809201034082928662907967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57649072181775619535509157 10809201034082928662907967)
  ·
    refine ⟨16213801551124392994361951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10809201034082928662907967 16213801551124392994361951)
    ·
      refine ⟨24320702326686589491542927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16213801551124392994361951 24320702326686589491542927)
      ·
        refine ⟨36481053490029884237314391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24320702326686589491542927 36481053490029884237314391)
        ·
          refine ⟨54721580235044826355971587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36481053490029884237314391 54721580235044826355971587)
          ·
            refine ⟨82082370352567239533957381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54721580235044826355971587 82082370352567239533957381)
            ·
              refine ⟨15390444441106357412617009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82082370352567239533957381 15390444441106357412617009)
              ·
                refine ⟨11542833330829768059462757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15390444441106357412617009 11542833330829768059462757)
                ·
                  refine ⟨2164281249530581511149267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11542833330829768059462757 2164281249530581511149267)
                  ·
                    refine ⟨3246421874295872266723901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2164281249530581511149267 3246421874295872266723901)
                    ·
                      refine ⟨1217408202860952100021463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3246421874295872266723901 1217408202860952100021463)
                      ·
                        rfl

theorem cell23_2370894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 2, 4, 1, 3].length) (baseStart_2370894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2370894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2370894 prefixEnd_2370894 := by exact prefixLift 2370894
  have htrace : WordTrace (prefixWord ++ tailWord_2370894) baseStart_2370894 baseEnd_2370894 := by
    simpa [prefixWord, tailWord_2370894, baseEnd_2370894] using wordTrace_append hprefix tailTrace_2370894
  have hstable : (prefixWord ++ tailWord_2370894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2370894).length < 2 ^ (prefixWord ++ tailWord_2370894).sum := by decide
  have hdescent : baseEnd_2370894 < baseStart_2370894 := by decide
  rcases family_descends (prefixWord ++ tailWord_2370894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2370937 : List Nat := [1, 2, 1, 3, 2, 1, 2, 2, 2, 4, 3]
def baseStart_2370937 : Nat := 118140960795 + 2370937 * 2 ^ 59
def prefixEnd_2370937 : Nat := 4983230072969 + 3 ^ 40 * 2370937 * 2
def baseEnd_2370937 : Nat := 1217430282529095431783765

theorem tailTrace_2370937 : CollatzResearch.WordTrace tailWord_2370937 prefixEnd_2370937 1217430282529095431783765 := by
  unfold tailWord_2370937
  simp only [CollatzResearch.WordTrace]
  refine ⟨86475176611507647647079065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57650117741005098431386043 86475176611507647647079065)
  ·
    refine ⟨64856382458630735735309299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86475176611507647647079065 64856382458630735735309299)
    ·
      refine ⟨97284573687946103602963949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64856382458630735735309299 97284573687946103602963949)
      ·
        refine ⟨36481715132979788851111481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97284573687946103602963949 36481715132979788851111481)
        ·
          refine ⟨27361286349734841638333611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36481715132979788851111481 27361286349734841638333611)
          ·
            refine ⟨41041929524602262457500417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27361286349734841638333611 41041929524602262457500417)
            ·
              refine ⟨30781447143451696843125313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41041929524602262457500417 30781447143451696843125313)
              ·
                refine ⟨23086085357588772632343985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30781447143451696843125313 23086085357588772632343985)
                ·
                  refine ⟨17314564018191579474257989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23086085357588772632343985 17314564018191579474257989)
                  ·
                    refine ⟨3246480753410921151423373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17314564018191579474257989 3246480753410921151423373)
                    ·
                      refine ⟨1217430282529095431783765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3246480753410921151423373 1217430282529095431783765)
                      ·
                        rfl

theorem cell23_2370937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2, 4, 3].length) (baseStart_2370937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2370937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2370937 prefixEnd_2370937 := by exact prefixLift 2370937
  have htrace : WordTrace (prefixWord ++ tailWord_2370937) baseStart_2370937 baseEnd_2370937 := by
    simpa [prefixWord, tailWord_2370937, baseEnd_2370937] using wordTrace_append hprefix tailTrace_2370937
  have hstable : (prefixWord ++ tailWord_2370937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2370937).length < 2 ^ (prefixWord ++ tailWord_2370937).sum := by decide
  have hdescent : baseEnd_2370937 < baseStart_2370937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2370937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2370951 : List Nat := [1, 1, 4, 2, 2, 2, 1, 2, 4, 2, 2]
def baseStart_2370951 : Nat := 118140960795 + 2370951 * 2 ^ 59
def prefixEnd_2370951 : Nat := 4983230072969 + 3 ^ 40 * 2370951 * 2
def baseEnd_2370951 : Nat := 1217437471258258377008701

theorem tailTrace_2370951 : CollatzResearch.WordTrace tailWord_2370951 prefixEnd_2370951 1217437471258258377008701 := by
  unfold tailWord_2370951
  simp only [CollatzResearch.WordTrace]
  refine ⟨86475687233456928038088707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57650458155637952025392471 86475687233456928038088707)
  ·
    refine ⟨129713530850185392057133061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86475687233456928038088707 129713530850185392057133061)
    ·
      refine ⟨24321287034409761010712449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 129713530850185392057133061 24321287034409761010712449)
      ·
        refine ⟨18240965275807320758034337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24321287034409761010712449 18240965275807320758034337)
        ·
          refine ⟨13680723956855490568525753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18240965275807320758034337 13680723956855490568525753)
          ·
            refine ⟨10260542967641617926394315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13680723956855490568525753 10260542967641617926394315)
            ·
              refine ⟨15390814451462426889591473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10260542967641617926394315 15390814451462426889591473)
              ·
                refine ⟨11543110838596820167193605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15390814451462426889591473 11543110838596820167193605)
                ·
                  refine ⟨2164333282236903781348801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11543110838596820167193605 2164333282236903781348801)
                  ·
                    refine ⟨1623249961677677836011601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2164333282236903781348801 1623249961677677836011601)
                    ·
                      refine ⟨1217437471258258377008701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1623249961677677836011601 1217437471258258377008701)
                      ·
                        rfl

theorem cell23_2370951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 2, 4, 2, 2].length) (baseStart_2370951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2370951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2370951 prefixEnd_2370951 := by exact prefixLift 2370951
  have htrace : WordTrace (prefixWord ++ tailWord_2370951) baseStart_2370951 baseEnd_2370951 := by
    simpa [prefixWord, tailWord_2370951, baseEnd_2370951] using wordTrace_append hprefix tailTrace_2370951
  have hstable : (prefixWord ++ tailWord_2370951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2370951).length < 2 ^ (prefixWord ++ tailWord_2370951).sum := by decide
  have hdescent : baseEnd_2370951 < baseStart_2370951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2370951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2370994 : List Nat := [3, 2, 1, 1, 1, 1, 2, 1, 4, 5, 2]
def baseStart_2370994 : Nat := 118140960795 + 2370994 * 2 ^ 59
def prefixEnd_2370994 : Nat := 4983230072969 + 3 ^ 40 * 2370994 * 2
def baseEnd_2370994 : Nat := 1217459550926401708771003

theorem tailTrace_2370994 : CollatzResearch.WordTrace tailWord_2370994 prefixEnd_2370994 1217459550926401708771003 := by
  unfold tailWord_2370994
  simp only [CollatzResearch.WordTrace]
  refine ⟨21619313893075286595476009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57651503714867430921269357 21619313893075286595476009)
  ·
    refine ⟨16214485419806464946607007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21619313893075286595476009 16214485419806464946607007)
    ·
      refine ⟨24321728129709697419910511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16214485419806464946607007 24321728129709697419910511)
      ·
        refine ⟨36482592194564546129865767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24321728129709697419910511 36482592194564546129865767)
        ·
          refine ⟨54723888291846819194798651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36482592194564546129865767 54723888291846819194798651)
          ·
            refine ⟨82085832437770228792197977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54723888291846819194798651 82085832437770228792197977)
            ·
              refine ⟨61564374328327671594148483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82085832437770228792197977 61564374328327671594148483)
              ·
                refine ⟨92346561492491507391222725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61564374328327671594148483 92346561492491507391222725)
                ·
                  refine ⟨17314980279842157635854261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 92346561492491507391222725 17314980279842157635854261)
                  ·
                    refine ⟨1623279401235202278361337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17314980279842157635854261 1623279401235202278361337)
                    ·
                      refine ⟨1217459550926401708771003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1623279401235202278361337 1217459550926401708771003)
                      ·
                        rfl

theorem cell23_2370994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 4, 5, 2].length) (baseStart_2370994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2370994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2370994 prefixEnd_2370994 := by exact prefixLift 2370994
  have htrace : WordTrace (prefixWord ++ tailWord_2370994) baseStart_2370994 baseEnd_2370994 := by
    simpa [prefixWord, tailWord_2370994, baseEnd_2370994] using wordTrace_append hprefix tailTrace_2370994
  have hstable : (prefixWord ++ tailWord_2370994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2370994).length < 2 ^ (prefixWord ++ tailWord_2370994).sum := by decide
  have hdescent : baseEnd_2370994 < baseStart_2370994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2370994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2371007 : List Nat := [1, 1, 2, 2, 2, 1, 1, 5, 1, 3, 4]
def baseStart_2371007 : Nat := 118140960795 + 2371007 * 2 ^ 59
def prefixEnd_2371007 : Nat := 4983230072969 + 3 ^ 40 * 2371007 * 2
def baseEnd_2371007 : Nat := 1217466226174910157908443

theorem tailTrace_2371007 : CollatzResearch.WordTrace tailWord_2371007 prefixEnd_2371007 1217466226174910157908443 := by
  unfold tailWord_2371007
  simp only [CollatzResearch.WordTrace]
  refine ⟨86477729721254049602127275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57651819814169366401418183 86477729721254049602127275)
  ·
    refine ⟨129716594581881074403190913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86477729721254049602127275 129716594581881074403190913)
    ·
      refine ⟨97287445936410805802393185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129716594581881074403190913 97287445936410805802393185)
      ·
        refine ⟨72965584452308104351794889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97287445936410805802393185 72965584452308104351794889)
        ·
          refine ⟨54724188339231078263846167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72965584452308104351794889 54724188339231078263846167)
          ·
            refine ⟨82086282508846617395769251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54724188339231078263846167 82086282508846617395769251)
            ·
              refine ⟨123129423763269926093653877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82086282508846617395769251 123129423763269926093653877)
              ·
                refine ⟨11543383477806555571280051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 123129423763269926093653877 11543383477806555571280051)
                ·
                  refine ⟨17315075216709833356920077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11543383477806555571280051 17315075216709833356920077)
                  ·
                    refine ⟨6493153206266187508845029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17315075216709833356920077 6493153206266187508845029)
                    ·
                      refine ⟨1217466226174910157908443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6493153206266187508845029 1217466226174910157908443)
                      ·
                        rfl

theorem cell23_2371007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5, 1, 3, 4].length) (baseStart_2371007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2371007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2371007 prefixEnd_2371007 := by exact prefixLift 2371007
  have htrace : WordTrace (prefixWord ++ tailWord_2371007) baseStart_2371007 baseEnd_2371007 := by
    simpa [prefixWord, tailWord_2371007, baseEnd_2371007] using wordTrace_append hprefix tailTrace_2371007
  have hstable : (prefixWord ++ tailWord_2371007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2371007).length < 2 ^ (prefixWord ++ tailWord_2371007).sum := by decide
  have hdescent : baseEnd_2371007 < baseStart_2371007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2371007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2371024 : List Nat := [2, 1, 1, 1, 1, 2, 2, 3, 4, 4, 2]
def baseStart_2371024 : Nat := 118140960795 + 2371024 * 2 ^ 59
def prefixEnd_2371024 : Nat := 4983230072969 + 3 ^ 40 * 2371024 * 2
def baseEnd_2371024 : Nat := 1217474955346036591395865

theorem tailTrace_2371024 : CollatzResearch.WordTrace tailWord_2371024 prefixEnd_2371024 1217474955346036591395865 := by
  unfold tailWord_2371024
  simp only [CollatzResearch.WordTrace]
  refine ⟨43239174881096230752748063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57652233174794974336997417 43239174881096230752748063)
  ·
    refine ⟨64858762321644346129122095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43239174881096230752748063 64858762321644346129122095)
    ·
      refine ⟨97288143482466519193683143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64858762321644346129122095 97288143482466519193683143)
      ·
        refine ⟨145932215223699778790524715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97288143482466519193683143 145932215223699778790524715)
        ·
          refine ⟨218898322835549668185787073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145932215223699778790524715 218898322835549668185787073)
          ·
            refine ⟨164173742126662251139340305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 218898322835549668185787073 164173742126662251139340305)
            ·
              refine ⟨123130306594996688354505229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 164173742126662251139340305 123130306594996688354505229)
              ·
                refine ⟨46173864973123758132939461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 123130306594996688354505229 46173864973123758132939461)
                ·
                  refine ⟨8657599682460704649926149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46173864973123758132939461 8657599682460704649926149)
                  ·
                    refine ⟨1623299940461382121861153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8657599682460704649926149 1623299940461382121861153)
                    ·
                      refine ⟨1217474955346036591395865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1623299940461382121861153 1217474955346036591395865)
                      ·
                        rfl

theorem cell23_2371024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 4, 4, 2].length) (baseStart_2371024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2371024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2371024 prefixEnd_2371024 := by exact prefixLift 2371024
  have htrace : WordTrace (prefixWord ++ tailWord_2371024) baseStart_2371024 baseEnd_2371024 := by
    simpa [prefixWord, tailWord_2371024, baseEnd_2371024] using wordTrace_append hprefix tailTrace_2371024
  have hstable : (prefixWord ++ tailWord_2371024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2371024).length < 2 ^ (prefixWord ++ tailWord_2371024).sum := by decide
  have hdescent : baseEnd_2371024 < baseStart_2371024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2371024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2371041 : List Nat := [1, 2, 3, 1, 2, 4, 1, 1, 2, 4, 2]
def baseStart_2371041 : Nat := 118140960795 + 2371041 * 2 ^ 59
def prefixEnd_2371041 : Nat := 4983230072969 + 3 ^ 40 * 2371041 * 2
def baseEnd_2371041 : Nat := 1217483684517163024883287

theorem tailTrace_2371041 : CollatzResearch.WordTrace tailWord_2371041 prefixEnd_2371041 1217483684517163024883287 := by
  unfold tailWord_2371041
  simp only [CollatzResearch.WordTrace]
  refine ⟨86478969803130873408864977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57652646535420582272576651 86478969803130873408864977)
  ·
    refine ⟨64859227352348155056648733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86478969803130873408864977 64859227352348155056648733)
    ·
      refine ⟨24322210257130558146243275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64859227352348155056648733 24322210257130558146243275)
      ·
        refine ⟨36483315385695837219364913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24322210257130558146243275 36483315385695837219364913)
        ·
          refine ⟨27362486539271877914523685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36483315385695837219364913 27362486539271877914523685)
          ·
            refine ⟨5130466226113477108973191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27362486539271877914523685 5130466226113477108973191)
            ·
              refine ⟨7695699339170215663459787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5130466226113477108973191 7695699339170215663459787)
              ·
                refine ⟨11543549008755323495189681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7695699339170215663459787 11543549008755323495189681)
                ·
                  refine ⟨8657661756566492621392261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11543549008755323495189681 8657661756566492621392261)
                  ·
                    refine ⟨1623311579356217366511049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8657661756566492621392261 1623311579356217366511049)
                    ·
                      refine ⟨1217483684517163024883287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1623311579356217366511049 1217483684517163024883287)
                      ·
                        rfl

theorem cell23_2371041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 1, 2, 4, 2].length) (baseStart_2371041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2371041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2371041 prefixEnd_2371041 := by exact prefixLift 2371041
  have htrace : WordTrace (prefixWord ++ tailWord_2371041) baseStart_2371041 baseEnd_2371041 := by
    simpa [prefixWord, tailWord_2371041, baseEnd_2371041] using wordTrace_append hprefix tailTrace_2371041
  have hstable : (prefixWord ++ tailWord_2371041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2371041).length < 2 ^ (prefixWord ++ tailWord_2371041).sum := by decide
  have hdescent : baseEnd_2371041 < baseStart_2371041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2371041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2371044 : List Nat := [2, 3, 1, 1, 1, 1, 1, 4, 4, 2, 3]
def baseStart_2371044 : Nat := 118140960795 + 2371044 * 2 ^ 59
def prefixEnd_2371044 : Nat := 4983230072969 + 3 ^ 40 * 2371044 * 2
def baseEnd_2371044 : Nat := 1217485224959126513145773

theorem tailTrace_2371044 : CollatzResearch.WordTrace tailWord_2371044 prefixEnd_2371044 1217485224959126513145773 := by
  unfold tailWord_2371044
  simp only [CollatzResearch.WordTrace]
  refine ⟨43239539611060002460612093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57652719481413336614149457 43239539611060002460612093)
  ·
    refine ⟨16214827354147500922729535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43239539611060002460612093 16214827354147500922729535)
    ·
      refine ⟨24322241031221251384094303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16214827354147500922729535 24322241031221251384094303)
      ·
        refine ⟨36483361546831877076141455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24322241031221251384094303 36483361546831877076141455)
        ·
          refine ⟨54725042320247815614212183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36483361546831877076141455 54725042320247815614212183)
          ·
            refine ⟨82087563480371723421318275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54725042320247815614212183 82087563480371723421318275)
            ·
              refine ⟨123131345220557585131977413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82087563480371723421318275 123131345220557585131977413)
              ·
                refine ⟨23087127228854547212245765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 123131345220557585131977413 23087127228854547212245765)
                ·
                  refine ⟨4328836355410227602296081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23087127228854547212245765 4328836355410227602296081)
                  ·
                    refine ⟨3246627266557670701722061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4328836355410227602296081 3246627266557670701722061)
                    ·
                      refine ⟨1217485224959126513145773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3246627266557670701722061 1217485224959126513145773)
                      ·
                        rfl

theorem cell23_2371044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 4, 2, 3].length) (baseStart_2371044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2371044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2371044 prefixEnd_2371044 := by exact prefixLift 2371044
  have htrace : WordTrace (prefixWord ++ tailWord_2371044) baseStart_2371044 baseEnd_2371044 := by
    simpa [prefixWord, tailWord_2371044, baseEnd_2371044] using wordTrace_append hprefix tailTrace_2371044
  have hstable : (prefixWord ++ tailWord_2371044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2371044).length < 2 ^ (prefixWord ++ tailWord_2371044).sum := by decide
  have hdescent : baseEnd_2371044 < baseStart_2371044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2371044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2371058 : List Nat := [3, 2, 1, 4, 1, 3, 1, 1, 2, 1, 4]
def baseStart_2371058 : Nat := 118140960795 + 2371058 * 2 ^ 59
def prefixEnd_2371058 : Nat := 4983230072969 + 3 ^ 40 * 2371058 * 2
def baseEnd_2371058 : Nat := 1217492413688289458370709

theorem tailTrace_2371058 : CollatzResearch.WordTrace tailWord_2371058 prefixEnd_2371058 1217492413688289458370709 := by
  unfold tailWord_2371058
  simp only [CollatzResearch.WordTrace]
  refine ⟨21619897461017321328058457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57653059896046190208155885 21619897461017321328058457)
  ·
    refine ⟨16214923095762990996043843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21619897461017321328058457 16214923095762990996043843)
    ·
      refine ⟨24322384643644486494065765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16214923095762990996043843 24322384643644486494065765)
      ·
        refine ⟨4560447120683341217637331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24322384643644486494065765 4560447120683341217637331)
        ·
          refine ⟨6840670681025011826455997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4560447120683341217637331 6840670681025011826455997)
          ·
            refine ⟨2565251505384379434920999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6840670681025011826455997 2565251505384379434920999)
            ·
              refine ⟨3847877258076569152381499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2565251505384379434920999 3847877258076569152381499)
              ·
                refine ⟨5771815887114853728572249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3847877258076569152381499 5771815887114853728572249)
                ·
                  refine ⟨4328861915336140296429187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5771815887114853728572249 4328861915336140296429187)
                  ·
                    refine ⟨6493292873004210444643781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4328861915336140296429187 6493292873004210444643781)
                    ·
                      refine ⟨1217492413688289458370709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6493292873004210444643781 1217492413688289458370709)
                      ·
                        rfl

theorem cell23_2371058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_2371058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2371058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2371058 prefixEnd_2371058 := by exact prefixLift 2371058
  have htrace : WordTrace (prefixWord ++ tailWord_2371058) baseStart_2371058 baseEnd_2371058 := by
    simpa [prefixWord, tailWord_2371058, baseEnd_2371058] using wordTrace_append hprefix tailTrace_2371058
  have hstable : (prefixWord ++ tailWord_2371058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2371058).length < 2 ^ (prefixWord ++ tailWord_2371058).sum := by decide
  have hdescent : baseEnd_2371058 < baseStart_2371058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2371058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2371091 : List Nat := [1, 1, 1, 2, 1, 6, 1, 3, 3, 1, 3]
def baseStart_2371091 : Nat := 118140960795 + 2371091 * 2 ^ 59
def prefixEnd_2371091 : Nat := 4983230072969 + 3 ^ 40 * 2371091 * 2
def baseEnd_2371091 : Nat := 1217509358549887829258057

theorem tailTrace_2371091 : CollatzResearch.WordTrace tailWord_2371091 prefixEnd_2371091 1217509358549887829258057 := by
  unfold tailWord_2371091
  simp only [CollatzResearch.WordTrace]
  refine ⟨86480793452949731948185127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57653862301966487965456751 86480793452949731948185127)
  ·
    refine ⟨129721190179424597922277691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86480793452949731948185127 129721190179424597922277691)
    ·
      refine ⟨194581785269136896883416537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129721190179424597922277691 194581785269136896883416537)
      ·
        refine ⟨145936338951852672662562403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194581785269136896883416537 145936338951852672662562403)
        ·
          refine ⟨218904508427779008993843605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145936338951852672662562403 218904508427779008993843605)
          ·
            refine ⟨10261148832552141046586419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 218904508427779008993843605 10261148832552141046586419)
            ·
              refine ⟨15391723248828211569879629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10261148832552141046586419 15391723248828211569879629)
              ·
                refine ⟨5771896218310579338704861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15391723248828211569879629 5771896218310579338704861)
                ·
                  refine ⟨2164461081866467252014323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5771896218310579338704861 2164461081866467252014323)
                  ·
                    refine ⟨3246691622799700878021485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2164461081866467252014323 3246691622799700878021485)
                    ·
                      refine ⟨1217509358549887829258057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3246691622799700878021485 1217509358549887829258057)
                      ·
                        rfl

theorem cell23_2371091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 3, 3, 1, 3].length) (baseStart_2371091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2371091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2371091 prefixEnd_2371091 := by exact prefixLift 2371091
  have htrace : WordTrace (prefixWord ++ tailWord_2371091) baseStart_2371091 baseEnd_2371091 := by
    simpa [prefixWord, tailWord_2371091, baseEnd_2371091] using wordTrace_append hprefix tailTrace_2371091
  have hstable : (prefixWord ++ tailWord_2371091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2371091).length < 2 ^ (prefixWord ++ tailWord_2371091).sum := by decide
  have hdescent : baseEnd_2371091 < baseStart_2371091 := by decide
  rcases family_descends (prefixWord ++ tailWord_2371091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2371101 : List Nat := [1, 4, 2, 2, 1, 1, 1, 1, 3, 5, 2]
def baseStart_2371101 : Nat := 118140960795 + 2371101 * 2 ^ 59
def prefixEnd_2371101 : Nat := 4983230072969 + 3 ^ 40 * 2371101 * 2
def baseEnd_2371101 : Nat := 1217514493356432790133011

theorem tailTrace_2371101 : CollatzResearch.WordTrace tailWord_2371101 prefixEnd_2371101 1217514493356432790133011 := by
  unfold tailWord_2371101
  simp only [CollatzResearch.WordTrace]
  refine ⟨86481158182913503656049157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57654105455275669104032771 86481158182913503656049157)
  ·
    refine ⟨16215217159296281935509217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86481158182913503656049157 16215217159296281935509217)
    ·
      refine ⟨12161412869472211451631913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16215217159296281935509217 12161412869472211451631913)
      ·
        refine ⟨9121059652104158588723935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12161412869472211451631913 9121059652104158588723935)
        ·
          refine ⟨13681589478156237883085903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9121059652104158588723935 13681589478156237883085903)
          ·
            refine ⟨20522384217234356824628855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13681589478156237883085903 20522384217234356824628855)
            ·
              refine ⟨30783576325851535236943283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20522384217234356824628855 30783576325851535236943283)
              ·
                refine ⟨46175364488777302855414925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30783576325851535236943283 46175364488777302855414925)
                ·
                  refine ⟨17315761683291488570780597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46175364488777302855414925 17315761683291488570780597)
                  ·
                    refine ⟨1623352657808577053510681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17315761683291488570780597 1623352657808577053510681)
                    ·
                      refine ⟨1217514493356432790133011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1623352657808577053510681 1217514493356432790133011)
                      ·
                        rfl

theorem cell23_2371101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 3, 5, 2].length) (baseStart_2371101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2371101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2371101 prefixEnd_2371101 := by exact prefixLift 2371101
  have htrace : WordTrace (prefixWord ++ tailWord_2371101) baseStart_2371101 baseEnd_2371101 := by
    simpa [prefixWord, tailWord_2371101, baseEnd_2371101] using wordTrace_append hprefix tailTrace_2371101
  have hstable : (prefixWord ++ tailWord_2371101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2371101).length < 2 ^ (prefixWord ++ tailWord_2371101).sum := by decide
  have hdescent : baseEnd_2371101 < baseStart_2371101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2371101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
