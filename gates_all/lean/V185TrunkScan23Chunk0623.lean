import V185TrunkScan23Chunk0622

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3683945 : List Nat := [1, 2, 1, 1, 1, 4, 2, 4, 7]
def baseStart_3683945 : Nat := 118140960795 + 3683945 * 2 ^ 59
def prefixEnd_3683945 : Nat := 4983230072969 + 3 ^ 40 * 3683945 * 2
def baseEnd_3683945 : Nat := 210181609969743809105039

theorem tailTrace_3683945 : CollatzResearch.WordTrace tailWord_3683945 prefixEnd_3683945 210181609969743809105039 := by
  unfold tailWord_3683945
  simp only [CollatzResearch.WordTrace]
  refine ⟨134364512638703907560509289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89576341759135938373672859 134364512638703907560509289)
  ·
    refine ⟨100773384479027930670381967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134364512638703907560509289 100773384479027930670381967)
    ·
      refine ⟨151160076718541896005572951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100773384479027930670381967 151160076718541896005572951)
      ·
        refine ⟨226740115077812844008359427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151160076718541896005572951 226740115077812844008359427)
        ·
          refine ⟨340110172616719266012539141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226740115077812844008359427 340110172616719266012539141)
          ·
            refine ⟨63770657365634862377351089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 340110172616719266012539141 63770657365634862377351089)
            ·
              refine ⟨47827993024226146783013317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63770657365634862377351089 47827993024226146783013317)
              ·
                refine ⟨8967748692042402521814997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47827993024226146783013317 8967748692042402521814997)
                ·
                  refine ⟨210181609969743809105039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8967748692042402521814997 210181609969743809105039)
                  ·
                    rfl

theorem cell23_3683945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 4, 7].length) (baseStart_3683945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3683945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3683945 prefixEnd_3683945 := by exact prefixLift 3683945
  have htrace : WordTrace (prefixWord ++ tailWord_3683945) baseStart_3683945 baseEnd_3683945 := by
    simpa [prefixWord, tailWord_3683945, baseEnd_3683945] using wordTrace_append hprefix tailTrace_3683945
  have hstable : (prefixWord ++ tailWord_3683945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683945).length < 2 ^ (prefixWord ++ tailWord_3683945).sum := by decide
  have hdescent : baseEnd_3683945 < baseStart_3683945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683985 : List Nat := [1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 7]
def baseStart_3683985 : Nat := 118140960795 + 3683985 * 2 ^ 59
def prefixEnd_3683985 : Nat := 4983230072969 + 3 ^ 40 * 3683985 * 2
def baseEnd_3683985 : Nat := 1891655028953874125445167

theorem tailTrace_3683985 : CollatzResearch.WordTrace tailWord_3683985 prefixEnd_3683985 1891655028953874125445167 := by
  unfold tailWord_3683985
  simp only [CollatzResearch.WordTrace]
  refine ⟨134365971558558994391965409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89577314372372662927976939 134365971558558994391965409)
  ·
    refine ⟨100774478668919245793974057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134365971558558994391965409 100774478668919245793974057)
    ·
      refine ⟨75580859001689434345480543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100774478668919245793974057 75580859001689434345480543)
      ·
        refine ⟨113371288502534151518220815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75580859001689434345480543 113371288502534151518220815)
        ·
          refine ⟨170056932753801227277331223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113371288502534151518220815 170056932753801227277331223)
          ·
            refine ⟨255085399130701840915996835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170056932753801227277331223 255085399130701840915996835)
            ·
              refine ⟨382628098696052761373995253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255085399130701840915996835 382628098696052761373995253)
              ·
                refine ⟨35871384252754946378812055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 382628098696052761373995253 35871384252754946378812055)
                ·
                  refine ⟨53807076379132419568218083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35871384252754946378812055 53807076379132419568218083)
                  ·
                    refine ⟨80710614568698629352327125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53807076379132419568218083 80710614568698629352327125)
                    ·
                      refine ⟨1891655028953874125445167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 80710614568698629352327125 1891655028953874125445167)
                      ·
                        rfl

theorem cell23_3683985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 7].length) (baseStart_3683985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3683985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3683985 prefixEnd_3683985 := by exact prefixLift 3683985
  have htrace : WordTrace (prefixWord ++ tailWord_3683985) baseStart_3683985 baseEnd_3683985 := by
    simpa [prefixWord, tailWord_3683985, baseEnd_3683985] using wordTrace_append hprefix tailTrace_3683985
  have hstable : (prefixWord ++ tailWord_3683985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683985).length < 2 ^ (prefixWord ++ tailWord_3683985).sum := by decide
  have hdescent : baseEnd_3683985 < baseStart_3683985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684029 : List Nat := [1, 4, 1, 2, 1, 2, 1, 1, 4, 4, 2]
def baseStart_3684029 : Nat := 118140960795 + 3684029 * 2 ^ 59
def prefixEnd_3684029 : Nat := 4983230072969 + 3 ^ 40 * 3684029 * 2
def baseEnd_3684029 : Nat := 1891677622102671953294965

theorem tailTrace_3684029 : CollatzResearch.WordTrace tailWord_3684029 prefixEnd_3684029 1891677622102671953294965 := by
  unfold tailWord_3684029
  simp only [CollatzResearch.WordTrace]
  refine ⟨134367576370399589906567141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89578384246933059937711427 134367576370399589906567141)
  ·
    refine ⟨25193920569449923107481339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134367576370399589906567141 25193920569449923107481339)
    ·
      refine ⟨37790880854174884661222009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25193920569449923107481339 37790880854174884661222009)
      ·
        refine ⟨28343160640631163495916507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37790880854174884661222009 28343160640631163495916507)
        ·
          refine ⟨42514740960946745243874761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28343160640631163495916507 42514740960946745243874761)
          ·
            refine ⟨31886055720710058932906071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42514740960946745243874761 31886055720710058932906071)
            ·
              refine ⟨47829083581065088399359107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31886055720710058932906071 47829083581065088399359107)
              ·
                refine ⟨71743625371597632599038661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47829083581065088399359107 71743625371597632599038661)
                ·
                  refine ⟨13451929757174556112319749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71743625371597632599038661 13451929757174556112319749)
                  ·
                    refine ⟨2522236829470229271059953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13451929757174556112319749 2522236829470229271059953)
                    ·
                      refine ⟨1891677622102671953294965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2522236829470229271059953 1891677622102671953294965)
                      ·
                        rfl

theorem cell23_3684029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 4, 4, 2].length) (baseStart_3684029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3684029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3684029 prefixEnd_3684029 := by exact prefixLift 3684029
  have htrace : WordTrace (prefixWord ++ tailWord_3684029) baseStart_3684029 baseEnd_3684029 := by
    simpa [prefixWord, tailWord_3684029, baseEnd_3684029] using wordTrace_append hprefix tailTrace_3684029
  have hstable : (prefixWord ++ tailWord_3684029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684029).length < 2 ^ (prefixWord ++ tailWord_3684029).sum := by decide
  have hdescent : baseEnd_3684029 < baseStart_3684029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684039 : List Nat := [1, 1, 4, 1, 1, 1, 6, 1, 3, 4]
def baseStart_3684039 : Nat := 118140960795 + 3684039 * 2 ^ 59
def prefixEnd_3684039 : Nat := 4983230072969 + 3 ^ 40 * 3684039 * 2
def baseEnd_3684039 : Nat := 630560918969738971389973

theorem tailTrace_3684039 : CollatzResearch.WordTrace tailWord_3684039 prefixEnd_3684039 630560918969738971389973 := by
  unfold tailWord_3684039
  simp only [CollatzResearch.WordTrace]
  refine ⟨134367941100363361614431171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89578627400242241076287447 134367941100363361614431171)
  ·
    refine ⟨201551911650545042421646757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134367941100363361614431171 201551911650545042421646757)
    ·
      refine ⟨37790983434477195454058767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 201551911650545042421646757 37790983434477195454058767)
      ·
        refine ⟨56686475151715793181088151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37790983434477195454058767 56686475151715793181088151)
        ·
          refine ⟨85029712727573689771632227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56686475151715793181088151 85029712727573689771632227)
          ·
            refine ⟨127544569091360534657448341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85029712727573689771632227 127544569091360534657448341)
            ·
              refine ⟨5978651676157525062067891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 127544569091360534657448341 5978651676157525062067891)
              ·
                refine ⟨8967977514236287593101837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5978651676157525062067891 8967977514236287593101837)
                ·
                  refine ⟨3362991567838607847413189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8967977514236287593101837 3362991567838607847413189)
                  ·
                    refine ⟨630560918969738971389973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3362991567838607847413189 630560918969738971389973)
                    ·
                      rfl

theorem cell23_3684039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 1, 3, 4].length) (baseStart_3684039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3684039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3684039 prefixEnd_3684039 := by exact prefixLift 3684039
  have htrace : WordTrace (prefixWord ++ tailWord_3684039) baseStart_3684039 baseEnd_3684039 := by
    simpa [prefixWord, tailWord_3684039, baseEnd_3684039] using wordTrace_append hprefix tailTrace_3684039
  have hstable : (prefixWord ++ tailWord_3684039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684039).length < 2 ^ (prefixWord ++ tailWord_3684039).sum := by decide
  have hdescent : baseEnd_3684039 < baseStart_3684039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684103 : List Nat := [1, 1, 4, 4, 2, 2, 2, 1, 6]
def baseStart_3684103 : Nat := 118140960795 + 3684103 * 2 ^ 59
def prefixEnd_3684103 : Nat := 4983230072969 + 3 ^ 40 * 3684103 * 2
def baseEnd_3684103 : Nat := 210190624407900518196625

theorem tailTrace_3684103 : CollatzResearch.WordTrace tailWord_3684103 prefixEnd_3684103 210190624407900518196625 := by
  unfold tailWord_3684103
  simp only [CollatzResearch.WordTrace]
  refine ⟨134370275372131500544760963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89580183581421000363173975 134370275372131500544760963)
  ·
    refine ⟨201555413058197250817141445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134370275372131500544760963 201555413058197250817141445)
    ·
      refine ⟨37791639948411984528214021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 201555413058197250817141445 37791639948411984528214021)
      ·
        refine ⟨7085932490327247099040129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37791639948411984528214021 7085932490327247099040129)
        ·
          refine ⟨5314449367745435324280097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7085932490327247099040129 5314449367745435324280097)
          ·
            refine ⟨3985837025809076493210073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5314449367745435324280097 3985837025809076493210073)
            ·
              refine ⟨2989377769356807369907555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3985837025809076493210073 2989377769356807369907555)
              ·
                refine ⟨4484066654035211054861333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2989377769356807369907555 4484066654035211054861333)
                ·
                  refine ⟨210190624407900518196625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4484066654035211054861333 210190624407900518196625)
                  ·
                    rfl

theorem cell23_3684103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 2, 1, 6].length) (baseStart_3684103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3684103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3684103 prefixEnd_3684103 := by exact prefixLift 3684103
  have htrace : WordTrace (prefixWord ++ tailWord_3684103) baseStart_3684103 baseEnd_3684103 := by
    simpa [prefixWord, tailWord_3684103, baseEnd_3684103] using wordTrace_append hprefix tailTrace_3684103
  have hstable : (prefixWord ++ tailWord_3684103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684103).length < 2 ^ (prefixWord ++ tailWord_3684103).sum := by decide
  have hdescent : baseEnd_3684103 < baseStart_3684103 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684129 : List Nat := [1, 2, 3, 2, 1, 4, 1, 2, 1, 6]
def baseStart_3684129 : Nat := 118140960795 + 3684129 * 2 ^ 59
def prefixEnd_3684129 : Nat := 4983230072969 + 3 ^ 40 * 3684129 * 2
def baseEnd_3684129 : Nat := 630576323389373854014835

theorem tailTrace_3684129 : CollatzResearch.WordTrace tailWord_3684129 prefixEnd_3684129 630576323389373854014835 := by
  unfold tailWord_3684129
  simp only [CollatzResearch.WordTrace]
  refine ⟨134371223670037306985207441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89580815780024871323471627 134371223670037306985207441)
  ·
    refine ⟨100778417752527980238905581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134371223670037306985207441 100778417752527980238905581)
    ·
      refine ⟨37791906657197992589589593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100778417752527980238905581 37791906657197992589589593)
      ·
        refine ⟨28343929992898494442192195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37791906657197992589589593 28343929992898494442192195)
        ·
          refine ⟨42515894989347741663288293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28343929992898494442192195 42515894989347741663288293)
          ·
            refine ⟨7971730310502701561866555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42515894989347741663288293 7971730310502701561866555)
            ·
              refine ⟨11957595465754052342799833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7971730310502701561866555 11957595465754052342799833)
              ·
                refine ⟨8968196599315539257099875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11957595465754052342799833 8968196599315539257099875)
                ·
                  refine ⟨13452294898973308885649813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8968196599315539257099875 13452294898973308885649813)
                  ·
                    refine ⟨630576323389373854014835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13452294898973308885649813 630576323389373854014835)
                    ·
                      rfl

theorem cell23_3684129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 2, 1, 6].length) (baseStart_3684129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3684129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3684129 prefixEnd_3684129 := by exact prefixLift 3684129
  have htrace : WordTrace (prefixWord ++ tailWord_3684129) baseStart_3684129 baseEnd_3684129 := by
    simpa [prefixWord, tailWord_3684129, baseEnd_3684129] using wordTrace_append hprefix tailTrace_3684129
  have hstable : (prefixWord ++ tailWord_3684129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684129).length < 2 ^ (prefixWord ++ tailWord_3684129).sum := by decide
  have hdescent : baseEnd_3684129 < baseStart_3684129 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684146 : List Nat := [3, 2, 1, 1, 3, 2, 1, 4, 2, 4]
def baseStart_3684146 : Nat := 118140960795 + 3684146 * 2 ^ 59
def prefixEnd_3684146 : Nat := 4983230072969 + 3 ^ 40 * 3684146 * 2
def baseEnd_3684146 : Nat := 630579233113082665177309

theorem tailTrace_3684146 : CollatzResearch.WordTrace tailWord_3684146 prefixEnd_3684146 630579233113082665177309 := by
  unfold tailWord_3684146
  simp only [CollatzResearch.WordTrace]
  refine ⟨33592960927743929722144073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89581229140650479259050861 33592960927743929722144073)
  ·
    refine ⟨25194720695807947291608055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33592960927743929722144073 25194720695807947291608055)
    ·
      refine ⟨37792081043711920937412083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25194720695807947291608055 37792081043711920937412083)
      ·
        refine ⟨56688121565567881406118125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37792081043711920937412083 56688121565567881406118125)
        ·
          refine ⟨21258045587087955527294297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56688121565567881406118125 21258045587087955527294297)
          ·
            refine ⟨15943534190315966645470723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21258045587087955527294297 15943534190315966645470723)
            ·
              refine ⟨23915301285473949968206085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15943534190315966645470723 23915301285473949968206085)
              ·
                refine ⟨4484118991026365619038641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23915301285473949968206085 4484118991026365619038641)
                ·
                  refine ⟨3363089243269774214278981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4484118991026365619038641 3363089243269774214278981)
                  ·
                    refine ⟨630579233113082665177309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3363089243269774214278981 630579233113082665177309)
                    ·
                      rfl

theorem cell23_3684146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 4, 2, 4].length) (baseStart_3684146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3684146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3684146 prefixEnd_3684146 := by exact prefixLift 3684146
  have htrace : WordTrace (prefixWord ++ tailWord_3684146) baseStart_3684146 baseEnd_3684146 := by
    simpa [prefixWord, tailWord_3684146, baseEnd_3684146] using wordTrace_append hprefix tailTrace_3684146
  have hstable : (prefixWord ++ tailWord_3684146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684146).length < 2 ^ (prefixWord ++ tailWord_3684146).sum := by decide
  have hdescent : baseEnd_3684146 < baseStart_3684146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684147 : List Nat := [1, 1, 1, 2, 7, 2, 2, 2, 1, 1, 3]
def baseStart_3684147 : Nat := 118140960795 + 3684147 * 2 ^ 59
def prefixEnd_3684147 : Nat := 4983230072969 + 3 ^ 40 * 3684147 * 2
def baseEnd_3684147 : Nat := 1891738212819902491619423

theorem tailTrace_3684147 : CollatzResearch.WordTrace tailWord_3684147 prefixEnd_3684147 1891738212819902491619423 := by
  unfold tailWord_3684147
  simp only [CollatzResearch.WordTrace]
  refine ⟨134371880183972096059362695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89581253455981397372908463 134371880183972096059362695)
  ·
    refine ⟨201557820275958144089044043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134371880183972096059362695 201557820275958144089044043)
    ·
      refine ⟨302336730413937216133566065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201557820275958144089044043 302336730413937216133566065)
      ·
        refine ⟨226752547810452912100174549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302336730413937216133566065 226752547810452912100174549)
        ·
          refine ⟨5314512839307490127347841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 226752547810452912100174549 5314512839307490127347841)
          ·
            refine ⟨3985884629480617595510881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5314512839307490127347841 3985884629480617595510881)
            ·
              refine ⟨2989413472110463196633161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3985884629480617595510881 2989413472110463196633161)
              ·
                refine ⟨2242060104082847397474871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2989413472110463196633161 2242060104082847397474871)
                ·
                  refine ⟨3363090156124271096212307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2242060104082847397474871 3363090156124271096212307)
                  ·
                    refine ⟨5044635234186406644318461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3363090156124271096212307 5044635234186406644318461)
                    ·
                      refine ⟨1891738212819902491619423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5044635234186406644318461 1891738212819902491619423)
                      ·
                        rfl

theorem cell23_3684147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 2, 2, 1, 1, 3].length) (baseStart_3684147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3684147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3684147 prefixEnd_3684147 := by exact prefixLift 3684147
  have htrace : WordTrace (prefixWord ++ tailWord_3684147) baseStart_3684147 baseEnd_3684147 := by
    simpa [prefixWord, tailWord_3684147, baseEnd_3684147] using wordTrace_append hprefix tailTrace_3684147
  have hstable : (prefixWord ++ tailWord_3684147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684147).length < 2 ^ (prefixWord ++ tailWord_3684147).sum := by decide
  have hdescent : baseEnd_3684147 < baseStart_3684147 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684173 : List Nat := [1, 6, 1, 2, 1, 1, 2, 1, 3, 2, 3]
def baseStart_3684173 : Nat := 118140960795 + 3684173 * 2 ^ 59
def prefixEnd_3684173 : Nat := 4983230072969 + 3 ^ 40 * 3684173 * 2
def baseEnd_3684173 : Nat := 1891751563316919389894303

theorem tailTrace_3684173 : CollatzResearch.WordTrace tailWord_3684173 prefixEnd_3684173 1891751563316919389894303 := by
  unfold tailWord_3684173
  simp only [CollatzResearch.WordTrace]
  refine ⟨134372828481877902499809173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89581885654585268333206115 134372828481877902499809173)
  ·
    refine ⟨6298726335088026679678555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 134372828481877902499809173 6298726335088026679678555)
    ·
      refine ⟨9448089502632040019517833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6298726335088026679678555 9448089502632040019517833)
      ·
        refine ⟨7086067126974030014638375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9448089502632040019517833 7086067126974030014638375)
        ·
          refine ⟨10629100690461045021957563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7086067126974030014638375 10629100690461045021957563)
          ·
            refine ⟨15943651035691567532936345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10629100690461045021957563 15943651035691567532936345)
            ·
              refine ⟨11957738276768675649702259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15943651035691567532936345 11957738276768675649702259)
              ·
                refine ⟨17936607415153013474553389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11957738276768675649702259 17936607415153013474553389)
                ·
                  refine ⟨6726227780682380052957521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17936607415153013474553389 6726227780682380052957521)
                  ·
                    refine ⟨5044670835511785039718141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6726227780682380052957521 5044670835511785039718141)
                    ·
                      refine ⟨1891751563316919389894303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5044670835511785039718141 1891751563316919389894303)
                      ·
                        rfl

theorem cell23_3684173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_3684173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3684173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3684173 prefixEnd_3684173 := by exact prefixLift 3684173
  have htrace : WordTrace (prefixWord ++ tailWord_3684173) baseStart_3684173 baseEnd_3684173 := by
    simpa [prefixWord, tailWord_3684173, baseEnd_3684173] using wordTrace_append hprefix tailTrace_3684173
  have hstable : (prefixWord ++ tailWord_3684173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684173).length < 2 ^ (prefixWord ++ tailWord_3684173).sum := by decide
  have hdescent : baseEnd_3684173 < baseStart_3684173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684186 : List Nat := [3, 1, 1, 2, 1, 3, 2, 2, 4, 1, 3]
def baseStart_3684186 : Nat := 118140960795 + 3684186 * 2 ^ 59
def prefixEnd_3684186 : Nat := 4983230072969 + 3 ^ 40 * 3684186 * 2
def baseEnd_3684186 : Nat := 1891758238565427839031743

theorem tailTrace_3684186 : CollatzResearch.WordTrace tailWord_3684186 prefixEnd_3684186 1891758238565427839031743 := by
  unfold tailWord_3684186
  simp only [CollatzResearch.WordTrace]
  refine ⟨33593325657707701430008103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89582201753887203813354941 33593325657707701430008103)
  ·
    refine ⟨50389988486561552145012155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33593325657707701430008103 50389988486561552145012155)
    ·
      refine ⟨75584982729842328217518233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50389988486561552145012155 75584982729842328217518233)
      ·
        refine ⟨56688737047381746163138675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75584982729842328217518233 56688737047381746163138675)
        ·
          refine ⟨85033105571072619244708013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56688737047381746163138675 85033105571072619244708013)
          ·
            refine ⟨31887414589152232216765505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85033105571072619244708013 31887414589152232216765505)
            ·
              refine ⟨23915560941864174162574129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31887414589152232216765505 23915560941864174162574129)
              ·
                refine ⟨17936670706398130621930597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23915560941864174162574129 17936670706398130621930597)
                ·
                  refine ⟨3363125757449649491611987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17936670706398130621930597 3363125757449649491611987)
                  ·
                    refine ⟨5044688636174474237417981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3363125757449649491611987 5044688636174474237417981)
                    ·
                      refine ⟨1891758238565427839031743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5044688636174474237417981 1891758238565427839031743)
                      ·
                        rfl

theorem cell23_3684186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2, 4, 1, 3].length) (baseStart_3684186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3684186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3684186 prefixEnd_3684186 := by exact prefixLift 3684186
  have htrace : WordTrace (prefixWord ++ tailWord_3684186) baseStart_3684186 baseEnd_3684186 := by
    simpa [prefixWord, tailWord_3684186, baseEnd_3684186] using wordTrace_append hprefix tailTrace_3684186
  have hstable : (prefixWord ++ tailWord_3684186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684186).length < 2 ^ (prefixWord ++ tailWord_3684186).sum := by decide
  have hdescent : baseEnd_3684186 < baseStart_3684186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684229 : List Nat := [1, 3, 1, 1, 3, 2, 2, 2, 2, 1, 5]
def baseStart_3684229 : Nat := 118140960795 + 3684229 * 2 ^ 59
def prefixEnd_3684229 : Nat := 4983230072969 + 3 ^ 40 * 3684229 * 2
def baseEnd_3684229 : Nat := 1891780318233571170794045

theorem tailTrace_3684229 : CollatzResearch.WordTrace tailWord_3684229 prefixEnd_3684229 1891780318233571170794045 := by
  unfold tailWord_3684229
  simp only [CollatzResearch.WordTrace]
  refine ⟨134374870969675024063847741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89583247313116682709231827 134374870969675024063847741)
  ·
    refine ⟨50390576613628134023942903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134374870969675024063847741 50390576613628134023942903)
    ·
      refine ⟨75585864920442201035914355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50390576613628134023942903 75585864920442201035914355)
      ·
        refine ⟨113378797380663301553871533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75585864920442201035914355 113378797380663301553871533)
        ·
          refine ⟨42517049017748738082701825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113378797380663301553871533 42517049017748738082701825)
          ·
            refine ⟨31887786763311553562026369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42517049017748738082701825 31887786763311553562026369)
            ·
              refine ⟨23915840072483665171519777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31887786763311553562026369 23915840072483665171519777)
              ·
                refine ⟨17936880054362748878639833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23915840072483665171519777 17936880054362748878639833)
                ·
                  refine ⟨13452660040772061658979875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17936880054362748878639833 13452660040772061658979875)
                  ·
                    refine ⟨20178990061158092488469813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13452660040772061658979875 20178990061158092488469813)
                    ·
                      refine ⟨1891780318233571170794045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20178990061158092488469813 1891780318233571170794045)
                      ·
                        rfl

theorem cell23_3684229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2, 2, 1, 5].length) (baseStart_3684229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3684229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3684229 prefixEnd_3684229 := by exact prefixLift 3684229
  have htrace : WordTrace (prefixWord ++ tailWord_3684229) baseStart_3684229 baseEnd_3684229 := by
    simpa [prefixWord, tailWord_3684229, baseEnd_3684229] using wordTrace_append hprefix tailTrace_3684229
  have hstable : (prefixWord ++ tailWord_3684229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684229).length < 2 ^ (prefixWord ++ tailWord_3684229).sum := by decide
  have hdescent : baseEnd_3684229 < baseStart_3684229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684277 : List Nat := [1, 3, 3, 2, 1, 2, 4, 1, 2, 2, 2]
def baseStart_3684277 : Nat := 118140960795 + 3684277 * 2 ^ 59
def prefixEnd_3684277 : Nat := 4983230072969 + 3 ^ 40 * 3684277 * 2
def baseEnd_3684277 : Nat := 1891804965304986982993825

theorem tailTrace_3684277 : CollatzResearch.WordTrace tailWord_3684277 prefixEnd_3684277 1891804965304986982993825 := by
  unfold tailWord_3684277
  simp only [CollatzResearch.WordTrace]
  refine ⟨134376621673501128261595085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89584414449000752174396723 134376621673501128261595085)
  ·
    refine ⟨50391233127562923098098157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134376621673501128261595085 50391233127562923098098157)
    ·
      refine ⟨18896712422836096161786809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50391233127562923098098157 18896712422836096161786809)
      ·
        refine ⟨14172534317127072121340107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18896712422836096161786809 14172534317127072121340107)
        ·
          refine ⟨21258801475690608182010161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14172534317127072121340107 21258801475690608182010161)
          ·
            refine ⟨15944101106767956136507621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21258801475690608182010161 15944101106767956136507621)
            ·
              refine ⟨2989518957518991775595179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15944101106767956136507621 2989518957518991775595179)
              ·
                refine ⟨4484278436278487663392769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2989518957518991775595179 4484278436278487663392769)
                ·
                  refine ⟨3363208827208865747544577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4484278436278487663392769 3363208827208865747544577)
                  ·
                    refine ⟨2522406620406649310658433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3363208827208865747544577 2522406620406649310658433)
                    ·
                      refine ⟨1891804965304986982993825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2522406620406649310658433 1891804965304986982993825)
                      ·
                        rfl

theorem cell23_3684277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 4, 1, 2, 2, 2].length) (baseStart_3684277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3684277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3684277 prefixEnd_3684277 := by exact prefixLift 3684277
  have htrace : WordTrace (prefixWord ++ tailWord_3684277) baseStart_3684277 baseEnd_3684277 := by
    simpa [prefixWord, tailWord_3684277, baseEnd_3684277] using wordTrace_append hprefix tailTrace_3684277
  have hstable : (prefixWord ++ tailWord_3684277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684277).length < 2 ^ (prefixWord ++ tailWord_3684277).sum := by decide
  have hdescent : baseEnd_3684277 < baseStart_3684277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684279 : List Nat := [1, 1, 3, 1, 3, 1, 1, 1, 6, 5]
def baseStart_3684279 : Nat := 118140960795 + 3684279 * 2 ^ 59
def prefixEnd_3684279 : Nat := 4983230072969 + 3 ^ 40 * 3684279 * 2
def baseEnd_3684279 : Nat := 630601997422098658389605

theorem tailTrace_3684279 : CollatzResearch.WordTrace tailWord_3684279 prefixEnd_3684279 630601997422098658389605 := by
  unfold tailWord_3684279
  simp only [CollatzResearch.WordTrace]
  refine ⟨134376694619493882603167891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89584463079662588402111927 134376694619493882603167891)
  ·
    refine ⟨201565041929240823904751837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134376694619493882603167891 201565041929240823904751837)
    ·
      refine ⟨75586890723465308964281939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201565041929240823904751837 75586890723465308964281939)
      ·
        refine ⟨113380336085197963446422909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75586890723465308964281939 113380336085197963446422909)
        ·
          refine ⟨42517626031949236292408591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113380336085197963446422909 42517626031949236292408591)
          ·
            refine ⟨63776439047923854438612887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42517626031949236292408591 63776439047923854438612887)
            ·
              refine ⟨95664658571885781657919331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63776439047923854438612887 95664658571885781657919331)
              ·
                refine ⟨143496987857828672486878997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95664658571885781657919331 143496987857828672486878997)
                ·
                  refine ⟨6726421305835719022822453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 143496987857828672486878997 6726421305835719022822453)
                  ·
                    refine ⟨630601997422098658389605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6726421305835719022822453 630601997422098658389605)
                    ·
                      rfl

theorem cell23_3684279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 6, 5].length) (baseStart_3684279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3684279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3684279 prefixEnd_3684279 := by exact prefixLift 3684279
  have htrace : WordTrace (prefixWord ++ tailWord_3684279) baseStart_3684279 baseEnd_3684279 := by
    simpa [prefixWord, tailWord_3684279, baseEnd_3684279] using wordTrace_append hprefix tailTrace_3684279
  have hstable : (prefixWord ++ tailWord_3684279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684279).length < 2 ^ (prefixWord ++ tailWord_3684279).sum := by decide
  have hdescent : baseEnd_3684279 < baseStart_3684279 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684296 : List Nat := [2, 1, 3, 1, 4, 1, 1, 3, 2, 5]
def baseStart_3684296 : Nat := 118140960795 + 3684296 * 2 ^ 59
def prefixEnd_3684296 : Nat := 4983230072969 + 3 ^ 40 * 3684296 * 2
def baseEnd_3684296 : Nat := 630604907145807469552079

theorem tailTrace_3684296 : CollatzResearch.WordTrace tailWord_3684296 prefixEnd_3684296 630604907145807469552079 := by
  unfold tailWord_3684296
  simp only [CollatzResearch.WordTrace]
  refine ⟨67188657330216147253268371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89584876440288196337691161 67188657330216147253268371)
  ·
    refine ⟨100782985995324220879902557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67188657330216147253268371 100782985995324220879902557)
    ·
      refine ⟨37793619748246582829963459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100782985995324220879902557 37793619748246582829963459)
      ·
        refine ⟨56690429622369874244945189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37793619748246582829963459 56690429622369874244945189)
        ·
          refine ⟨10629455554194351420927223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56690429622369874244945189 10629455554194351420927223)
          ·
            refine ⟨15944183331291527131390835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10629455554194351420927223 15944183331291527131390835)
            ·
              refine ⟨23916274996937290697086253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15944183331291527131390835 23916274996937290697086253)
              ·
                refine ⟨8968603123851484011407345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23916274996937290697086253 8968603123851484011407345)
                ·
                  refine ⟨6726452342888613008555509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8968603123851484011407345 6726452342888613008555509)
                  ·
                    refine ⟨630604907145807469552079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6726452342888613008555509 630604907145807469552079)
                    ·
                      rfl

theorem cell23_3684296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 3, 2, 5].length) (baseStart_3684296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3684296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3684296 prefixEnd_3684296 := by exact prefixLift 3684296
  have htrace : WordTrace (prefixWord ++ tailWord_3684296) baseStart_3684296 baseEnd_3684296 := by
    simpa [prefixWord, tailWord_3684296, baseEnd_3684296] using wordTrace_append hprefix tailTrace_3684296
  have hstable : (prefixWord ++ tailWord_3684296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684296).length < 2 ^ (prefixWord ++ tailWord_3684296).sum := by decide
  have hdescent : baseEnd_3684296 < baseStart_3684296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684317 : List Nat := [1, 4, 3, 1, 3, 2, 2, 2, 5]
def baseStart_3684317 : Nat := 118140960795 + 3684317 * 2 ^ 59
def prefixEnd_3684317 : Nat := 4983230072969 + 3 ^ 40 * 3684317 * 2
def baseEnd_3684317 : Nat := 210202833836796314054849

theorem tailTrace_3684317 : CollatzResearch.WordTrace tailWord_3684317 prefixEnd_3684317 210202833836796314054849 := by
  unfold tailWord_3684317
  simp only [CollatzResearch.WordTrace]
  refine ⟨134378080593356215093051205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89585387062237476728700803 134378080593356215093051205)
  ·
    refine ⟨25195890111254290329947101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134378080593356215093051205 25195890111254290329947101)
    ·
      refine ⟨9448458791720358873730163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25195890111254290329947101 9448458791720358873730163)
      ·
        refine ⟨14172688187580538310595245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9448458791720358873730163 14172688187580538310595245)
        ·
          refine ⟨5314758070342701866473217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14172688187580538310595245 5314758070342701866473217)
          ·
            refine ⟨3986068552757026399854913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5314758070342701866473217 3986068552757026399854913)
            ·
              refine ⟨2989551414567769799891185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3986068552757026399854913 2989551414567769799891185)
              ·
                refine ⟨2242163560925827349918389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2989551414567769799891185 2242163560925827349918389)
                ·
                  refine ⟨210202833836796314054849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2242163560925827349918389 210202833836796314054849)
                  ·
                    rfl

theorem cell23_3684317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 2, 2, 5].length) (baseStart_3684317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3684317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3684317 prefixEnd_3684317 := by exact prefixLift 3684317
  have htrace : WordTrace (prefixWord ++ tailWord_3684317) baseStart_3684317 baseEnd_3684317 := by
    simpa [prefixWord, tailWord_3684317, baseEnd_3684317] using wordTrace_append hprefix tailTrace_3684317
  have hstable : (prefixWord ++ tailWord_3684317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684317).length < 2 ^ (prefixWord ++ tailWord_3684317).sum := by decide
  have hdescent : baseEnd_3684317 < baseStart_3684317 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684336 : List Nat := [2, 1, 1, 1, 3, 2, 2, 2, 4, 2, 3]
def baseStart_3684336 : Nat := 118140960795 + 3684336 * 2 ^ 59
def prefixEnd_3684336 : Nat := 4983230072969 + 3 ^ 40 * 3684336 * 2
def baseEnd_3684336 : Nat := 1891835260663602252156053

theorem tailTrace_3684336 : CollatzResearch.WordTrace tailWord_3684336 prefixEnd_3684336 1891835260663602252156053 := by
  unfold tailWord_3684336
  simp only [CollatzResearch.WordTrace]
  refine ⟨67189386790143690668996431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89585849053524920891995241 67189386790143690668996431)
  ·
    refine ⟨100784080185215536003494647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67189386790143690668996431 100784080185215536003494647)
    ·
      refine ⟨151176120277823304005241971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100784080185215536003494647 151176120277823304005241971)
      ·
        refine ⟨226764180416734956007862957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151176120277823304005241971 226764180416734956007862957)
        ·
          refine ⟨85036567656275608502948609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226764180416734956007862957 85036567656275608502948609)
          ·
            refine ⟨63777425742206706377211457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85036567656275608502948609 63777425742206706377211457)
            ·
              refine ⟨47833069306655029782908593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63777425742206706377211457 47833069306655029782908593)
              ·
                refine ⟨35874801979991272337181445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47833069306655029782908593 35874801979991272337181445)
                ·
                  refine ⟨6726525371248363563221521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35874801979991272337181445 6726525371248363563221521)
                  ·
                    refine ⟨5044894028436272672416141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6726525371248363563221521 5044894028436272672416141)
                    ·
                      refine ⟨1891835260663602252156053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5044894028436272672416141 1891835260663602252156053)
                      ·
                        rfl

theorem cell23_3684336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 4, 2, 3].length) (baseStart_3684336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3684336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3684336 prefixEnd_3684336 := by exact prefixLift 3684336
  have htrace : WordTrace (prefixWord ++ tailWord_3684336) baseStart_3684336 baseEnd_3684336 := by
    simpa [prefixWord, tailWord_3684336, baseEnd_3684336] using wordTrace_append hprefix tailTrace_3684336
  have hstable : (prefixWord ++ tailWord_3684336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684336).length < 2 ^ (prefixWord ++ tailWord_3684336).sum := by decide
  have hdescent : baseEnd_3684336 < baseStart_3684336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684350 : List Nat := [4, 2, 2, 2, 1, 1, 3, 1, 2, 1, 4]
def baseStart_3684350 : Nat := 118140960795 + 3684350 * 2 ^ 59
def prefixEnd_3684350 : Nat := 4983230072969 + 3 ^ 40 * 3684350 * 2
def baseEnd_3684350 : Nat := 1891842449392765197380989

theorem tailTrace_3684350 : CollatzResearch.WordTrace tailWord_3684350 prefixEnd_3684350 1891842449392765197380989 := by
  unfold tailWord_3684350
  simp only [CollatzResearch.WordTrace]
  refine ⟨16797410525279582716125313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89586189468157774486001669 16797410525279582716125313)
  ·
    refine ⟨12598057893959687037093985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16797410525279582716125313 12598057893959687037093985)
    ·
      refine ⟨9448543420469765277820489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12598057893959687037093985 9448543420469765277820489)
      ·
        refine ⟨7086407565352323958365367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9448543420469765277820489 7086407565352323958365367)
        ·
          refine ⟨10629611348028485937548051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7086407565352323958365367 10629611348028485937548051)
          ·
            refine ⟨15944417022042728906322077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10629611348028485937548051 15944417022042728906322077)
            ·
              refine ⟨5979156383266023339870779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15944417022042728906322077 5979156383266023339870779)
              ·
                refine ⟨8968734574899035009806169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5979156383266023339870779 8968734574899035009806169)
                ·
                  refine ⟨6726550931174276257354627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8968734574899035009806169 6726550931174276257354627)
                  ·
                    refine ⟨10089826396761414386031941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6726550931174276257354627 10089826396761414386031941)
                    ·
                      refine ⟨1891842449392765197380989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10089826396761414386031941 1891842449392765197380989)
                      ·
                        rfl

theorem cell23_3684350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_3684350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3684350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3684350 prefixEnd_3684350 := by exact prefixLift 3684350
  have htrace : WordTrace (prefixWord ++ tailWord_3684350) baseStart_3684350 baseEnd_3684350 := by
    simpa [prefixWord, tailWord_3684350, baseEnd_3684350] using wordTrace_append hprefix tailTrace_3684350
  have hstable : (prefixWord ++ tailWord_3684350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684350).length < 2 ^ (prefixWord ++ tailWord_3684350).sum := by decide
  have hdescent : baseEnd_3684350 < baseStart_3684350 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684360 : List Nat := [2, 1, 3, 2, 1, 2, 4, 3, 1, 4]
def baseStart_3684360 : Nat := 118140960795 + 3684360 * 2 ^ 59
def prefixEnd_3684360 : Nat := 4983230072969 + 3 ^ 40 * 3684360 * 2
def baseEnd_3684360 : Nat := 630615861399770052751981

theorem tailTrace_3684360 : CollatzResearch.WordTrace tailWord_3684360 prefixEnd_3684360 630615861399770052751981 := by
  unfold tailWord_3684360
  simp only [CollatzResearch.WordTrace]
  refine ⟨67189824466100216718433267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89586432621466955624577689 67189824466100216718433267)
  ·
    refine ⟨100784736699150325077649901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67189824466100216718433267 100784736699150325077649901)
    ·
      refine ⟨37794276262181371904118713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100784736699150325077649901 37794276262181371904118713)
      ·
        refine ⟨28345707196636028928089035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37794276262181371904118713 28345707196636028928089035)
        ·
          refine ⟨42518560794954043392133553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28345707196636028928089035 42518560794954043392133553)
          ·
            refine ⟨31888920596215532544100165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42518560794954043392133553 31888920596215532544100165)
            ·
              refine ⟨5979172611790412352018781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31888920596215532544100165 5979172611790412352018781)
              ·
                refine ⟨2242189729421404632007043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5979172611790412352018781 2242189729421404632007043)
                ·
                  refine ⟨3363284594132106948010565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2242189729421404632007043 3363284594132106948010565)
                  ·
                    refine ⟨630615861399770052751981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3363284594132106948010565 630615861399770052751981)
                    ·
                      rfl

theorem cell23_3684360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 3, 1, 4].length) (baseStart_3684360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3684360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3684360 prefixEnd_3684360 := by exact prefixLift 3684360
  have htrace : WordTrace (prefixWord ++ tailWord_3684360) baseStart_3684360 baseEnd_3684360 := by
    simpa [prefixWord, tailWord_3684360, baseEnd_3684360] using wordTrace_append hprefix tailTrace_3684360
  have hstable : (prefixWord ++ tailWord_3684360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684360).length < 2 ^ (prefixWord ++ tailWord_3684360).sum := by decide
  have hdescent : baseEnd_3684360 < baseStart_3684360 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684379 : List Nat := [1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 7]
def baseStart_3684379 : Nat := 118140960795 + 3684379 * 2 ^ 59
def prefixEnd_3684379 : Nat := 4983230072969 + 3 ^ 40 * 3684379 * 2
def baseEnd_3684379 : Nat := 1891857340331745583918355

theorem tailTrace_3684379 : CollatzResearch.WordTrace tailWord_3684379 prefixEnd_3684379 1891857340331745583918355 := by
  unfold tailWord_3684379
  simp only [CollatzResearch.WordTrace]
  refine ⟨134380341919131599681808191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89586894612754399787872127 134380341919131599681808191)
  ·
    refine ⟨201570512878697399522712287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134380341919131599681808191 201570512878697399522712287)
    ·
      refine ⟨302355769318046099284068431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201570512878697399522712287 302355769318046099284068431)
      ·
        refine ⟨453533653977069148926102647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302355769318046099284068431 453533653977069148926102647)
        ·
          refine ⟨680300480965603723389153971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 453533653977069148926102647 680300480965603723389153971)
          ·
            refine ⟨1020450721448405585083730957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 680300480965603723389153971 1020450721448405585083730957)
            ·
              refine ⟨382669020543152094406399109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1020450721448405585083730957 382669020543152094406399109)
              ·
                refine ⟨71750441351841017701199833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 382669020543152094406399109 71750441351841017701199833)
                ·
                  refine ⟨53812831013880763275899875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71750441351841017701199833 53812831013880763275899875)
                  ·
                    refine ⟨80719246520821144913849813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53812831013880763275899875 80719246520821144913849813)
                    ·
                      refine ⟨1891857340331745583918355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 80719246520821144913849813 1891857340331745583918355)
                      ·
                        rfl

theorem cell23_3684379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 7].length) (baseStart_3684379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3684379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3684379 prefixEnd_3684379 := by exact prefixLift 3684379
  have htrace : WordTrace (prefixWord ++ tailWord_3684379) baseStart_3684379 baseEnd_3684379 := by
    simpa [prefixWord, tailWord_3684379, baseEnd_3684379] using wordTrace_append hprefix tailTrace_3684379
  have hstable : (prefixWord ++ tailWord_3684379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684379).length < 2 ^ (prefixWord ++ tailWord_3684379).sum := by decide
  have hdescent : baseEnd_3684379 < baseStart_3684379 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684423 : List Nat := [1, 1, 4, 1, 3, 1, 1, 5, 1, 1, 4]
def baseStart_3684423 : Nat := 118140960795 + 3684423 * 2 ^ 59
def prefixEnd_3684423 : Nat := 4983230072969 + 3 ^ 40 * 3684423 * 2
def baseEnd_3684423 : Nat := 1891879933480543411768153

theorem tailTrace_3684423 : CollatzResearch.WordTrace tailWord_3684423 prefixEnd_3684423 1891879933480543411768153 := by
  unfold tailWord_3684423
  simp only [CollatzResearch.WordTrace]
  refine ⟨134381946730972195196409923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89587964487314796797606615 134381946730972195196409923)
  ·
    refine ⟨201572920096458292794614885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134381946730972195196409923 201572920096458292794614885)
    ·
      refine ⟨37794922518085929898990291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 201572920096458292794614885 37794922518085929898990291)
      ·
        refine ⟨56692383777128894848485437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37794922518085929898990291 56692383777128894848485437)
        ·
          refine ⟨21259643916423335568182039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56692383777128894848485437 21259643916423335568182039)
          ·
            refine ⟨31889465874635003352273059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21259643916423335568182039 31889465874635003352273059)
            ·
              refine ⟨47834198811952505028409589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31889465874635003352273059 47834198811952505028409589)
              ·
                refine ⟨4484456138620547346413399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47834198811952505028409589 4484456138620547346413399)
                ·
                  refine ⟨6726684207930821019620099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4484456138620547346413399 6726684207930821019620099)
                  ·
                    refine ⟨10090026311896231529430149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6726684207930821019620099 10090026311896231529430149)
                    ·
                      refine ⟨1891879933480543411768153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10090026311896231529430149 1891879933480543411768153)
                      ·
                        rfl

theorem cell23_3684423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 5, 1, 1, 4].length) (baseStart_3684423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3684423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3684423 prefixEnd_3684423 := by exact prefixLift 3684423
  have htrace : WordTrace (prefixWord ++ tailWord_3684423) baseStart_3684423 baseEnd_3684423 := by
    simpa [prefixWord, tailWord_3684423, baseEnd_3684423] using wordTrace_append hprefix tailTrace_3684423
  have hstable : (prefixWord ++ tailWord_3684423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684423).length < 2 ^ (prefixWord ++ tailWord_3684423).sum := by decide
  have hdescent : baseEnd_3684423 < baseStart_3684423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684433 : List Nat := [1, 2, 2, 1, 3, 1, 1, 6, 2, 4]
def baseStart_3684433 : Nat := 118140960795 + 3684433 * 2 ^ 59
def prefixEnd_3684433 : Nat := 4983230072969 + 3 ^ 40 * 3684433 * 2
def baseEnd_3684433 : Nat := 630628356095696124214369

theorem tailTrace_3684433 : CollatzResearch.WordTrace tailWord_3684433 prefixEnd_3684433 630628356095696124214369 := by
  unfold tailWord_3684433
  simp only [CollatzResearch.WordTrace]
  refine ⟨134382311460935966904273953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89588207640623977936182635 134382311460935966904273953)
  ·
    refine ⟨100786733595701975178205465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134382311460935966904273953 100786733595701975178205465)
    ·
      refine ⟨75590050196776481383654099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100786733595701975178205465 75590050196776481383654099)
      ·
        refine ⟨113385075295164722075481149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75590050196776481383654099 113385075295164722075481149)
        ·
          refine ⟨42519403235686770778305431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113385075295164722075481149 42519403235686770778305431)
          ·
            refine ⟨63779104853530156167458147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42519403235686770778305431 63779104853530156167458147)
            ·
              refine ⟨95668657280295234251187221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63779104853530156167458147 95668657280295234251187221)
              ·
                refine ⟨4484468310013839105524401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 95668657280295234251187221 4484468310013839105524401)
                ·
                  refine ⟨3363351232510379329143301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4484468310013839105524401 3363351232510379329143301)
                  ·
                    refine ⟨630628356095696124214369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3363351232510379329143301 630628356095696124214369)
                    ·
                      rfl

theorem cell23_3684433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 6, 2, 4].length) (baseStart_3684433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3684433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3684433 prefixEnd_3684433 := by exact prefixLift 3684433
  have htrace : WordTrace (prefixWord ++ tailWord_3684433) baseStart_3684433 baseEnd_3684433 := by
    simpa [prefixWord, tailWord_3684433, baseEnd_3684433] using wordTrace_append hprefix tailTrace_3684433
  have hstable : (prefixWord ++ tailWord_3684433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684433).length < 2 ^ (prefixWord ++ tailWord_3684433).sum := by decide
  have hdescent : baseEnd_3684433 < baseStart_3684433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684434 : List Nat := [3, 2, 2, 1, 5, 1, 1, 1, 3, 1, 3]
def baseStart_3684434 : Nat := 118140960795 + 3684434 * 2 ^ 59
def prefixEnd_3684434 : Nat := 4983230072969 + 3 ^ 40 * 3684434 * 2
def baseEnd_3684434 : Nat := 1891885581767742868730603

theorem tailTrace_3684434 : CollatzResearch.WordTrace tailWord_3684434 prefixEnd_3684434 1891885581767742868730603 := by
  unfold tailWord_3684434
  simp only [CollatzResearch.WordTrace]
  refine ⟨33595586983483086018765089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89588231955954896050040237 33595586983483086018765089)
  ·
    refine ⟨25196690237612314514073817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33595586983483086018765089 25196690237612314514073817)
    ·
      refine ⟨18897517678209235885555363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25196690237612314514073817 18897517678209235885555363)
      ·
        refine ⟨28346276517313853828333045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18897517678209235885555363 28346276517313853828333045)
        ·
          refine ⟨2657463423498173796406223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28346276517313853828333045 2657463423498173796406223)
          ·
            refine ⟨3986195135247260694609335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2657463423498173796406223 3986195135247260694609335)
            ·
              refine ⟨5979292702870891041914003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3986195135247260694609335 5979292702870891041914003)
              ·
                refine ⟨8968939054306336562871005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5979292702870891041914003 8968939054306336562871005)
                ·
                  refine ⟨3363352145364876211076627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8968939054306336562871005 3363352145364876211076627)
                  ·
                    refine ⟨5045028218047314316614941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3363352145364876211076627 5045028218047314316614941)
                    ·
                      refine ⟨1891885581767742868730603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5045028218047314316614941 1891885581767742868730603)
                      ·
                        rfl

theorem cell23_3684434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 1, 3, 1, 3].length) (baseStart_3684434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3684434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3684434 prefixEnd_3684434 := by exact prefixLift 3684434
  have htrace : WordTrace (prefixWord ++ tailWord_3684434) baseStart_3684434 baseEnd_3684434 := by
    simpa [prefixWord, tailWord_3684434, baseEnd_3684434] using wordTrace_append hprefix tailTrace_3684434
  have hstable : (prefixWord ++ tailWord_3684434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684434).length < 2 ^ (prefixWord ++ tailWord_3684434).sum := by decide
  have hdescent : baseEnd_3684434 < baseStart_3684434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684460 : List Nat := [2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 3]
def baseStart_3684460 : Nat := 118140960795 + 3684460 * 2 ^ 59
def prefixEnd_3684460 : Nat := 4983230072969 + 3 ^ 40 * 3684460 * 2
def baseEnd_3684460 : Nat := 1891898932264759767005483

theorem tailTrace_3684460 : CollatzResearch.WordTrace tailWord_3684460 prefixEnd_3684460 1891898932264759767005483 := by
  unfold tailWord_3684460
  simp only [CollatzResearch.WordTrace]
  refine ⟨67191648115919075257753417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89588864154558767010337889 67191648115919075257753417)
  ·
    refine ⟨50393736086939306443315063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67191648115919075257753417 50393736086939306443315063)
    ·
      refine ⟨75590604130408959664972595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50393736086939306443315063 75590604130408959664972595)
      ·
        refine ⟨113385906195613439497458893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75590604130408959664972595 113385906195613439497458893)
        ·
          refine ⟨42519714823355039811547085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113385906195613439497458893 42519714823355039811547085)
          ·
            refine ⟨15944893058758139929330157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42519714823355039811547085 15944893058758139929330157)
            ·
              refine ⟨5979334897034302473498809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15944893058758139929330157 5979334897034302473498809)
              ·
                refine ⟨4484501172775726855124107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5979334897034302473498809 4484501172775726855124107)
                ·
                  refine ⟨6726751759163590282686161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4484501172775726855124107 6726751759163590282686161)
                  ·
                    refine ⟨5045063819372692712014621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6726751759163590282686161 5045063819372692712014621)
                    ·
                      refine ⟨1891898932264759767005483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5045063819372692712014621 1891898932264759767005483)
                      ·
                        rfl

theorem cell23_3684460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 3].length) (baseStart_3684460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3684460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3684460 prefixEnd_3684460 := by exact prefixLift 3684460
  have htrace : WordTrace (prefixWord ++ tailWord_3684460) baseStart_3684460 baseEnd_3684460 := by
    simpa [prefixWord, tailWord_3684460, baseEnd_3684460] using wordTrace_append hprefix tailTrace_3684460
  have hstable : (prefixWord ++ tailWord_3684460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684460).length < 2 ^ (prefixWord ++ tailWord_3684460).sum := by decide
  have hdescent : baseEnd_3684460 < baseStart_3684460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684470 : List Nat := [5, 1, 1, 2, 1, 3, 1, 2, 1, 2, 4]
def baseStart_3684470 : Nat := 118140960795 + 3684470 * 2 ^ 59
def prefixEnd_3684470 : Nat := 4983230072969 + 3 ^ 40 * 3684470 * 2
def baseEnd_3684470 : Nat := 1891904067071304727880437

theorem tailTrace_3684470 : CollatzResearch.WordTrace tailWord_3684470 prefixEnd_3684470 1891904067071304727880437 := by
  unfold tailWord_3684470
  simp only [CollatzResearch.WordTrace]
  refine ⟨8398978810112620138960679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89589107307867948148913909 8398978810112620138960679)
  ·
    refine ⟨12598468215168930208441019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8398978810112620138960679 12598468215168930208441019)
    ·
      refine ⟨18897702322753395312661529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12598468215168930208441019 18897702322753395312661529)
      ·
        refine ⟨14173276742065046484496147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18897702322753395312661529 14173276742065046484496147)
        ·
          refine ⟨21259915113097569726744221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14173276742065046484496147 21259915113097569726744221)
          ·
            refine ⟨7972468167411588647529083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21259915113097569726744221 7972468167411588647529083)
            ·
              refine ⟨11958702251117382971293625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7972468167411588647529083 11958702251117382971293625)
              ·
                refine ⟨8969026688338037228470219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11958702251117382971293625 8969026688338037228470219)
                ·
                  refine ⟨13453540032507055842705329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8969026688338037228470219 13453540032507055842705329)
                  ·
                    refine ⟨10090155024380291882028997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13453540032507055842705329 10090155024380291882028997)
                    ·
                      refine ⟨1891904067071304727880437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10090155024380291882028997 1891904067071304727880437)
                      ·
                        rfl

theorem cell23_3684470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_3684470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3684470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3684470 prefixEnd_3684470 := by exact prefixLift 3684470
  have htrace : WordTrace (prefixWord ++ tailWord_3684470) baseStart_3684470 baseEnd_3684470 := by
    simpa [prefixWord, tailWord_3684470, baseEnd_3684470] using wordTrace_append hprefix tailTrace_3684470
  have hstable : (prefixWord ++ tailWord_3684470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684470).length < 2 ^ (prefixWord ++ tailWord_3684470).sum := by decide
  have hdescent : baseEnd_3684470 < baseStart_3684470 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684473 : List Nat := [1, 2, 1, 3, 4, 1, 1, 1, 3, 3, 3]
def baseStart_3684473 : Nat := 118140960795 + 3684473 * 2 ^ 59
def prefixEnd_3684473 : Nat := 4983230072969 + 3 ^ 40 * 3684473 * 2
def baseEnd_3684473 : Nat := 1891905607513268216142923

theorem tailTrace_3684473 : CollatzResearch.WordTrace tailWord_3684473 prefixEnd_3684473 1891905607513268216142923 := by
  unfold tailWord_3684473
  simp only [CollatzResearch.WordTrace]
  refine ⟨134383770380791053735730073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89589180253860702490486715 134383770380791053735730073)
  ·
    refine ⟨100787827785593290301797555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134383770380791053735730073 100787827785593290301797555)
    ·
      refine ⟨151181741678389935452696333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100787827785593290301797555 151181741678389935452696333)
      ·
        refine ⟨56693153129396225794761125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151181741678389935452696333 56693153129396225794761125)
        ·
          refine ⟨10629966211761792336517711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56693153129396225794761125 10629966211761792336517711)
          ·
            refine ⟨15944949317642688504776567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10629966211761792336517711 15944949317642688504776567)
            ·
              refine ⟨23917423976464032757164851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15944949317642688504776567 23917423976464032757164851)
              ·
                refine ⟨35876135964696049135747277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23917423976464032757164851 35876135964696049135747277)
                ·
                  refine ⟨13453550986761018425905229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35876135964696049135747277 13453550986761018425905229)
                  ·
                    refine ⟨5045081620035381909714461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13453550986761018425905229 5045081620035381909714461)
                    ·
                      refine ⟨1891905607513268216142923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5045081620035381909714461 1891905607513268216142923)
                      ·
                        rfl

theorem cell23_3684473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 3, 3, 3].length) (baseStart_3684473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3684473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3684473 prefixEnd_3684473 := by exact prefixLift 3684473
  have htrace : WordTrace (prefixWord ++ tailWord_3684473) baseStart_3684473 baseEnd_3684473 := by
    simpa [prefixWord, tailWord_3684473, baseEnd_3684473] using wordTrace_append hprefix tailTrace_3684473
  have hstable : (prefixWord ++ tailWord_3684473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684473).length < 2 ^ (prefixWord ++ tailWord_3684473).sum := by decide
  have hdescent : baseEnd_3684473 < baseStart_3684473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684477 : List Nat := [1, 4, 1, 1, 3, 3, 3, 1, 1, 2, 3]
def baseStart_3684477 : Nat := 118140960795 + 3684477 * 2 ^ 59
def prefixEnd_3684477 : Nat := 4983230072969 + 3 ^ 40 * 3684477 * 2
def baseEnd_3684477 : Nat := 1891907661435886200492905

theorem tailTrace_3684477 : CollatzResearch.WordTrace tailWord_3684477 prefixEnd_3684477 1891907661435886200492905 := by
  unfold tailWord_3684477
  simp only [CollatzResearch.WordTrace]
  refine ⟨134383916272776562418875685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89589277515184374945917123 134383916272776562418875685)
  ·
    refine ⟨25196984301145605453539191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134383916272776562418875685 25196984301145605453539191)
    ·
      refine ⟨37795476451718408180308787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25196984301145605453539191 37795476451718408180308787)
      ·
        refine ⟨56693214677577612270463181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37795476451718408180308787 56693214677577612270463181)
        ·
          refine ⟨21259955504091604601423693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56693214677577612270463181 21259955504091604601423693)
          ·
            refine ⟨7972483314034351725533885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21259955504091604601423693 7972483314034351725533885)
            ·
              refine ⟨2989681242762881897075207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7972483314034351725533885 2989681242762881897075207)
              ·
                refine ⟨4484521864144322845612811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2989681242762881897075207 4484521864144322845612811)
                ·
                  refine ⟨6726782796216484268419217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4484521864144322845612811 6726782796216484268419217)
                  ·
                    refine ⟨5045087097162363201314413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6726782796216484268419217 5045087097162363201314413)
                    ·
                      refine ⟨1891907661435886200492905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5045087097162363201314413 1891907661435886200492905)
                      ·
                        rfl

theorem cell23_3684477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 3, 1, 1, 2, 3].length) (baseStart_3684477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3684477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3684477 prefixEnd_3684477 := by exact prefixLift 3684477
  have htrace : WordTrace (prefixWord ++ tailWord_3684477) baseStart_3684477 baseEnd_3684477 := by
    simpa [prefixWord, tailWord_3684477, baseEnd_3684477] using wordTrace_append hprefix tailTrace_3684477
  have hstable : (prefixWord ++ tailWord_3684477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684477).length < 2 ^ (prefixWord ++ tailWord_3684477).sum := by decide
  have hdescent : baseEnd_3684477 < baseStart_3684477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684496 : List Nat := [2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 4]
def baseStart_3684496 : Nat := 118140960795 + 3684496 * 2 ^ 59
def prefixEnd_3684496 : Nat := 4983230072969 + 3 ^ 40 * 3684496 * 2
def baseEnd_3684496 : Nat := 1891917417568321626155317

theorem tailTrace_3684496 : CollatzResearch.WordTrace tailWord_3684496 prefixEnd_3684496 1891917417568321626155317 := by
  unfold tailWord_3684496
  simp only [CollatzResearch.WordTrace]
  refine ⟨67192304629853864331908671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89589739506471819109211561 67192304629853864331908671)
  ·
    refine ⟨100788456944780796497863007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67192304629853864331908671 100788456944780796497863007)
    ·
      refine ⟨151182685417171194746794511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100788456944780796497863007 151182685417171194746794511)
      ·
        refine ⟨226774028125756792120191767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151182685417171194746794511 226774028125756792120191767)
        ·
          refine ⟨340161042188635188180287651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226774028125756792120191767 340161042188635188180287651)
          ·
            refine ⟨510241563282952782270431477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340161042188635188180287651 510241563282952782270431477)
            ·
              refine ⟨47835146557776823337852951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 510241563282952782270431477 47835146557776823337852951)
              ·
                refine ⟨71752719836665235006779427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47835146557776823337852951 71752719836665235006779427)
                ·
                  refine ⟨107629079754997852510169141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71752719836665235006779427 107629079754997852510169141)
                  ·
                    refine ⟨10090226227031048672828357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 107629079754997852510169141 10090226227031048672828357)
                    ·
                      refine ⟨1891917417568321626155317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10090226227031048672828357 1891917417568321626155317)
                      ·
                        rfl

theorem cell23_3684496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 4].length) (baseStart_3684496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3684496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3684496 prefixEnd_3684496 := by exact prefixLift 3684496
  have htrace : WordTrace (prefixWord ++ tailWord_3684496) baseStart_3684496 baseEnd_3684496 := by
    simpa [prefixWord, tailWord_3684496, baseEnd_3684496] using wordTrace_append hprefix tailTrace_3684496
  have hstable : (prefixWord ++ tailWord_3684496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684496).length < 2 ^ (prefixWord ++ tailWord_3684496).sum := by decide
  have hdescent : baseEnd_3684496 < baseStart_3684496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684530 : List Nat := [3, 2, 1, 1, 1, 3, 1, 4, 1, 4, 2]
def baseStart_3684530 : Nat := 118140960795 + 3684530 * 2 ^ 59
def prefixEnd_3684530 : Nat := 4983230072969 + 3 ^ 40 * 3684530 * 2
def baseEnd_3684530 : Nat := 1891934875910574493130161

theorem tailTrace_3684530 : CollatzResearch.WordTrace tailWord_3684530 prefixEnd_3684530 1891934875910574493130161 := by
  unfold tailWord_3684530
  simp only [CollatzResearch.WordTrace]
  refine ⟨33596462335396138117638761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89590566227723034980370029 33596462335396138117638761)
  ·
    refine ⟨25197346751547103588229071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33596462335396138117638761 25197346751547103588229071)
    ·
      refine ⟨37796020127320655382343607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25197346751547103588229071 37796020127320655382343607)
      ·
        refine ⟨56694030190980983073515411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37796020127320655382343607 56694030190980983073515411)
        ·
          refine ⟨85041045286471474610273117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56694030190980983073515411 85041045286471474610273117)
          ·
            refine ⟨31890391982426802978852419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85041045286471474610273117 31890391982426802978852419)
            ·
              refine ⟨47835587973640204468278629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31890391982426802978852419 47835587973640204468278629)
              ·
                refine ⟨8969172745057538337802243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47835587973640204468278629 8969172745057538337802243)
                ·
                  refine ⟨13453759117586307506703365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8969172745057538337802243 13453759117586307506703365)
                  ·
                    refine ⟨2522579834547432657506881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13453759117586307506703365 2522579834547432657506881)
                    ·
                      refine ⟨1891934875910574493130161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2522579834547432657506881 1891934875910574493130161)
                      ·
                        rfl

theorem cell23_3684530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 4, 1, 4, 2].length) (baseStart_3684530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3684530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3684530 prefixEnd_3684530 := by exact prefixLift 3684530
  have htrace : WordTrace (prefixWord ++ tailWord_3684530) baseStart_3684530 baseEnd_3684530 := by
    simpa [prefixWord, tailWord_3684530, baseEnd_3684530] using wordTrace_append hprefix tailTrace_3684530
  have hstable : (prefixWord ++ tailWord_3684530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684530).length < 2 ^ (prefixWord ++ tailWord_3684530).sum := by decide
  have hdescent : baseEnd_3684530 < baseStart_3684530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684536 : List Nat := [2, 1, 2, 1, 2, 1, 3, 2, 9]
def baseStart_3684536 : Nat := 118140960795 + 3684536 * 2 ^ 59
def prefixEnd_3684536 : Nat := 4983230072969 + 3 ^ 40 * 3684536 * 2
def baseEnd_3684536 : Nat := 210215328532722385517237

theorem tailTrace_3684536 : CollatzResearch.WordTrace tailWord_3684536 prefixEnd_3684536 210215328532722385517237 := by
  unfold tailWord_3684536
  simp only [CollatzResearch.WordTrace]
  refine ⟨67193034089781407747636731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89590712119708543663515641 67193034089781407747636731)
  ·
    refine ⟨100789551134672111621455097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67193034089781407747636731 100789551134672111621455097)
    ·
      refine ⟨75592163351004083716091323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100789551134672111621455097 75592163351004083716091323)
      ·
        refine ⟨113388245026506125574136985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75592163351004083716091323 113388245026506125574136985)
        ·
          refine ⟨85041183769879594180602739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113388245026506125574136985 85041183769879594180602739)
          ·
            refine ⟨127561775654819391270904109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85041183769879594180602739 127561775654819391270904109)
            ·
              refine ⟨47835665870557271726589041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127561775654819391270904109 47835665870557271726589041)
              ·
                refine ⟨35876749402917953794941781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47835665870557271726589041 35876749402917953794941781)
                ·
                  refine ⟨210215328532722385517237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 35876749402917953794941781 210215328532722385517237)
                  ·
                    rfl

theorem cell23_3684536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 9].length) (baseStart_3684536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3684536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3684536 prefixEnd_3684536 := by exact prefixLift 3684536
  have htrace : WordTrace (prefixWord ++ tailWord_3684536) baseStart_3684536 baseEnd_3684536 := by
    simpa [prefixWord, tailWord_3684536, baseEnd_3684536] using wordTrace_append hprefix tailTrace_3684536
  have hstable : (prefixWord ++ tailWord_3684536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684536).length < 2 ^ (prefixWord ++ tailWord_3684536).sum := by decide
  have hdescent : baseEnd_3684536 < baseStart_3684536 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684590 : List Nat := [4, 1, 2, 1, 1, 1, 1, 2, 1, 7, 2]
def baseStart_3684590 : Nat := 118140960795 + 3684590 * 2 ^ 59
def prefixEnd_3684590 : Nat := 4983230072969 + 3 ^ 40 * 3684590 * 2
def baseEnd_3684590 : Nat := 1891965684749844258379885

theorem tailTrace_3684590 : CollatzResearch.WordTrace tailWord_3684590 prefixEnd_3684590 1891965684749844258379885 := by
  unfold tailWord_3684590
  simp only [CollatzResearch.WordTrace]
  refine ⟨16798504715170897839717403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89592025147578121811826149 16798504715170897839717403)
  ·
    refine ⟨25197757072756346759576105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16798504715170897839717403 25197757072756346759576105)
    ·
      refine ⟨18898317804567260069682079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25197757072756346759576105 18898317804567260069682079)
      ·
        refine ⟨28347476706850890104523119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18898317804567260069682079 28347476706850890104523119)
        ·
          refine ⟨42521215060276335156784679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28347476706850890104523119 42521215060276335156784679)
          ·
            refine ⟨63781822590414502735177019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42521215060276335156784679 63781822590414502735177019)
            ·
              refine ⟨95672733885621754102765529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63781822590414502735177019 95672733885621754102765529)
              ·
                refine ⟨71754550414216315577074147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95672733885621754102765529 71754550414216315577074147)
                ·
                  refine ⟨107631825621324473365611221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71754550414216315577074147 107631825621324473365611221)
                  ·
                    refine ⟨2522620912999792344506513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 107631825621324473365611221 2522620912999792344506513)
                    ·
                      refine ⟨1891965684749844258379885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2522620912999792344506513 1891965684749844258379885)
                      ·
                        rfl

theorem cell23_3684590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 1, 7, 2].length) (baseStart_3684590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3684590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3684590 prefixEnd_3684590 := by exact prefixLift 3684590
  have htrace : WordTrace (prefixWord ++ tailWord_3684590) baseStart_3684590 baseEnd_3684590 := by
    simpa [prefixWord, tailWord_3684590, baseEnd_3684590] using wordTrace_append hprefix tailTrace_3684590
  have hstable : (prefixWord ++ tailWord_3684590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684590).length < 2 ^ (prefixWord ++ tailWord_3684590).sum := by decide
  have hdescent : baseEnd_3684590 < baseStart_3684590 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684610 : List Nat := [3, 4, 1, 1, 2, 1, 1, 1, 1, 1, 7]
def baseStart_3684610 : Nat := 118140960795 + 3684610 * 2 ^ 59
def prefixEnd_3684610 : Nat := 4983230072969 + 3 ^ 40 * 3684610 * 2
def baseEnd_3684610 : Nat := 1891975954362934180129793

theorem tailTrace_3684610 : CollatzResearch.WordTrace tailWord_3684610 prefixEnd_3684610 1891975954362934180129793 := by
  unfold tailWord_3684610
  simp only [CollatzResearch.WordTrace]
  refine ⟨33597191795323681533366821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89592511454196484088978189 33597191795323681533366821)
  ·
    refine ⟨6299473461623190287506279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33597191795323681533366821 6299473461623190287506279)
    ·
      refine ⟨9449210192434785431259419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6299473461623190287506279 9449210192434785431259419)
      ·
        refine ⟨14173815288652178146889129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9449210192434785431259419 14173815288652178146889129)
        ·
          refine ⟨10630361466489133610166847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14173815288652178146889129 10630361466489133610166847)
          ·
            refine ⟨15945542199733700415250271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10630361466489133610166847 15945542199733700415250271)
            ·
              refine ⟨23918313299600550622875407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15945542199733700415250271 23918313299600550622875407)
              ·
                refine ⟨35877469949400825934313111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23918313299600550622875407 35877469949400825934313111)
                ·
                  refine ⟨53816204924101238901469667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35877469949400825934313111 53816204924101238901469667)
                  ·
                    refine ⟨80724307386151858352204501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53816204924101238901469667 80724307386151858352204501)
                    ·
                      refine ⟨1891975954362934180129793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 80724307386151858352204501 1891975954362934180129793)
                      ·
                        rfl

theorem cell23_3684610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_3684610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3684610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3684610 prefixEnd_3684610 := by exact prefixLift 3684610
  have htrace : WordTrace (prefixWord ++ tailWord_3684610) baseStart_3684610 baseEnd_3684610 := by
    simpa [prefixWord, tailWord_3684610, baseEnd_3684610] using wordTrace_append hprefix tailTrace_3684610
  have hstable : (prefixWord ++ tailWord_3684610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684610).length < 2 ^ (prefixWord ++ tailWord_3684610).sum := by decide
  have hdescent : baseEnd_3684610 < baseStart_3684610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684615 : List Nat := [1, 1, 4, 5, 2, 1, 2, 1, 2, 2, 2]
def baseStart_3684615 : Nat := 118140960795 + 3684615 * 2 ^ 59
def prefixEnd_3684615 : Nat := 4983230072969 + 3 ^ 40 * 3684615 * 2
def baseEnd_3684615 : Nat := 1891978521766206660567271

theorem tailTrace_3684615 : CollatzResearch.WordTrace tailWord_3684615 prefixEnd_3684615 1891978521766206660567271 := by
  unfold tailWord_3684615
  simp only [CollatzResearch.WordTrace]
  refine ⟨134388949546276611987399299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89592633030851074658266199 134388949546276611987399299)
  ·
    refine ⟨201583424319414917981098949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134388949546276611987399299 201583424319414917981098949)
    ·
      refine ⟨37796892059890297121456053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 201583424319414917981098949 37796892059890297121456053)
      ·
        refine ⟨3543458630614715355136505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37796892059890297121456053 3543458630614715355136505)
        ·
          refine ⟨2657593972961036516352379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3543458630614715355136505 2657593972961036516352379)
          ·
            refine ⟨3986390959441554774528569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2657593972961036516352379 3986390959441554774528569)
            ·
              refine ⟨2989793219581166080896427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3986390959441554774528569 2989793219581166080896427)
              ·
                refine ⟨4484689829371749121344641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2989793219581166080896427 4484689829371749121344641)
                ·
                  refine ⟨3363517372028811841008481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4484689829371749121344641 3363517372028811841008481)
                  ·
                    refine ⟨2522638029021608880756361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3363517372028811841008481 2522638029021608880756361)
                    ·
                      refine ⟨1891978521766206660567271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2522638029021608880756361 1891978521766206660567271)
                      ·
                        rfl

theorem cell23_3684615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_3684615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3684615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3684615 prefixEnd_3684615 := by exact prefixLift 3684615
  have htrace : WordTrace (prefixWord ++ tailWord_3684615) baseStart_3684615 baseEnd_3684615 := by
    simpa [prefixWord, tailWord_3684615, baseEnd_3684615] using wordTrace_append hprefix tailTrace_3684615
  have hstable : (prefixWord ++ tailWord_3684615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684615).length < 2 ^ (prefixWord ++ tailWord_3684615).sum := by decide
  have hdescent : baseEnd_3684615 < baseStart_3684615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684620 : List Nat := [2, 2, 1, 2, 2, 2, 2, 1, 1, 6, 2]
def baseStart_3684620 : Nat := 118140960795 + 3684620 * 2 ^ 59
def prefixEnd_3684620 : Nat := 4983230072969 + 3 ^ 40 * 3684620 * 2
def baseEnd_3684620 : Nat := 1891981089169479141004747

theorem tailTrace_3684620 : CollatzResearch.WordTrace tailWord_3684620 prefixEnd_3684620 1891981089169479141004747 := by
  unfold tailWord_3684620
  simp only [CollatzResearch.WordTrace]
  refine ⟨67194565955629248920665657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89592754607505665227554209 67194565955629248920665657)
  ·
    refine ⟨50395924466721936690499243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67194565955629248920665657 50395924466721936690499243)
    ·
      refine ⟨75593886700082905035748865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50395924466721936690499243 75593886700082905035748865)
      ·
        refine ⟨56695415025062178776811649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75593886700082905035748865 56695415025062178776811649)
        ·
          refine ⟨42521561268796634082608737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56695415025062178776811649 42521561268796634082608737)
          ·
            refine ⟨31891170951597475561956553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42521561268796634082608737 31891170951597475561956553)
            ·
              refine ⟨23918378213698106671467415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31891170951597475561956553 23918378213698106671467415)
              ·
                refine ⟨35877567320547160007201123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23918378213698106671467415 35877567320547160007201123)
                ·
                  refine ⟨53816350980820740010801685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35877567320547160007201123 53816350980820740010801685)
                  ·
                    refine ⟨2522641452225972188006329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 53816350980820740010801685 2522641452225972188006329)
                    ·
                      refine ⟨1891981089169479141004747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2522641452225972188006329 1891981089169479141004747)
                      ·
                        rfl

theorem cell23_3684620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 1, 6, 2].length) (baseStart_3684620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3684620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3684620 prefixEnd_3684620 := by exact prefixLift 3684620
  have htrace : WordTrace (prefixWord ++ tailWord_3684620) baseStart_3684620 baseEnd_3684620 := by
    simpa [prefixWord, tailWord_3684620, baseEnd_3684620] using wordTrace_append hprefix tailTrace_3684620
  have hstable : (prefixWord ++ tailWord_3684620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684620).length < 2 ^ (prefixWord ++ tailWord_3684620).sum := by decide
  have hdescent : baseEnd_3684620 < baseStart_3684620 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684623 : List Nat := [1, 1, 2, 1, 1, 1, 3, 3, 3, 4, 3]
def baseStart_3684623 : Nat := 118140960795 + 3684623 * 2 ^ 59
def prefixEnd_3684623 : Nat := 4983230072969 + 3 ^ 40 * 3684623 * 2
def baseEnd_3684623 : Nat := 1891982629611442629267233

theorem tailTrace_3684623 : CollatzResearch.WordTrace tailWord_3684623 prefixEnd_3684623 1891982629611442629267233 := by
  unfold tailWord_3684623
  simp only [CollatzResearch.WordTrace]
  refine ⟨134389241330247629353690523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89592827553498419569127015 134389241330247629353690523)
  ·
    refine ⟨201583861995371444030535785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134389241330247629353690523 201583861995371444030535785)
    ·
      refine ⟨151187896496528583022901839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201583861995371444030535785 151187896496528583022901839)
      ·
        refine ⟨226781844744792874534352759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151187896496528583022901839 226781844744792874534352759)
        ·
          refine ⟨340172767117189311801529139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226781844744792874534352759 340172767117189311801529139)
          ·
            refine ⟨510259150675783967702293709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340172767117189311801529139 510259150675783967702293709)
            ·
              refine ⟨191347181503418987888360141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 510259150675783967702293709 191347181503418987888360141)
              ·
                refine ⟨71755193063782120458135053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 191347181503418987888360141 71755193063782120458135053)
                ·
                  refine ⟨26908197398918295171800645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71755193063782120458135053 26908197398918295171800645)
                  ·
                    refine ⟨5045287012297180344712621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26908197398918295171800645 5045287012297180344712621)
                    ·
                      refine ⟨1891982629611442629267233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5045287012297180344712621 1891982629611442629267233)
                      ·
                        rfl

theorem cell23_3684623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3, 4, 3].length) (baseStart_3684623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3684623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3684623 prefixEnd_3684623 := by exact prefixLift 3684623
  have htrace : WordTrace (prefixWord ++ tailWord_3684623) baseStart_3684623 baseEnd_3684623 := by
    simpa [prefixWord, tailWord_3684623, baseEnd_3684623] using wordTrace_append hprefix tailTrace_3684623
  have hstable : (prefixWord ++ tailWord_3684623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684623).length < 2 ^ (prefixWord ++ tailWord_3684623).sum := by decide
  have hdescent : baseEnd_3684623 < baseStart_3684623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684664 : List Nat := [2, 1, 2, 1, 3, 1, 6, 2, 1, 4]
def baseStart_3684664 : Nat := 118140960795 + 3684664 * 2 ^ 59
def prefixEnd_3684664 : Nat := 4983230072969 + 3 ^ 40 * 3684664 * 2
def baseEnd_3684664 : Nat := 630667894106092322951515

theorem tailTrace_3684664 : CollatzResearch.WordTrace tailWord_3684664 prefixEnd_3684664 630667894106092322951515 := by
  unfold tailWord_3684664
  simp only [CollatzResearch.WordTrace]
  refine ⟨67195368361549546677966523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89593824482066062237288697 67195368361549546677966523)
  ·
    refine ⟨100793052542324320016949785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67195368361549546677966523 100793052542324320016949785)
    ·
      refine ⟨75594789406743240012712339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100793052542324320016949785 75594789406743240012712339)
      ·
        refine ⟨113392184110114860019068509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75594789406743240012712339 113392184110114860019068509)
        ·
          refine ⟨42522069041293072507150691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113392184110114860019068509 42522069041293072507150691)
          ·
            refine ⟨63783103561939608760726037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42522069041293072507150691 63783103561939608760726037)
            ·
              refine ⟨2989832979465919160659033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 63783103561939608760726037 2989832979465919160659033)
              ·
                refine ⟨2242374734599439370494275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2989832979465919160659033 2242374734599439370494275)
                ·
                  refine ⟨3363562101899159055741413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2242374734599439370494275 3363562101899159055741413)
                  ·
                    refine ⟨630667894106092322951515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3363562101899159055741413 630667894106092322951515)
                    ·
                      rfl

theorem cell23_3684664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 6, 2, 1, 4].length) (baseStart_3684664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3684664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3684664 prefixEnd_3684664 := by exact prefixLift 3684664
  have htrace : WordTrace (prefixWord ++ tailWord_3684664) baseStart_3684664 baseEnd_3684664 := by
    simpa [prefixWord, tailWord_3684664, baseEnd_3684664] using wordTrace_append hprefix tailTrace_3684664
  have hstable : (prefixWord ++ tailWord_3684664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684664).length < 2 ^ (prefixWord ++ tailWord_3684664).sum := by decide
  have hdescent : baseEnd_3684664 < baseStart_3684664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684690 : List Nat := [3, 2, 2, 1, 1, 1, 4, 1, 3, 5]
def baseStart_3684690 : Nat := 118140960795 + 3684690 * 2 ^ 59
def prefixEnd_3684690 : Nat := 4983230072969 + 3 ^ 40 * 3684690 * 2
def baseEnd_3684690 : Nat := 630672344271764622376475

theorem tailTrace_3684690 : CollatzResearch.WordTrace tailWord_3684690 prefixEnd_3684690 630672344271764622376475 := by
  unfold tailWord_3684690
  simp only [CollatzResearch.WordTrace]
  refine ⟨33597921255251224949094881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89594456680669933197586349 33597921255251224949094881)
  ·
    refine ⟨25198440941438418711821161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33597921255251224949094881 25198440941438418711821161)
    ·
      refine ⟨18898830706078814033865871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25198440941438418711821161 18898830706078814033865871)
      ·
        refine ⟨28348246059118221050798807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18898830706078814033865871 28348246059118221050798807)
        ·
          refine ⟨42522369088677331576198211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28348246059118221050798807 42522369088677331576198211)
          ·
            refine ⟨63783553633015997364297317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42522369088677331576198211 63783553633015997364297317)
            ·
              refine ⟨11959416306190499505805747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63783553633015997364297317 11959416306190499505805747)
              ·
                refine ⟨17939124459285749258708621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11959416306190499505805747 17939124459285749258708621)
                ·
                  refine ⟨6727171672232155972015733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17939124459285749258708621 6727171672232155972015733)
                  ·
                    refine ⟨630672344271764622376475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6727171672232155972015733 630672344271764622376475)
                    ·
                      rfl

theorem cell23_3684690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 1, 3, 5].length) (baseStart_3684690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3684690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3684690 prefixEnd_3684690 := by exact prefixLift 3684690
  have htrace : WordTrace (prefixWord ++ tailWord_3684690) baseStart_3684690 baseEnd_3684690 := by
    simpa [prefixWord, tailWord_3684690, baseEnd_3684690] using wordTrace_append hprefix tailTrace_3684690
  have hstable : (prefixWord ++ tailWord_3684690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684690).length < 2 ^ (prefixWord ++ tailWord_3684690).sum := by decide
  have hdescent : baseEnd_3684690 < baseStart_3684690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684723 : List Nat := [1, 1, 1, 2, 2, 1, 2, 3, 3, 1, 6]
def baseStart_3684723 : Nat := 118140960795 + 3684723 * 2 ^ 59
def prefixEnd_3684723 : Nat := 4983230072969 + 3 ^ 40 * 3684723 * 2
def baseEnd_3684723 : Nat := 1892033977676892238016773

theorem tailTrace_3684723 : CollatzResearch.WordTrace tailWord_3684723 prefixEnd_3684723 1892033977676892238016773 := by
  unfold tailWord_3684723
  simp only [CollatzResearch.WordTrace]
  refine ⟨134392888629885346432330823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89595259086590230954887215 134392888629885346432330823)
  ·
    refine ⟨201589332944828019648496235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134392888629885346432330823 201589332944828019648496235)
    ·
      refine ⟨302383999417242029472744353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201589332944828019648496235 302383999417242029472744353)
      ·
        refine ⟨226787999562931522104558265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302383999417242029472744353 226787999562931522104558265)
        ·
          refine ⟨170090999672198641578418699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226787999562931522104558265 170090999672198641578418699)
          ·
            refine ⟨255136499508297962367628049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170090999672198641578418699 255136499508297962367628049)
            ·
              refine ⟨191352374631223471775721037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255136499508297962367628049 191352374631223471775721037)
              ·
                refine ⟨71757140486708801915895389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 191352374631223471775721037 71757140486708801915895389)
                ·
                  refine ⟨26908927682515800718460771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71757140486708801915895389 26908927682515800718460771)
                  ·
                    refine ⟨40363391523773701077691157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26908927682515800718460771 40363391523773701077691157)
                    ·
                      refine ⟨1892033977676892238016773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40363391523773701077691157 1892033977676892238016773)
                      ·
                        rfl

theorem cell23_3684723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3, 1, 6].length) (baseStart_3684723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3684723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3684723 prefixEnd_3684723 := by exact prefixLift 3684723
  have htrace : WordTrace (prefixWord ++ tailWord_3684723) baseStart_3684723 baseEnd_3684723 := by
    simpa [prefixWord, tailWord_3684723, baseEnd_3684723] using wordTrace_append hprefix tailTrace_3684723
  have hstable : (prefixWord ++ tailWord_3684723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684723).length < 2 ^ (prefixWord ++ tailWord_3684723).sum := by decide
  have hdescent : baseEnd_3684723 < baseStart_3684723 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684737 : List Nat := [1, 2, 4, 3, 1, 1, 3, 1, 1, 6]
def baseStart_3684737 : Nat := 118140960795 + 3684737 * 2 ^ 59
def prefixEnd_3684737 : Nat := 4983230072969 + 3 ^ 40 * 3684737 * 2
def baseEnd_3684737 : Nat := 630680388802018394413903

theorem tailTrace_3684737 : CollatzResearch.WordTrace tailWord_3684737 prefixEnd_3684737 630680388802018394413903 := by
  unfold tailWord_3684737
  simp only [CollatzResearch.WordTrace]
  refine ⟨134393399251834626823340465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89595599501223084548893643 134393399251834626823340465)
  ·
    refine ⟨100795049438875970117505349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134393399251834626823340465 100795049438875970117505349)
    ·
      refine ⟨18899071769789244397032253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100795049438875970117505349 18899071769789244397032253)
      ·
        refine ⟨7087151913670966648887095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18899071769789244397032253 7087151913670966648887095)
        ·
          refine ⟨10630727870506449973330643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7087151913670966648887095 10630727870506449973330643)
          ·
            refine ⟨15946091805759674959995965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10630727870506449973330643 15946091805759674959995965)
            ·
              refine ⟨5979784427159878109998487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15946091805759674959995965 5979784427159878109998487)
              ·
                refine ⟨8969676640739817164997731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5979784427159878109998487 8969676640739817164997731)
                ·
                  refine ⟨13454514961109725747496597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8969676640739817164997731 13454514961109725747496597)
                  ·
                    refine ⟨630680388802018394413903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13454514961109725747496597 630680388802018394413903)
                    ·
                      rfl

theorem cell23_3684737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 1, 1, 6].length) (baseStart_3684737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3684737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3684737 prefixEnd_3684737 := by exact prefixLift 3684737
  have htrace : WordTrace (prefixWord ++ tailWord_3684737) baseStart_3684737 baseEnd_3684737 := by
    simpa [prefixWord, tailWord_3684737, baseEnd_3684737] using wordTrace_append hprefix tailTrace_3684737
  have hstable : (prefixWord ++ tailWord_3684737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684737).length < 2 ^ (prefixWord ++ tailWord_3684737).sum := by decide
  have hdescent : baseEnd_3684737 < baseStart_3684737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684740 : List Nat := [2, 3, 2, 1, 1, 2, 3, 1, 1, 1, 6]
def baseStart_3684740 : Nat := 118140960795 + 3684740 * 2 ^ 59
def prefixEnd_3684740 : Nat := 4983230072969 + 3 ^ 40 * 3684740 * 2
def baseEnd_3684740 : Nat := 1892042706848018671504195

theorem tailTrace_3684740 : CollatzResearch.WordTrace tailWord_3684740 prefixEnd_3684740 1892042706848018671504195 := by
  unfold tailWord_3684740
  simp only [CollatzResearch.WordTrace]
  refine ⟨67196754335411879167849837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89595672447215838890466449 67196754335411879167849837)
  ·
    refine ⟨25198782875779454687943689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67196754335411879167849837 25198782875779454687943689)
    ·
      refine ⟨18899087156834591015957767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25198782875779454687943689 18899087156834591015957767)
      ·
        refine ⟨28348630735251886523936651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18899087156834591015957767 28348630735251886523936651)
        ·
          refine ⟨42522946102877829785904977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28348630735251886523936651 42522946102877829785904977)
          ·
            refine ⟨31892209577158372339428733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42522946102877829785904977 31892209577158372339428733)
            ·
              refine ⟨11959578591434389627285775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31892209577158372339428733 11959578591434389627285775)
              ·
                refine ⟨17939367887151584440928663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11959578591434389627285775 17939367887151584440928663)
                ·
                  refine ⟨26909051830727376661392995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17939367887151584440928663 26909051830727376661392995)
                  ·
                    refine ⟨40363577746091064992089493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26909051830727376661392995 40363577746091064992089493)
                    ·
                      refine ⟨1892042706848018671504195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40363577746091064992089493 1892042706848018671504195)
                      ·
                        rfl

theorem cell23_3684740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_3684740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3684740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3684740 prefixEnd_3684740 := by exact prefixLift 3684740
  have htrace : WordTrace (prefixWord ++ tailWord_3684740) baseStart_3684740 baseEnd_3684740 := by
    simpa [prefixWord, tailWord_3684740, baseEnd_3684740] using wordTrace_append hprefix tailTrace_3684740
  have hstable : (prefixWord ++ tailWord_3684740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684740).length < 2 ^ (prefixWord ++ tailWord_3684740).sum := by decide
  have hdescent : baseEnd_3684740 < baseStart_3684740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684744 : List Nat := [2, 1, 3, 3, 1, 1, 1, 4, 3, 2, 2]
def baseStart_3684744 : Nat := 118140960795 + 3684744 * 2 ^ 59
def prefixEnd_3684744 : Nat := 4983230072969 + 3 ^ 40 * 3684744 * 2
def baseEnd_3684744 : Nat := 1892044760770636655854177

theorem tailTrace_3684744 : CollatzResearch.WordTrace tailWord_3684744 prefixEnd_3684744 1892044760770636655854177 := by
  unfold tailWord_3684744
  simp only [CollatzResearch.WordTrace]
  refine ⟨67196827281404633509422643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89595769708539511345896857 67196827281404633509422643)
  ·
    refine ⟨100795240922106950264133965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67196827281404633509422643 100795240922106950264133965)
    ·
      refine ⟨37798215345790106349050237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100795240922106950264133965 37798215345790106349050237)
      ·
        refine ⟨14174330754671289880893839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37798215345790106349050237 14174330754671289880893839)
        ·
          refine ⟨21261496132006934821340759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14174330754671289880893839 21261496132006934821340759)
          ·
            refine ⟨31892244198010402232011139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21261496132006934821340759 31892244198010402232011139)
            ·
              refine ⟨47838366297015603348016709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31892244198010402232011139 47838366297015603348016709)
              ·
                refine ⟨8969693680690425627753133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47838366297015603348016709 8969693680690425627753133)
                ·
                  refine ⟨3363635130258909610407425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8969693680690425627753133 3363635130258909610407425)
                  ·
                    refine ⟨2522726347694182207805569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3363635130258909610407425 2522726347694182207805569)
                    ·
                      refine ⟨1892044760770636655854177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2522726347694182207805569 1892044760770636655854177)
                      ·
                        rfl

theorem cell23_3684744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 4, 3, 2, 2].length) (baseStart_3684744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3684744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3684744 prefixEnd_3684744 := by exact prefixLift 3684744
  have htrace : WordTrace (prefixWord ++ tailWord_3684744) baseStart_3684744 baseEnd_3684744 := by
    simpa [prefixWord, tailWord_3684744, baseEnd_3684744] using wordTrace_append hprefix tailTrace_3684744
  have hstable : (prefixWord ++ tailWord_3684744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684744).length < 2 ^ (prefixWord ++ tailWord_3684744).sum := by decide
  have hdescent : baseEnd_3684744 < baseStart_3684744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684747 : List Nat := [1, 1, 1, 1, 4, 4, 1, 4, 1, 2, 3]
def baseStart_3684747 : Nat := 118140960795 + 3684747 * 2 ^ 59
def prefixEnd_3684747 : Nat := 4983230072969 + 3 ^ 40 * 3684747 * 2
def baseEnd_3684747 : Nat := 1892046301212600144116663

theorem tailTrace_3684747 : CollatzResearch.WordTrace tailWord_3684747 prefixEnd_3684747 1892046301212600144116663 := by
  unfold tailWord_3684747
  simp only [CollatzResearch.WordTrace]
  refine ⟨134393763981798398531204495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89595842654532265687469663 134393763981798398531204495)
  ·
    refine ⟨201590645972697597796806743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134393763981798398531204495 201590645972697597796806743)
    ·
      refine ⟨302385968959046396695210115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201590645972697597796806743 302385968959046396695210115)
      ·
        refine ⟨453578953438569595042815173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302385968959046396695210115 453578953438569595042815173)
        ·
          refine ⟨85046053769731799070527845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 453578953438569595042815173 85046053769731799070527845)
          ·
            refine ⟨15946135081824712325723971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85046053769731799070527845 15946135081824712325723971)
            ·
              refine ⟨23919202622737068488585957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15946135081824712325723971 23919202622737068488585957)
              ·
                refine ⟨4484850491763200341609867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23919202622737068488585957 4484850491763200341609867)
                ·
                  refine ⟨6727275737644800512414801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4484850491763200341609867 6727275737644800512414801)
                  ·
                    refine ⟨5045456803233600384311101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6727275737644800512414801 5045456803233600384311101)
                    ·
                      refine ⟨1892046301212600144116663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5045456803233600384311101 1892046301212600144116663)
                      ·
                        rfl

theorem cell23_3684747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 4, 1, 2, 3].length) (baseStart_3684747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3684747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3684747 prefixEnd_3684747 := by exact prefixLift 3684747
  have htrace : WordTrace (prefixWord ++ tailWord_3684747) baseStart_3684747 baseEnd_3684747 := by
    simpa [prefixWord, tailWord_3684747, baseEnd_3684747] using wordTrace_append hprefix tailTrace_3684747
  have hstable : (prefixWord ++ tailWord_3684747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684747).length < 2 ^ (prefixWord ++ tailWord_3684747).sum := by decide
  have hdescent : baseEnd_3684747 < baseStart_3684747 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684788 : List Nat := [2, 5, 2, 2, 1, 1, 1, 3, 2, 4]
def baseStart_3684788 : Nat := 118140960795 + 3684788 * 2 ^ 59
def prefixEnd_3684788 : Nat := 4983230072969 + 3 ^ 40 * 3684788 * 2
def baseEnd_3684788 : Nat := 630689117973144827901325

theorem tailTrace_3684788 : CollatzResearch.WordTrace tailWord_3684788 prefixEnd_3684788 630689117973144827901325 := by
  unfold tailWord_3684788
  simp only [CollatzResearch.WordTrace]
  refine ⟨67197629687324931266723509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89596839583099908355631345 67197629687324931266723509)
  ·
    refine ⟨6299777783186712306255329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67197629687324931266723509 6299777783186712306255329)
    ·
      refine ⟨4724833337390034229691497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6299777783186712306255329 4724833337390034229691497)
      ·
        refine ⟨3543625003042525672268623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4724833337390034229691497 3543625003042525672268623)
        ·
          refine ⟨5315437504563788508402935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3543625003042525672268623 5315437504563788508402935)
          ·
            refine ⟨7973156256845682762604403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5315437504563788508402935 7973156256845682762604403)
            ·
              refine ⟨11959734385268524143906605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7973156256845682762604403 11959734385268524143906605)
              ·
                refine ⟨4484900394475696553964977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11959734385268524143906605 4484900394475696553964977)
                ·
                  refine ⟨3363675295856772415473733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4484900394475696553964977 3363675295856772415473733)
                  ·
                    refine ⟨630689117973144827901325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3363675295856772415473733 630689117973144827901325)
                    ·
                      rfl

theorem cell23_3684788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_3684788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3684788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3684788 prefixEnd_3684788 := by exact prefixLift 3684788
  have htrace : WordTrace (prefixWord ++ tailWord_3684788) baseStart_3684788 baseEnd_3684788 := by
    simpa [prefixWord, tailWord_3684788, baseEnd_3684788] using wordTrace_append hprefix tailTrace_3684788
  have hstable : (prefixWord ++ tailWord_3684788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684788).length < 2 ^ (prefixWord ++ tailWord_3684788).sum := by decide
  have hdescent : baseEnd_3684788 < baseStart_3684788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684874 : List Nat := [3, 1, 2, 2, 2, 1, 4, 3, 5]
def baseStart_3684874 : Nat := 118140960795 + 3684874 * 2 ^ 59
def prefixEnd_3684874 : Nat := 4983230072969 + 3 ^ 40 * 3684874 * 2
def baseEnd_3684874 : Nat := 210234612583969016358731

theorem tailTrace_3684874 : CollatzResearch.WordTrace tailWord_3684874 prefixEnd_3684874 210234612583969016358731 := by
  unfold tailWord_3684874
  simp only [CollatzResearch.WordTrace]
  refine ⟨33599599013084574805269419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89598930701558866147385117 33599599013084574805269419)
  ·
    refine ⟨50399398519626862207904129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33599599013084574805269419 50399398519626862207904129)
    ·
      refine ⟨37799548889720146655928097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50399398519626862207904129 37799548889720146655928097)
      ·
        refine ⟨28349661667290109991946073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37799548889720146655928097 28349661667290109991946073)
        ·
          refine ⟨21262246250467582493959555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28349661667290109991946073 21262246250467582493959555)
          ·
            refine ⟨31893369375701373740939333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21262246250467582493959555 31893369375701373740939333)
            ·
              refine ⟨5980006757944007576426125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31893369375701373740939333 5980006757944007576426125)
              ·
                refine ⟨2242502534229002841159797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5980006757944007576426125 2242502534229002841159797)
                ·
                  refine ⟨210234612583969016358731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2242502534229002841159797 210234612583969016358731)
                  ·
                    rfl

theorem cell23_3684874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 3, 5].length) (baseStart_3684874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3684874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3684874 prefixEnd_3684874 := by exact prefixLift 3684874
  have htrace : WordTrace (prefixWord ++ tailWord_3684874) baseStart_3684874 baseEnd_3684874 := by
    simpa [prefixWord, tailWord_3684874, baseEnd_3684874] using wordTrace_append hprefix tailTrace_3684874
  have hstable : (prefixWord ++ tailWord_3684874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684874).length < 2 ^ (prefixWord ++ tailWord_3684874).sum := by decide
  have hdescent : baseEnd_3684874 < baseStart_3684874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684927 : List Nat := [1, 1, 2, 2, 3, 2, 1, 3, 1, 4, 3]
def baseStart_3684927 : Nat := 118140960795 + 3684927 * 2 ^ 59
def prefixEnd_3684927 : Nat := 4983230072969 + 3 ^ 40 * 3684927 * 2
def baseEnd_3684927 : Nat := 1892138727730409439865835

theorem tailTrace_3684927 : CollatzResearch.WordTrace tailWord_3684927 prefixEnd_3684927 1892138727730409439865835 := by
  unfold tailWord_3684927
  simp only [CollatzResearch.WordTrace]
  refine ⟨134400329121146289272757035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89600219414097526181838023 134400329121146289272757035)
  ·
    refine ⟨201600493681719433909135553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134400329121146289272757035 201600493681719433909135553)
    ·
      refine ⟨151200370261289575431851665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201600493681719433909135553 151200370261289575431851665)
      ·
        refine ⟨113400277695967181573888749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151200370261289575431851665 113400277695967181573888749)
        ·
          refine ⟨42525104135987693090208281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113400277695967181573888749 42525104135987693090208281)
          ·
            refine ⟨31893828101990769817656211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42525104135987693090208281 31893828101990769817656211)
            ·
              refine ⟨47840742152986154726484317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31893828101990769817656211 47840742152986154726484317)
              ·
                refine ⟨17940278307369808022431619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47840742152986154726484317 17940278307369808022431619)
                ·
                  refine ⟨26910417461054712033647429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17940278307369808022431619 26910417461054712033647429)
                  ·
                    refine ⟨5045703273947758506308893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26910417461054712033647429 5045703273947758506308893)
                    ·
                      refine ⟨1892138727730409439865835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5045703273947758506308893 1892138727730409439865835)
                      ·
                        rfl

theorem cell23_3684927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3, 1, 4, 3].length) (baseStart_3684927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3684927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3684927 prefixEnd_3684927 := by exact prefixLift 3684927
  have htrace : WordTrace (prefixWord ++ tailWord_3684927) baseStart_3684927 baseEnd_3684927 := by
    simpa [prefixWord, tailWord_3684927, baseEnd_3684927] using wordTrace_append hprefix tailTrace_3684927
  have hstable : (prefixWord ++ tailWord_3684927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684927).length < 2 ^ (prefixWord ++ tailWord_3684927).sum := by decide
  have hdescent : baseEnd_3684927 < baseStart_3684927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684941 : List Nat := [1, 6, 1, 1, 2, 2, 1, 2, 2, 1, 4]
def baseStart_3684941 : Nat := 118140960795 + 3684941 * 2 ^ 59
def prefixEnd_3684941 : Nat := 4983230072969 + 3 ^ 40 * 3684941 * 2
def baseEnd_3684941 : Nat := 1892145916459572385090771

theorem tailTrace_3684941 : CollatzResearch.WordTrace tailWord_3684941 prefixEnd_3684941 1892145916459572385090771 := by
  unfold tailWord_3684941
  simp only [CollatzResearch.WordTrace]
  refine ⟨134400839743095569663766677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89600559828730379775844451 134400839743095569663766677)
  ·
    refine ⟨6300039362957604827989063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 134400839743095569663766677 6300039362957604827989063)
    ·
      refine ⟨9450059044436407241983595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6300039362957604827989063 9450059044436407241983595)
      ·
        refine ⟨14175088566654610862975393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9450059044436407241983595 14175088566654610862975393)
        ·
          refine ⟨10631316424990958147231545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14175088566654610862975393 10631316424990958147231545)
          ·
            refine ⟨7973487318743218610423659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10631316424990958147231545 7973487318743218610423659)
            ·
              refine ⟨11960230978114827915635489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7973487318743218610423659 11960230978114827915635489)
              ·
                refine ⟨8970173233586120936726617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11960230978114827915635489 8970173233586120936726617)
                ·
                  refine ⟨6727629925189590702544963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8970173233586120936726617 6727629925189590702544963)
                  ·
                    refine ⟨10091444887784386053817445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6727629925189590702544963 10091444887784386053817445)
                    ·
                      refine ⟨1892145916459572385090771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10091444887784386053817445 1892145916459572385090771)
                      ·
                        rfl

theorem cell23_3684941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_3684941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3684941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3684941 prefixEnd_3684941 := by exact prefixLift 3684941
  have htrace : WordTrace (prefixWord ++ tailWord_3684941) baseStart_3684941 baseEnd_3684941 := by
    simpa [prefixWord, tailWord_3684941, baseEnd_3684941] using wordTrace_append hprefix tailTrace_3684941
  have hstable : (prefixWord ++ tailWord_3684941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684941).length < 2 ^ (prefixWord ++ tailWord_3684941).sum := by decide
  have hdescent : baseEnd_3684941 < baseStart_3684941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684984 : List Nat := [2, 1, 2, 1, 1, 1, 2, 2, 6, 3, 2]
def baseStart_3684984 : Nat := 118140960795 + 3684984 * 2 ^ 59
def prefixEnd_3684984 : Nat := 4983230072969 + 3 ^ 40 * 3684984 * 2
def baseEnd_3684984 : Nat := 1892167996127715716853073

theorem tailTrace_3684984 : CollatzResearch.WordTrace tailWord_3684984 prefixEnd_3684984 1892167996127715716853073 := by
  unfold tailWord_3684984
  simp only [CollatzResearch.WordTrace]
  refine ⟨67201204040969894003791003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89601605387959858671721337 67201204040969894003791003)
  ·
    refine ⟨100801806061454841005686505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67201204040969894003791003 100801806061454841005686505)
    ·
      refine ⟨75601354546091130754264879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100801806061454841005686505 75601354546091130754264879)
      ·
        refine ⟨113402031819136696131397319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75601354546091130754264879 113402031819136696131397319)
        ·
          refine ⟨170103047728705044197095979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113402031819136696131397319 170103047728705044197095979)
          ·
            refine ⟨255154571593057566295643969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170103047728705044197095979 255154571593057566295643969)
            ·
              refine ⟨191365928694793174721732977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255154571593057566295643969 191365928694793174721732977)
              ·
                refine ⟨143524446521094881041299733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191365928694793174721732977 143524446521094881041299733)
                ·
                  refine ⟨6727708430676322548810925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 143524446521094881041299733 6727708430676322548810925)
                  ·
                    refine ⟨2522890661503620955804097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6727708430676322548810925 2522890661503620955804097)
                    ·
                      refine ⟨1892167996127715716853073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2522890661503620955804097 1892167996127715716853073)
                      ·
                        rfl

theorem cell23_3684984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 6, 3, 2].length) (baseStart_3684984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3684984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3684984 prefixEnd_3684984 := by exact prefixLift 3684984
  have htrace : WordTrace (prefixWord ++ tailWord_3684984) baseStart_3684984 baseEnd_3684984 := by
    simpa [prefixWord, tailWord_3684984, baseEnd_3684984] using wordTrace_append hprefix tailTrace_3684984
  have hstable : (prefixWord ++ tailWord_3684984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684984).length < 2 ^ (prefixWord ++ tailWord_3684984).sum := by decide
  have hdescent : baseEnd_3684984 < baseStart_3684984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3685002 : List Nat := [3, 1, 2, 3, 4, 1, 2, 2, 1, 4]
def baseStart_3685002 : Nat := 118140960795 + 3685002 * 2 ^ 59
def prefixEnd_3685002 : Nat := 4983230072969 + 3 ^ 40 * 3685002 * 2
def baseEnd_3685002 : Nat := 630725746259832215475997

theorem tailTrace_3685002 : CollatzResearch.WordTrace tailWord_3685002 prefixEnd_3685002 630725746259832215475997 := by
  unfold tailWord_3685002
  simp only [CollatzResearch.WordTrace]
  refine ⟨33600766148968644270434315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89602043063916384721158173 33600766148968644270434315)
  ·
    refine ⟨50401149223452966405651473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33600766148968644270434315 50401149223452966405651473)
    ·
      refine ⟨37800861917589724804238605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50401149223452966405651473 37800861917589724804238605)
      ·
        refine ⟨14175323219096146801589477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37800861917589724804238605 14175323219096146801589477)
        ·
          refine ⟨2657873103580527525298027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14175323219096146801589477 2657873103580527525298027)
          ·
            refine ⟨3986809655370791287947041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2657873103580527525298027 3986809655370791287947041)
            ·
              refine ⟨2990107241528093465960281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3986809655370791287947041 2990107241528093465960281)
              ·
                refine ⟨2242580431146070099470211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2990107241528093465960281 2242580431146070099470211)
                ·
                  refine ⟨3363870646719105149205317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2242580431146070099470211 3363870646719105149205317)
                  ·
                    refine ⟨630725746259832215475997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3363870646719105149205317 630725746259832215475997)
                    ·
                      rfl

theorem cell23_3685002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 2, 2, 1, 4].length) (baseStart_3685002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3685002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3685002 prefixEnd_3685002 := by exact prefixLift 3685002
  have htrace : WordTrace (prefixWord ++ tailWord_3685002) baseStart_3685002 baseEnd_3685002 := by
    simpa [prefixWord, tailWord_3685002, baseEnd_3685002] using wordTrace_append hprefix tailTrace_3685002
  have hstable : (prefixWord ++ tailWord_3685002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3685002).length < 2 ^ (prefixWord ++ tailWord_3685002).sum := by decide
  have hdescent : baseEnd_3685002 < baseStart_3685002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3685002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3685017 : List Nat := [1, 2, 1, 2, 1, 2, 4, 1, 3, 1, 5]
def baseStart_3685017 : Nat := 118140960795 + 3685017 * 2 ^ 59
def prefixEnd_3685017 : Nat := 4983230072969 + 3 ^ 40 * 3685017 * 2
def baseEnd_3685017 : Nat := 1892184940989314087740421

theorem tailTrace_3685017 : CollatzResearch.WordTrace tailWord_3685017 prefixEnd_3685017 1892184940989314087740421 := by
  unfold tailWord_3685017
  simp only [CollatzResearch.WordTrace]
  refine ⟨134403611690820234643533305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89602407793880156429022203 134403611690820234643533305)
  ·
    refine ⟨100802708768115175982649979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134403611690820234643533305 100802708768115175982649979)
    ·
      refine ⟨151204063152172763973974969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100802708768115175982649979 151204063152172763973974969)
      ·
        refine ⟨113403047364129572980481227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151204063152172763973974969 113403047364129572980481227)
        ·
          refine ⟨170104571046194359470721841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113403047364129572980481227 170104571046194359470721841)
          ·
            refine ⟨127578428284645769603041381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170104571046194359470721841 127578428284645769603041381)
            ·
              refine ⟨23920955303371081800570259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 127578428284645769603041381 23920955303371081800570259)
              ·
                refine ⟨35881432955056622700855389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23920955303371081800570259 35881432955056622700855389)
                ·
                  refine ⟨13455537358146233512820771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35881432955056622700855389 13455537358146233512820771)
                  ·
                    refine ⟨20183306037219350269231157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13455537358146233512820771 20183306037219350269231157)
                    ·
                      refine ⟨1892184940989314087740421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20183306037219350269231157 1892184940989314087740421)
                      ·
                        rfl

theorem cell23_3685017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 3, 1, 5].length) (baseStart_3685017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3685017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3685017 prefixEnd_3685017 := by exact prefixLift 3685017
  have htrace : WordTrace (prefixWord ++ tailWord_3685017) baseStart_3685017 baseEnd_3685017 := by
    simpa [prefixWord, tailWord_3685017, baseEnd_3685017] using wordTrace_append hprefix tailTrace_3685017
  have hstable : (prefixWord ++ tailWord_3685017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3685017).length < 2 ^ (prefixWord ++ tailWord_3685017).sum := by decide
  have hdescent : baseEnd_3685017 < baseStart_3685017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3685017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3685097 : List Nat := [1, 2, 1, 1, 1, 2, 4, 2, 1, 8]
def baseStart_3685097 : Nat := 118140960795 + 3685097 * 2 ^ 59
def prefixEnd_3685097 : Nat := 4983230072969 + 3 ^ 40 * 3685097 * 2
def baseEnd_3685097 : Nat := 630742006480557924913351

theorem tailTrace_3685097 : CollatzResearch.WordTrace tailWord_3685097 prefixEnd_3685097 630742006480557924913351 := by
  unfold tailWord_3685097
  simp only [CollatzResearch.WordTrace]
  refine ⟨134406529530530408306445545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89604353020353605537630363 134406529530530408306445545)
  ·
    refine ⟨100804897147897806229834159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134406529530530408306445545 100804897147897806229834159)
    ·
      refine ⟨151207345721846709344751239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100804897147897806229834159 151207345721846709344751239)
      ·
        refine ⟨226811018582770064017126859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151207345721846709344751239 226811018582770064017126859)
        ·
          refine ⟨340216527874155096025690289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226811018582770064017126859 340216527874155096025690289)
          ·
            refine ⟨255162395905616322019267717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 340216527874155096025690289 255162395905616322019267717)
            ·
              refine ⟨47842949232303060378612697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 255162395905616322019267717 47842949232303060378612697)
              ·
                refine ⟨35882211924227295283959523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47842949232303060378612697 35882211924227295283959523)
                ·
                  refine ⟨53823317886340942925939285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35882211924227295283959523 53823317886340942925939285)
                  ·
                    refine ⟨630742006480557924913351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 53823317886340942925939285 630742006480557924913351)
                    ·
                      rfl

theorem cell23_3685097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 8].length) (baseStart_3685097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3685097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3685097 prefixEnd_3685097 := by exact prefixLift 3685097
  have htrace : WordTrace (prefixWord ++ tailWord_3685097) baseStart_3685097 baseEnd_3685097 := by
    simpa [prefixWord, tailWord_3685097, baseEnd_3685097] using wordTrace_append hprefix tailTrace_3685097
  have hstable : (prefixWord ++ tailWord_3685097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3685097).length < 2 ^ (prefixWord ++ tailWord_3685097).sum := by decide
  have hdescent : baseEnd_3685097 < baseStart_3685097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3685097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3685124 : List Nat := [2, 3, 2, 2, 1, 1, 1, 2, 1, 3, 5]
def baseStart_3685124 : Nat := 118140960795 + 3685124 * 2 ^ 59
def prefixEnd_3685124 : Nat := 4983230072969 + 3 ^ 40 * 3685124 * 2
def baseEnd_3685124 : Nat := 1892239883419345169102429

theorem tailTrace_3685124 : CollatzResearch.WordTrace tailWord_3685124 prefixEnd_3685124 1892239883419345169102429 := by
  unfold tailWord_3685124
  simp only [CollatzResearch.WordTrace]
  refine ⟨67203757150716295958839213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89605009534288394611785617 67203757150716295958839213)
  ·
    refine ⟨25201408931518610984564705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67203757150716295958839213 25201408931518610984564705)
    ·
      refine ⟨18901056698638958238423529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25201408931518610984564705 18901056698638958238423529)
      ·
        refine ⟨14175792523979218678817647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18901056698638958238423529 14175792523979218678817647)
        ·
          refine ⟨21263688785968828018226471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14175792523979218678817647 21263688785968828018226471)
          ·
            refine ⟨31895533178953242027339707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21263688785968828018226471 31895533178953242027339707)
            ·
              refine ⟨47843299768429863041009561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31895533178953242027339707 47843299768429863041009561)
              ·
                refine ⟨35882474826322397280757171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47843299768429863041009561 35882474826322397280757171)
                ·
                  refine ⟨53823712239483595921135757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35882474826322397280757171 53823712239483595921135757)
                  ·
                    refine ⟨20183892089806348470425909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53823712239483595921135757 20183892089806348470425909)
                    ·
                      refine ⟨1892239883419345169102429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20183892089806348470425909 1892239883419345169102429)
                      ·
                        rfl

theorem cell23_3685124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_3685124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3685124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3685124 prefixEnd_3685124 := by exact prefixLift 3685124
  have htrace : WordTrace (prefixWord ++ tailWord_3685124) baseStart_3685124 baseEnd_3685124 := by
    simpa [prefixWord, tailWord_3685124, baseEnd_3685124] using wordTrace_append hprefix tailTrace_3685124
  have hstable : (prefixWord ++ tailWord_3685124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3685124).length < 2 ^ (prefixWord ++ tailWord_3685124).sum := by decide
  have hdescent : baseEnd_3685124 < baseStart_3685124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3685124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3685134 : List Nat := [4, 1, 1, 2, 1, 1, 1, 3, 1, 4, 4]
def baseStart_3685134 : Nat := 118140960795 + 3685134 * 2 ^ 59
def prefixEnd_3685134 : Nat := 4983230072969 + 3 ^ 40 * 3685134 * 2
def baseEnd_3685134 : Nat := 1892245018225890129977383

theorem tailTrace_3685134 : CollatzResearch.WordTrace tailWord_3685134 prefixEnd_3685134 1892245018225890129977383 := by
  unfold tailWord_3685134
  simp only [CollatzResearch.WordTrace]
  refine ⟨16800984878924545453192807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89605252687597575750361637 16800984878924545453192807)
  ·
    refine ⟨25201477318386818179789211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16800984878924545453192807 25201477318386818179789211)
    ·
      refine ⟨37802215977580227269683817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25201477318386818179789211 37802215977580227269683817)
      ·
        refine ⟨28351661983185170452262863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37802215977580227269683817 28351661983185170452262863)
        ·
          refine ⟨42527492974777755678394295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28351661983185170452262863 42527492974777755678394295)
          ·
            refine ⟨63791239462166633517591443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42527492974777755678394295 63791239462166633517591443)
            ·
              refine ⟨95686859193249950276387165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63791239462166633517591443 95686859193249950276387165)
              ·
                refine ⟨35882572197468731353645187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95686859193249950276387165 35882572197468731353645187)
                ·
                  refine ⟨53823858296203097030467781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35882572197468731353645187 53823858296203097030467781)
                  ·
                    refine ⟨10091973430538080693212709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53823858296203097030467781 10091973430538080693212709)
                    ·
                      refine ⟨1892245018225890129977383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10091973430538080693212709 1892245018225890129977383)
                      ·
                        rfl

theorem cell23_3685134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_3685134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3685134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3685134 prefixEnd_3685134 := by exact prefixLift 3685134
  have htrace : WordTrace (prefixWord ++ tailWord_3685134) baseStart_3685134 baseEnd_3685134 := by
    simpa [prefixWord, tailWord_3685134, baseEnd_3685134] using wordTrace_append hprefix tailTrace_3685134
  have hstable : (prefixWord ++ tailWord_3685134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3685134).length < 2 ^ (prefixWord ++ tailWord_3685134).sum := by decide
  have hdescent : baseEnd_3685134 < baseStart_3685134 := by decide
  rcases family_descends (prefixWord ++ tailWord_3685134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3685178 : List Nat := [3, 1, 1, 1, 6, 1, 1, 4, 5]
def baseStart_3685178 : Nat := 118140960795 + 3685178 * 2 ^ 59
def prefixEnd_3685178 : Nat := 4983230072969 + 3 ^ 40 * 3685178 * 2
def baseEnd_3685178 : Nat := 210251956819409773091909

theorem tailTrace_3685178 : CollatzResearch.WordTrace tailWord_3685178 prefixEnd_3685178 210251956819409773091909 := by
  unfold tailWord_3685178
  simp only [CollatzResearch.WordTrace]
  refine ⟨33602370960809239785036047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89606322562157972760096125 33602370960809239785036047)
  ·
    refine ⟨50403556441213859677554071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33602370960809239785036047 50403556441213859677554071)
    ·
      refine ⟨75605334661820789516331107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50403556441213859677554071 75605334661820789516331107)
      ·
        refine ⟨113408001992731184274496661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75605334661820789516331107 113408001992731184274496661)
        ·
          refine ⟨5316000093409274262867031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 113408001992731184274496661 5316000093409274262867031)
          ·
            refine ⟨7974000140113911394300547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5316000093409274262867031 7974000140113911394300547)
            ·
              refine ⟨11961000210170867091450821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7974000140113911394300547 11961000210170867091450821)
              ·
                refine ⟨2242687539407037579647029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11961000210170867091450821 2242687539407037579647029)
                ·
                  refine ⟨210251956819409773091909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2242687539407037579647029 210251956819409773091909)
                  ·
                    rfl

theorem cell23_3685178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 4, 5].length) (baseStart_3685178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3685178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3685178 prefixEnd_3685178 := by exact prefixLift 3685178
  have htrace : WordTrace (prefixWord ++ tailWord_3685178) baseStart_3685178 baseEnd_3685178 := by
    simpa [prefixWord, tailWord_3685178, baseEnd_3685178] using wordTrace_append hprefix tailTrace_3685178
  have hstable : (prefixWord ++ tailWord_3685178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3685178).length < 2 ^ (prefixWord ++ tailWord_3685178).sum := by decide
  have hdescent : baseEnd_3685178 < baseStart_3685178 := by decide
  rcases family_descends (prefixWord ++ tailWord_3685178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3685231 : List Nat := [1, 1, 2, 1, 3, 1, 1, 6, 2, 2, 3]
def baseStart_3685231 : Nat := 118140960795 + 3685231 * 2 ^ 59
def prefixEnd_3685231 : Nat := 4983230072969 + 3 ^ 40 * 3685231 * 2
def baseEnd_3685231 : Nat := 1892294825849376250464437

theorem tailTrace_3685231 : CollatzResearch.WordTrace tailWord_3685231 prefixEnd_3685231 1892294825849376250464437 := by
  unfold tailWord_3685231
  simp only [CollatzResearch.WordTrace]
  refine ⟨134411416912044949191823547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89607611274696632794549031 134411416912044949191823547)
  ·
    refine ⟨201617125368067423787735321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134411416912044949191823547 201617125368067423787735321)
    ·
      refine ⟨151212844026050567840801491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201617125368067423787735321 151212844026050567840801491)
      ·
        refine ⟨226819266039075851761202237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151212844026050567840801491 226819266039075851761202237)
        ·
          refine ⟨85057224764653444410450839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226819266039075851761202237 85057224764653444410450839)
          ·
            refine ⟨127585837146980166615676259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85057224764653444410450839 127585837146980166615676259)
            ·
              refine ⟨191378755720470249923514389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127585837146980166615676259 191378755720470249923514389)
              ·
                refine ⟨8970879174397042965164737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 191378755720470249923514389 8970879174397042965164737)
                ·
                  refine ⟨6728159380797782223873553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8970879174397042965164737 6728159380797782223873553)
                  ·
                    refine ⟨5046119535598336667905165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6728159380797782223873553 5046119535598336667905165)
                    ·
                      refine ⟨1892294825849376250464437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5046119535598336667905165 1892294825849376250464437)
                      ·
                        rfl

theorem cell23_3685231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 6, 2, 2, 3].length) (baseStart_3685231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3685231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3685231 prefixEnd_3685231 := by exact prefixLift 3685231
  have htrace : WordTrace (prefixWord ++ tailWord_3685231) baseStart_3685231 baseEnd_3685231 := by
    simpa [prefixWord, tailWord_3685231, baseEnd_3685231] using wordTrace_append hprefix tailTrace_3685231
  have hstable : (prefixWord ++ tailWord_3685231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3685231).length < 2 ^ (prefixWord ++ tailWord_3685231).sum := by decide
  have hdescent : baseEnd_3685231 < baseStart_3685231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3685231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3685311 : List Nat := [1, 1, 2, 2, 2, 1, 2, 2, 6, 4]
def baseStart_3685311 : Nat := 118140960795 + 3685311 * 2 ^ 59
def prefixEnd_3685311 : Nat := 4983230072969 + 3 ^ 40 * 3685311 * 2
def baseEnd_3685311 : Nat := 630778634767245312488023

theorem tailTrace_3685311 : CollatzResearch.WordTrace tailWord_3685311 prefixEnd_3685311 630778634767245312488023 := by
  unfold tailWord_3685311
  simp only [CollatzResearch.WordTrace]
  refine ⟨134414334751755122854735787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89609556501170081903157191 134414334751755122854735787)
  ·
    refine ⟨201621502127632684282103681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134414334751755122854735787 201621502127632684282103681)
    ·
      refine ⟨151216126595724513211577761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201621502127632684282103681 151216126595724513211577761)
      ·
        refine ⟨113412094946793384908683321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151216126595724513211577761 113412094946793384908683321)
        ·
          refine ⟨85059071210095038681512491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113412094946793384908683321 85059071210095038681512491)
          ·
            refine ⟨127588606815142558022268737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85059071210095038681512491 127588606815142558022268737)
            ·
              refine ⟨95691455111356918516701553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127588606815142558022268737 95691455111356918516701553)
              ·
                refine ⟨71768591333517688887526165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95691455111356918516701553 71768591333517688887526165)
                ·
                  refine ⟨3364152718758641666602789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 71768591333517688887526165 3364152718758641666602789)
                  ·
                    refine ⟨630778634767245312488023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3364152718758641666602789 630778634767245312488023)
                    ·
                      rfl

theorem cell23_3685311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 6, 4].length) (baseStart_3685311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3685311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3685311 prefixEnd_3685311 := by exact prefixLift 3685311
  have htrace : WordTrace (prefixWord ++ tailWord_3685311) baseStart_3685311 baseEnd_3685311 := by
    simpa [prefixWord, tailWord_3685311, baseEnd_3685311] using wordTrace_append hprefix tailTrace_3685311
  have hstable : (prefixWord ++ tailWord_3685311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3685311).length < 2 ^ (prefixWord ++ tailWord_3685311).sum := by decide
  have hdescent : baseEnd_3685311 < baseStart_3685311 := by decide
  rcases family_descends (prefixWord ++ tailWord_3685311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3685338 : List Nat := [3, 1, 1, 2, 4, 1, 3, 1, 1, 1, 5]
def baseStart_3685338 : Nat := 118140960795 + 3685338 * 2 ^ 59
def prefixEnd_3685338 : Nat := 4983230072969 + 3 ^ 40 * 3685338 * 2
def baseEnd_3685338 : Nat := 1892349768279407331826445

theorem tailTrace_3685338 : CollatzResearch.WordTrace tailWord_3685338 prefixEnd_3685338 1892349768279407331826445 := by
  unfold tailWord_3685338
  simp only [CollatzResearch.WordTrace]
  refine ⟨33603829880664326616492167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89610213015104870977312445 33603829880664326616492167)
  ·
    refine ⟨50405744820996489924738251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33603829880664326616492167 50405744820996489924738251)
    ·
      refine ⟨75608617231494734887107377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50405744820996489924738251 75608617231494734887107377)
      ·
        refine ⟨56706462923621051165330533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75608617231494734887107377 56706462923621051165330533)
        ·
          refine ⟨10632461798178947093499475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56706462923621051165330533 10632461798178947093499475)
          ·
            refine ⟨15948692697268420640249213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10632461798178947093499475 15948692697268420640249213)
            ·
              refine ⟨5980759761475657740093455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15948692697268420640249213 5980759761475657740093455)
              ·
                refine ⟨8971139642213486610140183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5980759761475657740093455 8971139642213486610140183)
                ·
                  refine ⟨13456709463320229915210275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8971139642213486610140183 13456709463320229915210275)
                  ·
                    refine ⟨20185064194980344872815413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13456709463320229915210275 20185064194980344872815413)
                    ·
                      refine ⟨1892349768279407331826445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20185064194980344872815413 1892349768279407331826445)
                      ·
                        rfl

theorem cell23_3685338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 1, 1, 1, 5].length) (baseStart_3685338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3685338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3685338 prefixEnd_3685338 := by exact prefixLift 3685338
  have htrace : WordTrace (prefixWord ++ tailWord_3685338) baseStart_3685338 baseEnd_3685338 := by
    simpa [prefixWord, tailWord_3685338, baseEnd_3685338] using wordTrace_append hprefix tailTrace_3685338
  have hstable : (prefixWord ++ tailWord_3685338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3685338).length < 2 ^ (prefixWord ++ tailWord_3685338).sum := by decide
  have hdescent : baseEnd_3685338 < baseStart_3685338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3685338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3685341 : List Nat := [1, 4, 3, 1, 2, 12]
def baseStart_3685341 : Nat := 118140960795 + 3685341 * 2 ^ 59
def prefixEnd_3685341 : Nat := 4983230072969 + 3 ^ 40 * 3685341 * 2
def baseEnd_3685341 : Nat := 7787453945355435473617

theorem tailTrace_3685341 : CollatzResearch.WordTrace tailWord_3685341 prefixEnd_3685341 7787453945355435473617 := by
  unfold tailWord_3685341
  simp only [CollatzResearch.WordTrace]
  refine ⟨134415428941646437978327877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89610285961097625318885251 134415428941646437978327877)
  ·
    refine ⟨25202892926558707120936477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134415428941646437978327877 25202892926558707120936477)
    ·
      refine ⟨9451084847459515170351179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25202892926558707120936477 9451084847459515170351179)
      ·
        refine ⟨14176627271189272755526769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9451084847459515170351179 14176627271189272755526769)
        ·
          refine ⟨10632470453391954566645077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14176627271189272755526769 10632470453391954566645077)
          ·
            refine ⟨7787453945355435473617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 10632470453391954566645077 7787453945355435473617)
            ·
              rfl

theorem cell23_3685341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 12].length) (baseStart_3685341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3685341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3685341 prefixEnd_3685341 := by exact prefixLift 3685341
  have htrace : WordTrace (prefixWord ++ tailWord_3685341) baseStart_3685341 baseEnd_3685341 := by
    simpa [prefixWord, tailWord_3685341, baseEnd_3685341] using wordTrace_append hprefix tailTrace_3685341
  have hstable : (prefixWord ++ tailWord_3685341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3685341).length < 2 ^ (prefixWord ++ tailWord_3685341).sum := by decide
  have hdescent : baseEnd_3685341 < baseStart_3685341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3685341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3685346 : List Nat := [3, 3, 3, 1, 1, 1, 4, 2, 1, 1, 3]
def baseStart_3685346 : Nat := 118140960795 + 3685346 * 2 ^ 59
def prefixEnd_3685346 : Nat := 4983230072969 + 3 ^ 40 * 3685346 * 2
def baseEnd_3685346 : Nat := 1892353876124643300526409

theorem tailTrace_3685346 : CollatzResearch.WordTrace tailWord_3685346 prefixEnd_3685346 1892353876124643300526409 := by
  unfold tailWord_3685346
  simp only [CollatzResearch.WordTrace]
  refine ⟨33603902826657080958064973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89610407537752215888173261 33603902826657080958064973)
  ·
    refine ⟨12601463559996405359274365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33603902826657080958064973 12601463559996405359274365)
    ·
      refine ⟨4725548834998652009727887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12601463559996405359274365 4725548834998652009727887)
      ·
        refine ⟨7088323252497978014591831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4725548834998652009727887 7088323252497978014591831)
        ·
          refine ⟨10632484878746967021887747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7088323252497978014591831 10632484878746967021887747)
          ·
            refine ⟨15948727318120450532831621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10632484878746967021887747 15948727318120450532831621)
            ·
              refine ⟨2990386372147584474905929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15948727318120450532831621 2990386372147584474905929)
              ·
                refine ⟨2242789779110688356179447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2990386372147584474905929 2242789779110688356179447)
                ·
                  refine ⟨3364184668666032534269171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2242789779110688356179447 3364184668666032534269171)
                  ·
                    refine ⟨5046277002999048801403757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3364184668666032534269171 5046277002999048801403757)
                    ·
                      refine ⟨1892353876124643300526409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5046277002999048801403757 1892353876124643300526409)
                      ·
                        rfl

theorem cell23_3685346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_3685346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3685346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3685346 prefixEnd_3685346 := by exact prefixLift 3685346
  have htrace : WordTrace (prefixWord ++ tailWord_3685346) baseStart_3685346 baseEnd_3685346 := by
    simpa [prefixWord, tailWord_3685346, baseEnd_3685346] using wordTrace_append hprefix tailTrace_3685346
  have hstable : (prefixWord ++ tailWord_3685346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3685346).length < 2 ^ (prefixWord ++ tailWord_3685346).sum := by decide
  have hdescent : baseEnd_3685346 < baseStart_3685346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3685346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3685368 : List Nat := [2, 1, 2, 1, 1, 3, 1, 2, 6, 1, 3]
def baseStart_3685368 : Nat := 118140960795 + 3685368 * 2 ^ 59
def prefixEnd_3685368 : Nat := 4983230072969 + 3 ^ 40 * 3685368 * 2
def baseEnd_3685368 : Nat := 1892365172699042214451307

theorem tailTrace_3685368 : CollatzResearch.WordTrace tailWord_3685368 prefixEnd_3685368 1892365172699042214451307 := by
  unfold tailWord_3685368
  simp only [CollatzResearch.WordTrace]
  refine ⟨67208206856274310794780379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89610942475032414393040505 67208206856274310794780379)
  ·
    refine ⟨100812310284411466192170569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67208206856274310794780379 100812310284411466192170569)
    ·
      refine ⟨75609232713308599644127927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100812310284411466192170569 75609232713308599644127927)
      ·
        refine ⟨113413849069962899466191891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75609232713308599644127927 113413849069962899466191891)
        ·
          refine ⟨170120773604944349199287837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113413849069962899466191891 170120773604944349199287837)
          ·
            refine ⟨63795290101854130949732939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170120773604944349199287837 63795290101854130949732939)
            ·
              refine ⟨95692935152781196424599409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63795290101854130949732939 95692935152781196424599409)
              ·
                refine ⟨71769701364585897318449557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95692935152781196424599409 71769701364585897318449557)
                ·
                  refine ⟨3364204751464963936802323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 71769701364585897318449557 3364204751464963936802323)
                  ·
                    refine ⟨5046307127197445905203485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3364204751464963936802323 5046307127197445905203485)
                    ·
                      refine ⟨1892365172699042214451307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5046307127197445905203485 1892365172699042214451307)
                      ·
                        rfl

theorem cell23_3685368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 6, 1, 3].length) (baseStart_3685368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3685368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3685368 prefixEnd_3685368 := by exact prefixLift 3685368
  have htrace : WordTrace (prefixWord ++ tailWord_3685368) baseStart_3685368 baseEnd_3685368 := by
    simpa [prefixWord, tailWord_3685368, baseEnd_3685368] using wordTrace_append hprefix tailTrace_3685368
  have hstable : (prefixWord ++ tailWord_3685368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3685368).length < 2 ^ (prefixWord ++ tailWord_3685368).sum := by decide
  have hdescent : baseEnd_3685368 < baseStart_3685368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3685368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3685381 : List Nat := [1, 3, 1, 1, 2, 3, 2, 1, 2, 2, 5]
def baseStart_3685381 : Nat := 118140960795 + 3685381 * 2 ^ 59
def prefixEnd_3685381 : Nat := 4983230072969 + 3 ^ 40 * 3685381 * 2
def baseEnd_3685381 : Nat := 1892371847947550663588747

theorem tailTrace_3685381 : CollatzResearch.WordTrace tailWord_3685381 prefixEnd_3685381 1892371847947550663588747 := by
  unfold tailWord_3685381
  simp only [CollatzResearch.WordTrace]
  refine ⟨134416887861501524809783997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89611258574334349873189331 134416887861501524809783997)
  ·
    refine ⟨50406332948063071803668999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134416887861501524809783997 50406332948063071803668999)
    ·
      refine ⟨75609499422094607705503499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50406332948063071803668999 75609499422094607705503499)
      ·
        refine ⟨113414249133141911558255249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75609499422094607705503499 113414249133141911558255249)
        ·
          refine ⟨85060686849856433668691437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113414249133141911558255249 85060686849856433668691437)
          ·
            refine ⟨31897757568696162625759289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85060686849856433668691437 31897757568696162625759289)
            ·
              refine ⟨23923318176522121969319467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31897757568696162625759289 23923318176522121969319467)
              ·
                refine ⟨35884977264783182953979201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23923318176522121969319467 35884977264783182953979201)
                ·
                  refine ⟨26913732948587387215484401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35884977264783182953979201 26913732948587387215484401)
                  ·
                    refine ⟨20185299711440540411613301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26913732948587387215484401 20185299711440540411613301)
                    ·
                      refine ⟨1892371847947550663588747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20185299711440540411613301 1892371847947550663588747)
                      ·
                        rfl

theorem cell23_3685381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 2, 2, 5].length) (baseStart_3685381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3685381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3685381 prefixEnd_3685381 := by exact prefixLift 3685381
  have htrace : WordTrace (prefixWord ++ tailWord_3685381) baseStart_3685381 baseEnd_3685381 := by
    simpa [prefixWord, tailWord_3685381, baseEnd_3685381] using wordTrace_append hprefix tailTrace_3685381
  have hstable : (prefixWord ++ tailWord_3685381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3685381).length < 2 ^ (prefixWord ++ tailWord_3685381).sum := by decide
  have hdescent : baseEnd_3685381 < baseStart_3685381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3685381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3685401 : List Nat := [1, 2, 1, 2, 1, 1, 5, 2, 2, 6]
def baseStart_3685401 : Nat := 118140960795 + 3685401 * 2 ^ 59
def prefixEnd_3685401 : Nat := 4983230072969 + 3 ^ 40 * 3685401 * 2
def baseEnd_3685401 : Nat := 630794039186880195112885

theorem tailTrace_3685401 : CollatzResearch.WordTrace tailWord_3685401 prefixEnd_3685401 630794039186880195112885 := by
  unfold tailWord_3685401
  simp only [CollatzResearch.WordTrace]
  refine ⟨134417617321429068225512057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89611744880952712150341371 134417617321429068225512057)
  ·
    refine ⟨100813212991071801169134043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134417617321429068225512057 100813212991071801169134043)
    ·
      refine ⟨151219819486607701753701065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100813212991071801169134043 151219819486607701753701065)
      ·
        refine ⟨113414864614955776315275799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151219819486607701753701065 113414864614955776315275799)
        ·
          refine ⟨170122296922433664472913699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113414864614955776315275799 170122296922433664472913699)
          ·
            refine ⟨255183445383650496709370549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170122296922433664472913699 255183445383650496709370549)
            ·
              refine ⟨23923448004717234066503489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 255183445383650496709370549 23923448004717234066503489)
              ·
                refine ⟨17942586003537925549877617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23923448004717234066503489 17942586003537925549877617)
                ·
                  refine ⟨13456939502653444162408213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17942586003537925549877617 13456939502653444162408213)
                  ·
                    refine ⟨630794039186880195112885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13456939502653444162408213 630794039186880195112885)
                    ·
                      rfl

theorem cell23_3685401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2, 2, 6].length) (baseStart_3685401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3685401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3685401 prefixEnd_3685401 := by exact prefixLift 3685401
  have htrace : WordTrace (prefixWord ++ tailWord_3685401) baseStart_3685401 baseEnd_3685401 := by
    simpa [prefixWord, tailWord_3685401, baseEnd_3685401] using wordTrace_append hprefix tailTrace_3685401
  have hstable : (prefixWord ++ tailWord_3685401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3685401).length < 2 ^ (prefixWord ++ tailWord_3685401).sum := by decide
  have hdescent : baseEnd_3685401 < baseStart_3685401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3685401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3685532 : List Nat := [2, 2, 3, 2, 1, 3, 1, 1, 2, 4, 2]
def baseStart_3685532 : Nat := 118140960795 + 3685532 * 2 ^ 59
def prefixEnd_3685532 : Nat := 4983230072969 + 3 ^ 40 * 3685532 * 2
def baseEnd_3685532 : Nat := 1892449383526379572800553

theorem tailTrace_3685532 : CollatzResearch.WordTrace tailWord_3685532 prefixEnd_3685532 1892449383526379572800553 := by
  unfold tailWord_3685532
  simp only [CollatzResearch.WordTrace]
  refine ⟨67211197641977238799265425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89614930189302985065687233 67211197641977238799265425)
  ·
    refine ⟨50408398231482929099449069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67211197641977238799265425 50408398231482929099449069)
    ·
      refine ⟨18903149336806098412293401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50408398231482929099449069 18903149336806098412293401)
      ·
        refine ⟨14177362002604573809220051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18903149336806098412293401 14177362002604573809220051)
        ·
          refine ⟨21266043003906860713830077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14177362002604573809220051 21266043003906860713830077)
          ·
            refine ⟨7974766126465072767686279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21266043003906860713830077 7974766126465072767686279)
            ·
              refine ⟨11962149189697609151529419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7974766126465072767686279 11962149189697609151529419)
              ·
                refine ⟨17943223784546413727294129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11962149189697609151529419 17943223784546413727294129)
                ·
                  refine ⟨13457417838409810295470597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17943223784546413727294129 13457417838409810295470597)
                  ·
                    refine ⟨2523265844701839430400737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13457417838409810295470597 2523265844701839430400737)
                    ·
                      refine ⟨1892449383526379572800553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2523265844701839430400737 1892449383526379572800553)
                      ·
                        rfl

theorem cell23_3685532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 1, 2, 4, 2].length) (baseStart_3685532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3685532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3685532 prefixEnd_3685532 := by exact prefixLift 3685532
  have htrace : WordTrace (prefixWord ++ tailWord_3685532) baseStart_3685532 baseEnd_3685532 := by
    simpa [prefixWord, tailWord_3685532, baseEnd_3685532] using wordTrace_append hprefix tailTrace_3685532
  have hstable : (prefixWord ++ tailWord_3685532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3685532).length < 2 ^ (prefixWord ++ tailWord_3685532).sum := by decide
  have hdescent : baseEnd_3685532 < baseStart_3685532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3685532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3685548 : List Nat := [2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 3]
def baseStart_3685548 : Nat := 118140960795 + 3685548 * 2 ^ 59
def prefixEnd_3685548 : Nat := 4983230072969 + 3 ^ 40 * 3685548 * 2
def baseEnd_3685548 : Nat := 1892457599216851510200479

theorem tailTrace_3685548 : CollatzResearch.WordTrace tailWord_3685548 prefixEnd_3685548 1892457599216851510200479 := by
  unfold tailWord_3685548
  simp only [CollatzResearch.WordTrace]
  refine ⟨67211489425948256165556649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89615319234597674887408865 67211489425948256165556649)
  ·
    refine ⟨50408617069461192124167487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67211489425948256165556649 50408617069461192124167487)
    ·
      refine ⟨75612925604191788186251231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50408617069461192124167487 75612925604191788186251231)
      ·
        refine ⟨113419388406287682279376847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75612925604191788186251231 113419388406287682279376847)
        ·
          refine ⟨170129082609431523419065271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113419388406287682279376847 170129082609431523419065271)
          ·
            refine ⟨255193623914147285128597907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170129082609431523419065271 255193623914147285128597907)
            ·
              refine ⟨382790435871220927692896861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255193623914147285128597907 382790435871220927692896861)
              ·
                refine ⟨143546413451707847884836323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 382790435871220927692896861 143546413451707847884836323)
                ·
                  refine ⟨215319620177561771827254485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143546413451707847884836323 215319620177561771827254485)
                  ·
                    refine ⟨5046553597911604027201277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 215319620177561771827254485 5046553597911604027201277)
                    ·
                      refine ⟨1892457599216851510200479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5046553597911604027201277 1892457599216851510200479)
                      ·
                        rfl

theorem cell23_3685548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 3].length) (baseStart_3685548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3685548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3685548 prefixEnd_3685548 := by exact prefixLift 3685548
  have htrace : WordTrace (prefixWord ++ tailWord_3685548) baseStart_3685548 baseEnd_3685548 := by
    simpa [prefixWord, tailWord_3685548, baseEnd_3685548] using wordTrace_append hprefix tailTrace_3685548
  have hstable : (prefixWord ++ tailWord_3685548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3685548).length < 2 ^ (prefixWord ++ tailWord_3685548).sum := by decide
  have hdescent : baseEnd_3685548 < baseStart_3685548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3685548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3685549 : List Nat := [1, 5, 2, 1, 3, 2, 1, 1, 2, 1, 4]
def baseStart_3685549 : Nat := 118140960795 + 3685549 * 2 ^ 59
def prefixEnd_3685549 : Nat := 4983230072969 + 3 ^ 40 * 3685549 * 2
def baseEnd_3685549 : Nat := 1892458112697506006287975

theorem tailTrace_3685549 : CollatzResearch.WordTrace tailWord_3685549 prefixEnd_3685549 1892458112697506006287975 := by
  unfold tailWord_3685549
  simp only [CollatzResearch.WordTrace]
  refine ⟨134423015324892889501899701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89615343549928593001266467 134423015324892889501899701)
  ·
    refine ⟨12602157686708708390803097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 134423015324892889501899701 12602157686708708390803097)
    ·
      refine ⟨9451618265031531293102323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12602157686708708390803097 9451618265031531293102323)
      ·
        refine ⟨14177427397547296939653485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9451618265031531293102323 14177427397547296939653485)
        ·
          refine ⟨5316535274080236352370057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14177427397547296939653485 5316535274080236352370057)
          ·
            refine ⟨3987401455560177264277543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5316535274080236352370057 3987401455560177264277543)
            ·
              refine ⟨5981102183340265896416315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3987401455560177264277543 5981102183340265896416315)
              ·
                refine ⟨8971653275010398844624473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5981102183340265896416315 8971653275010398844624473)
                ·
                  refine ⟨6728739956257799133468355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8971653275010398844624473 6728739956257799133468355)
                  ·
                    refine ⟨10093109934386698700202533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6728739956257799133468355 10093109934386698700202533)
                    ·
                      refine ⟨1892458112697506006287975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10093109934386698700202533 1892458112697506006287975)
                      ·
                        rfl

theorem cell23_3685549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_3685549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3685549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3685549 prefixEnd_3685549 := by exact prefixLift 3685549
  have htrace : WordTrace (prefixWord ++ tailWord_3685549) baseStart_3685549 baseEnd_3685549 := by
    simpa [prefixWord, tailWord_3685549, baseEnd_3685549] using wordTrace_append hprefix tailTrace_3685549
  have hstable : (prefixWord ++ tailWord_3685549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3685549).length < 2 ^ (prefixWord ++ tailWord_3685549).sum := by decide
  have hdescent : baseEnd_3685549 < baseStart_3685549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3685549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3685625 : List Nat := [1, 2, 1, 3, 1, 1, 6, 1, 1, 1, 5]
def baseStart_3685625 : Nat := 118140960795 + 3685625 * 2 ^ 59
def prefixEnd_3685625 : Nat := 4983230072969 + 3 ^ 40 * 3685625 * 2
def baseEnd_3685625 : Nat := 1892497137227247708937625

theorem tailTrace_3685625 : CollatzResearch.WordTrace tailWord_3685625 prefixEnd_3685625 1892497137227247708937625 := by
  unfold tailWord_3685625
  simp only [CollatzResearch.WordTrace]
  refine ⟨134425787272617554481666329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89617191515078369654444219 134425787272617554481666329)
  ·
    refine ⟨100819340454463165861249747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134425787272617554481666329 100819340454463165861249747)
    ·
      refine ⟨151229010681694748791874621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100819340454463165861249747 151229010681694748791874621)
      ·
        refine ⟨56710879005635530796952983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151229010681694748791874621 56710879005635530796952983)
        ·
          refine ⟨85066318508453296195429475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56710879005635530796952983 85066318508453296195429475)
          ·
            refine ⟨127599477762679944293144213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85066318508453296195429475 127599477762679944293144213)
            ·
              refine ⟨5981225520125622388741135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 127599477762679944293144213 5981225520125622388741135)
              ·
                refine ⟨8971838280188433583111703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5981225520125622388741135 8971838280188433583111703)
                ·
                  refine ⟨13457757420282650374667555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8971838280188433583111703 13457757420282650374667555)
                  ·
                    refine ⟨20186636130423975562001333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13457757420282650374667555 20186636130423975562001333)
                    ·
                      refine ⟨1892497137227247708937625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20186636130423975562001333 1892497137227247708937625)
                      ·
                        rfl

theorem cell23_3685625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 1, 1, 1, 5].length) (baseStart_3685625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3685625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3685625 prefixEnd_3685625 := by exact prefixLift 3685625
  have htrace : WordTrace (prefixWord ++ tailWord_3685625) baseStart_3685625 baseEnd_3685625 := by
    simpa [prefixWord, tailWord_3685625, baseEnd_3685625] using wordTrace_append hprefix tailTrace_3685625
  have hstable : (prefixWord ++ tailWord_3685625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3685625).length < 2 ^ (prefixWord ++ tailWord_3685625).sum := by decide
  have hdescent : baseEnd_3685625 < baseStart_3685625 := by decide
  rcases family_descends (prefixWord ++ tailWord_3685625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3685672 : List Nat := [2, 1, 5, 1, 2, 1, 1, 1, 3, 3, 3]
def baseStart_3685672 : Nat := 118140960795 + 3685672 * 2 ^ 59
def prefixEnd_3685672 : Nat := 4983230072969 + 3 ^ 40 * 3685672 * 2
def baseEnd_3685672 : Nat := 1892521270818009025049909

theorem tailTrace_3685672 : CollatzResearch.WordTrace tailWord_3685672 prefixEnd_3685672 1892521270818009025049909 := by
  unfold tailWord_3685672
  simp only [CollatzResearch.WordTrace]
  refine ⟨67213750751723640754313635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89618334335631521005751513 67213750751723640754313635)
  ·
    refine ⟨100820626127585461131470453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67213750751723640754313635 100820626127585461131470453)
    ·
      refine ⟨9451933699461136981075355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 100820626127585461131470453 9451933699461136981075355)
      ·
        refine ⟨14177900549191705471613033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9451933699461136981075355 14177900549191705471613033)
        ·
          refine ⟨10633425411893779103709775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14177900549191705471613033 10633425411893779103709775)
          ·
            refine ⟨15950138117840668655564663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10633425411893779103709775 15950138117840668655564663)
            ·
              refine ⟨23925207176761002983346995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15950138117840668655564663 23925207176761002983346995)
              ·
                refine ⟨35887810765141504475020493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23925207176761002983346995 35887810765141504475020493)
                ·
                  refine ⟨13457929036928064178132685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35887810765141504475020493 13457929036928064178132685)
                  ·
                    refine ⟨5046723388848024066799757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13457929036928064178132685 5046723388848024066799757)
                    ·
                      refine ⟨1892521270818009025049909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5046723388848024066799757 1892521270818009025049909)
                      ·
                        rfl

theorem cell23_3685672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_3685672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3685672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3685672 prefixEnd_3685672 := by exact prefixLift 3685672
  have htrace : WordTrace (prefixWord ++ tailWord_3685672) baseStart_3685672 baseEnd_3685672 := by
    simpa [prefixWord, tailWord_3685672, baseEnd_3685672] using wordTrace_append hprefix tailTrace_3685672
  have hstable : (prefixWord ++ tailWord_3685672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3685672).length < 2 ^ (prefixWord ++ tailWord_3685672).sum := by decide
  have hdescent : baseEnd_3685672 < baseStart_3685672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3685672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3685695 : List Nat := [1, 1, 2, 2, 4, 2, 1, 1, 2, 3, 4]
def baseStart_3685695 : Nat := 118140960795 + 3685695 * 2 ^ 59
def prefixEnd_3685695 : Nat := 4983230072969 + 3 ^ 40 * 3685695 * 2
def baseEnd_3685695 : Nat := 1892533080873062435062303

theorem tailTrace_3685695 : CollatzResearch.WordTrace tailWord_3685695 prefixEnd_3685695 1892533080873062435062303 := by
  unfold tailWord_3685695
  simp only [CollatzResearch.WordTrace]
  refine ⟨134428340382363956436714539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89618893588242637624476359 134428340382363956436714539)
  ·
    refine ⟨201642510573545934655071809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134428340382363956436714539 201642510573545934655071809)
    ·
      refine ⟨151231882930159450991303857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201642510573545934655071809 151231882930159450991303857)
      ·
        refine ⟨113423912197619588243477893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151231882930159450991303857 113423912197619588243477893)
        ·
          refine ⟨21266983537053672795652105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113423912197619588243477893 21266983537053672795652105)
          ·
            refine ⟨15950237652790254596739079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21266983537053672795652105 15950237652790254596739079)
            ·
              refine ⟨23925356479185381895108619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15950237652790254596739079 23925356479185381895108619)
              ·
                refine ⟨35888034718778072842662929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23925356479185381895108619 35888034718778072842662929)
                ·
                  refine ⟨26916026039083554631997197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35888034718778072842662929 26916026039083554631997197)
                  ·
                    refine ⟨10093509764656332986998949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26916026039083554631997197 10093509764656332986998949)
                    ·
                      refine ⟨1892533080873062435062303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10093509764656332986998949 1892533080873062435062303)
                      ·
                        rfl

theorem cell23_3685695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 2, 3, 4].length) (baseStart_3685695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3685695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3685695 prefixEnd_3685695 := by exact prefixLift 3685695
  have htrace : WordTrace (prefixWord ++ tailWord_3685695) baseStart_3685695 baseEnd_3685695 := by
    simpa [prefixWord, tailWord_3685695, baseEnd_3685695] using wordTrace_append hprefix tailTrace_3685695
  have hstable : (prefixWord ++ tailWord_3685695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3685695).length < 2 ^ (prefixWord ++ tailWord_3685695).sum := by decide
  have hdescent : baseEnd_3685695 < baseStart_3685695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3685695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3685715 : List Nat := [1, 1, 1, 2, 1, 1, 5, 2, 2, 4, 3]
def baseStart_3685715 : Nat := 118140960795 + 3685715 * 2 ^ 59
def prefixEnd_3685715 : Nat := 4983230072969 + 3 ^ 40 * 3685715 * 2
def baseEnd_3685715 : Nat := 1892543350486152356812211

theorem tailTrace_3685715 : CollatzResearch.WordTrace tailWord_3685715 prefixEnd_3685715 1892543350486152356812211 := by
  unfold tailWord_3685715
  simp only [CollatzResearch.WordTrace]
  refine ⟨134429069842291499852442599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89619379894860999901628399 134429069842291499852442599)
  ·
    refine ⟨201643604763437249778663899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134429069842291499852442599 201643604763437249778663899)
    ·
      refine ⟨302465407145155874667995849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201643604763437249778663899 302465407145155874667995849)
      ·
        refine ⟨226849055358866906000996887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302465407145155874667995849 226849055358866906000996887)
        ·
          refine ⟨340273583038300359001495331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226849055358866906000996887 340273583038300359001495331)
          ·
            refine ⟨510410374557450538502242997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340273583038300359001495331 510410374557450538502242997)
            ·
              refine ⟨47850972614760987984585281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 510410374557450538502242997 47850972614760987984585281)
              ·
                refine ⟨35888229461070740988438961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47850972614760987984585281 35888229461070740988438961)
                ·
                  refine ⟨26916172095803055741329221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35888229461070740988438961 26916172095803055741329221)
                  ·
                    refine ⟨5046782267963072951499229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26916172095803055741329221 5046782267963072951499229)
                    ·
                      refine ⟨1892543350486152356812211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5046782267963072951499229 1892543350486152356812211)
                      ·
                        rfl

theorem cell23_3685715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2, 4, 3].length) (baseStart_3685715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3685715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3685715 prefixEnd_3685715 := by exact prefixLift 3685715
  have htrace : WordTrace (prefixWord ++ tailWord_3685715) baseStart_3685715 baseEnd_3685715 := by
    simpa [prefixWord, tailWord_3685715, baseEnd_3685715] using wordTrace_append hprefix tailTrace_3685715
  have hstable : (prefixWord ++ tailWord_3685715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3685715).length < 2 ^ (prefixWord ++ tailWord_3685715).sum := by decide
  have hdescent : baseEnd_3685715 < baseStart_3685715 := by decide
  rcases family_descends (prefixWord ++ tailWord_3685715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3685763 : List Nat := [1, 1, 1, 3, 5, 2, 3, 1, 2, 2, 2]
def baseStart_3685763 : Nat := 118140960795 + 3685763 * 2 ^ 59
def prefixEnd_3685763 : Nat := 4983230072969 + 3 ^ 40 * 3685763 * 2
def baseEnd_3685763 : Nat := 1892567997557568169011991

theorem tailTrace_3685763 : CollatzResearch.WordTrace tailWord_3685763 prefixEnd_3685763 1892567997557568169011991 := by
  unfold tailWord_3685763
  simp only [CollatzResearch.WordTrace]
  refine ⟨134430820546117604050189943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89620547030745069366793295 134430820546117604050189943)
  ·
    refine ⟨201646230819176406075284915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134430820546117604050189943 201646230819176406075284915)
    ·
      refine ⟨302469346228764609112927373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201646230819176406075284915 302469346228764609112927373)
      ·
        refine ⟨113426004835786728417347765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 302469346228764609112927373 113426004835786728417347765)
        ·
          refine ⟨10633687953355005789126353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 113426004835786728417347765 10633687953355005789126353)
          ·
            refine ⟨7975265965016254341844765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10633687953355005789126353 7975265965016254341844765)
            ·
              refine ⟨2990724736881095378191787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7975265965016254341844765 2990724736881095378191787)
              ·
                refine ⟨4486087105321643067287681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2990724736881095378191787 4486087105321643067287681)
                ·
                  refine ⟨3364565328991232300465761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4486087105321643067287681 3364565328991232300465761)
                  ·
                    refine ⟨2523423996743424225349321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3364565328991232300465761 2523423996743424225349321)
                    ·
                      refine ⟨1892567997557568169011991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2523423996743424225349321 1892567997557568169011991)
                      ·
                        rfl

theorem cell23_3685763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 3, 1, 2, 2, 2].length) (baseStart_3685763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3685763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3685763 prefixEnd_3685763 := by exact prefixLift 3685763
  have htrace : WordTrace (prefixWord ++ tailWord_3685763) baseStart_3685763 baseEnd_3685763 := by
    simpa [prefixWord, tailWord_3685763, baseEnd_3685763] using wordTrace_append hprefix tailTrace_3685763
  have hstable : (prefixWord ++ tailWord_3685763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3685763).length < 2 ^ (prefixWord ++ tailWord_3685763).sum := by decide
  have hdescent : baseEnd_3685763 < baseStart_3685763 := by decide
  rcases family_descends (prefixWord ++ tailWord_3685763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3685765 : List Nat := [1, 3, 1, 1, 3, 1, 3, 2, 1, 7]
def baseStart_3685765 : Nat := 118140960795 + 3685765 * 2 ^ 59
def prefixEnd_3685765 : Nat := 4983230072969 + 3 ^ 40 * 3685765 * 2
def baseEnd_3685765 : Nat := 630856341506292387062327

theorem tailTrace_3685765 : CollatzResearch.WordTrace tailWord_3685765 prefixEnd_3685765 630856341506292387062327 := by
  unfold tailWord_3685765
  simp only [CollatzResearch.WordTrace]
  refine ⟨134430893492110358391762749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89620595661406905594508499 134430893492110358391762749)
  ·
    refine ⟨50411585059541384396911031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134430893492110358391762749 50411585059541384396911031)
    ·
      refine ⟨75617377589312076595366547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50411585059541384396911031 75617377589312076595366547)
      ·
        refine ⟨113426066383968114893049821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75617377589312076595366547 113426066383968114893049821)
        ·
          refine ⟨42534774893988043084893683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113426066383968114893049821 42534774893988043084893683)
          ·
            refine ⟨63802162340982064627340525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42534774893988043084893683 63802162340982064627340525)
            ·
              refine ⟨23925810877868274235252697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63802162340982064627340525 23925810877868274235252697)
              ·
                refine ⟨17944358158401205676439523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23925810877868274235252697 17944358158401205676439523)
                ·
                  refine ⟨26916537237601808514659285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17944358158401205676439523 26916537237601808514659285)
                  ·
                    refine ⟨630856341506292387062327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26916537237601808514659285 630856341506292387062327)
                    ·
                      rfl

theorem cell23_3685765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2, 1, 7].length) (baseStart_3685765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3685765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3685765 prefixEnd_3685765 := by exact prefixLift 3685765
  have htrace : WordTrace (prefixWord ++ tailWord_3685765) baseStart_3685765 baseEnd_3685765 := by
    simpa [prefixWord, tailWord_3685765, baseEnd_3685765] using wordTrace_append hprefix tailTrace_3685765
  have hstable : (prefixWord ++ tailWord_3685765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3685765).length < 2 ^ (prefixWord ++ tailWord_3685765).sum := by decide
  have hdescent : baseEnd_3685765 < baseStart_3685765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3685765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3685859 : List Nat := [1, 1, 1, 6, 2, 2, 2, 2, 6]
def baseStart_3685859 : Nat := 118140960795 + 3685859 * 2 ^ 59
def prefixEnd_3685859 : Nat := 4983230072969 + 3 ^ 40 * 3685859 * 2
def baseEnd_3685859 : Nat := 210290810188933310379061

theorem tailTrace_3685859 : CollatzResearch.WordTrace tailWord_3685859 prefixEnd_3685859 210290810188933310379061 := by
  unfold tailWord_3685859
  simp only [CollatzResearch.WordTrace]
  refine ⟨134434321953769812445684631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89622881302513208297123087 134434321953769812445684631)
  ·
    refine ⟨201651482930654718668526947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134434321953769812445684631 201651482930654718668526947)
    ·
      refine ⟨302477224395982078002790421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201651482930654718668526947 302477224395982078002790421)
      ·
        refine ⟨14178619893561659906380801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 302477224395982078002790421 14178619893561659906380801)
        ·
          refine ⟨10633964920171244929785601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14178619893561659906380801 10633964920171244929785601)
          ·
            refine ⟨7975473690128433697339201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10633964920171244929785601 7975473690128433697339201)
            ·
              refine ⟨5981605267596325273004401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7975473690128433697339201 5981605267596325273004401)
              ·
                refine ⟨4486203950697243954753301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5981605267596325273004401 4486203950697243954753301)
                ·
                  refine ⟨210290810188933310379061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4486203950697243954753301 210290810188933310379061)
                  ·
                    rfl

theorem cell23_3685859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 2, 6].length) (baseStart_3685859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3685859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3685859 prefixEnd_3685859 := by exact prefixLift 3685859
  have htrace : WordTrace (prefixWord ++ tailWord_3685859) baseStart_3685859 baseEnd_3685859 := by
    simpa [prefixWord, tailWord_3685859, baseEnd_3685859] using wordTrace_append hprefix tailTrace_3685859
  have hstable : (prefixWord ++ tailWord_3685859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3685859).length < 2 ^ (prefixWord ++ tailWord_3685859).sum := by decide
  have hdescent : baseEnd_3685859 < baseStart_3685859 := by decide
  rcases family_descends (prefixWord ++ tailWord_3685859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3685863 : List Nat := [1, 1, 5, 2, 1, 2, 4, 2, 1, 4]
def baseStart_3685863 : Nat := 118140960795 + 3685863 * 2 ^ 59
def prefixEnd_3685863 : Nat := 4983230072969 + 3 ^ 40 * 3685863 * 2
def baseEnd_3685863 : Nat := 630873115207672592587177

theorem tailTrace_3685863 : CollatzResearch.WordTrace tailWord_3685863 prefixEnd_3685863 630873115207672592587177 := by
  unfold tailWord_3685863
  simp only [CollatzResearch.WordTrace]
  refine ⟨134434467845755321128830243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89622978563836880752553495 134434467845755321128830243)
  ·
    refine ⟨201651701768632981693245365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134434467845755321128830243 201651701768632981693245365)
    ·
      refine ⟨18904847040809342033741753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 201651701768632981693245365 18904847040809342033741753)
      ·
        refine ⟨14178635280607006525306315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18904847040809342033741753 14178635280607006525306315)
        ·
          refine ⟨21267952920910509787959473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14178635280607006525306315 21267952920910509787959473)
          ·
            refine ⟨15950964690682882340969605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21267952920910509787959473 15950964690682882340969605)
            ·
              refine ⟨2990805879503040438931801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15950964690682882340969605 2990805879503040438931801)
              ·
                refine ⟨2243104409627280329198851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2990805879503040438931801 2243104409627280329198851)
                ·
                  refine ⟨3364656614440920493798277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2243104409627280329198851 3364656614440920493798277)
                  ·
                    refine ⟨630873115207672592587177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3364656614440920493798277 630873115207672592587177)
                    ·
                      rfl

theorem cell23_3685863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 4, 2, 1, 4].length) (baseStart_3685863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3685863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3685863 prefixEnd_3685863 := by exact prefixLift 3685863
  have htrace : WordTrace (prefixWord ++ tailWord_3685863) baseStart_3685863 baseEnd_3685863 := by
    simpa [prefixWord, tailWord_3685863, baseEnd_3685863] using wordTrace_append hprefix tailTrace_3685863
  have hstable : (prefixWord ++ tailWord_3685863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3685863).length < 2 ^ (prefixWord ++ tailWord_3685863).sum := by decide
  have hdescent : baseEnd_3685863 < baseStart_3685863 := by decide
  rcases family_descends (prefixWord ++ tailWord_3685863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3685872 : List Nat := [2, 1, 1, 1, 3, 4, 1, 2, 3, 5]
def baseStart_3685872 : Nat := 118140960795 + 3685872 * 2 ^ 59
def prefixEnd_3685872 : Nat := 4983230072969 + 3 ^ 40 * 3685872 * 2
def baseEnd_3685872 : Nat := 630874655649636080849663

theorem tailTrace_3685872 : CollatzResearch.WordTrace tailWord_3685872 prefixEnd_3685872 630874655649636080849663 := by
  unfold tailWord_3685872
  simp only [CollatzResearch.WordTrace]
  refine ⟨67217398051361357832953935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89623197401815143777271913 67217398051361357832953935)
  ·
    refine ⟨100826097077042036749430903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67217398051361357832953935 100826097077042036749430903)
    ·
      refine ⟨151239145615563055124146355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100826097077042036749430903 151239145615563055124146355)
      ·
        refine ⟨226858718423344582686219533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151239145615563055124146355 226858718423344582686219533)
        ·
          refine ⟨85072019408754218507332325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226858718423344582686219533 85072019408754218507332325)
          ·
            refine ⟨15951003639141415970124811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85072019408754218507332325 15951003639141415970124811)
            ·
              refine ⟨23926505458712123955187217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15951003639141415970124811 23926505458712123955187217)
              ·
                refine ⟨17944879094034092966390413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23926505458712123955187217 17944879094034092966390413)
                ·
                  refine ⟨6729329660262784862396405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17944879094034092966390413 6729329660262784862396405)
                  ·
                    refine ⟨630874655649636080849663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6729329660262784862396405 630874655649636080849663)
                    ·
                      rfl

theorem cell23_3685872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 2, 3, 5].length) (baseStart_3685872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3685872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3685872 prefixEnd_3685872 := by exact prefixLift 3685872
  have htrace : WordTrace (prefixWord ++ tailWord_3685872) baseStart_3685872 baseEnd_3685872 := by
    simpa [prefixWord, tailWord_3685872, baseEnd_3685872] using wordTrace_append hprefix tailTrace_3685872
  have hstable : (prefixWord ++ tailWord_3685872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3685872).length < 2 ^ (prefixWord ++ tailWord_3685872).sum := by decide
  have hdescent : baseEnd_3685872 < baseStart_3685872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3685872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3685896 : List Nat := [2, 1, 3, 2, 1, 1, 5, 1, 2, 3, 2]
def baseStart_3685896 : Nat := 118140960795 + 3685896 * 2 ^ 59
def prefixEnd_3685896 : Nat := 4983230072969 + 3 ^ 40 * 3685896 * 2
def baseEnd_3685896 : Nat := 1892636290484616148648879

theorem tailTrace_3685896 : CollatzResearch.WordTrace tailWord_3685896 prefixEnd_3685896 1892636290484616148648879 := by
  unfold tailWord_3685896
  simp only [CollatzResearch.WordTrace]
  refine ⟨67217835727317883882390771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89623780969757178509854361 67217835727317883882390771)
  ·
    refine ⟨100826753590976825823586157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67217835727317883882390771 100826753590976825823586157)
    ·
      refine ⟨37810032596616309683844809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100826753590976825823586157 37810032596616309683844809)
      ·
        refine ⟨28357524447462232262883607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37810032596616309683844809 28357524447462232262883607)
        ·
          refine ⟨42536286671193348394325411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28357524447462232262883607 42536286671193348394325411)
          ·
            refine ⟨63804430006790022591488117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42536286671193348394325411 63804430006790022591488117)
            ·
              refine ⟨5981665313136564617952011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63804430006790022591488117 5981665313136564617952011)
              ·
                refine ⟨8972497969704846926928017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5981665313136564617952011 8972497969704846926928017)
                ·
                  refine ⟨6729373477278635195196013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8972497969704846926928017 6729373477278635195196013)
                  ·
                    refine ⟨2523515053979488198198505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6729373477278635195196013 2523515053979488198198505)
                    ·
                      refine ⟨1892636290484616148648879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2523515053979488198198505 1892636290484616148648879)
                      ·
                        rfl

theorem cell23_3685896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 1, 2, 3, 2].length) (baseStart_3685896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3685896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3685896 prefixEnd_3685896 := by exact prefixLift 3685896
  have htrace : WordTrace (prefixWord ++ tailWord_3685896) baseStart_3685896 baseEnd_3685896 := by
    simpa [prefixWord, tailWord_3685896, baseEnd_3685896] using wordTrace_append hprefix tailTrace_3685896
  have hstable : (prefixWord ++ tailWord_3685896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3685896).length < 2 ^ (prefixWord ++ tailWord_3685896).sum := by decide
  have hdescent : baseEnd_3685896 < baseStart_3685896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3685896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3685939 : List Nat := [1, 1, 1, 2, 4, 3, 3, 1, 1, 2, 4]
def baseStart_3685939 : Nat := 118140960795 + 3685939 * 2 ^ 59
def prefixEnd_3685939 : Nat := 4983230072969 + 3 ^ 40 * 3685939 * 2
def baseEnd_3685939 : Nat := 1892658370152759480411181

theorem tailTrace_3685939 : CollatzResearch.WordTrace tailWord_3685939 prefixEnd_3685939 1892658370152759480411181 := by
  unfold tailWord_3685939
  simp only [CollatzResearch.WordTrace]
  refine ⟨134437239793479986108596871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89624826528986657405731247 134437239793479986108596871)
  ·
    refine ⟨201655859690219979162895307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134437239793479986108596871 201655859690219979162895307)
    ·
      refine ⟨302483789535329968744342961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201655859690219979162895307 302483789535329968744342961)
      ·
        refine ⟨226862842151497476558257221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302483789535329968744342961 226862842151497476558257221)
        ·
          refine ⟨42536782903405776854673229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 226862842151497476558257221 42536782903405776854673229)
          ·
            refine ⟨15951293588777166320502461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42536782903405776854673229 15951293588777166320502461)
            ·
              refine ⟨5981735095791437370188423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15951293588777166320502461 5981735095791437370188423)
              ·
                refine ⟨8972602643687156055282635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5981735095791437370188423 8972602643687156055282635)
                ·
                  refine ⟨13458903965530734082923953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8972602643687156055282635 13458903965530734082923953)
                  ·
                    refine ⟨10094177974148050562192965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13458903965530734082923953 10094177974148050562192965)
                    ·
                      refine ⟨1892658370152759480411181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10094177974148050562192965 1892658370152759480411181)
                      ·
                        rfl

theorem cell23_3685939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 1, 1, 2, 4].length) (baseStart_3685939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3685939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3685939 prefixEnd_3685939 := by exact prefixLift 3685939
  have htrace : WordTrace (prefixWord ++ tailWord_3685939) baseStart_3685939 baseEnd_3685939 := by
    simpa [prefixWord, tailWord_3685939, baseEnd_3685939] using wordTrace_append hprefix tailTrace_3685939
  have hstable : (prefixWord ++ tailWord_3685939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3685939).length < 2 ^ (prefixWord ++ tailWord_3685939).sum := by decide
  have hdescent : baseEnd_3685939 < baseStart_3685939 := by decide
  rcases family_descends (prefixWord ++ tailWord_3685939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3685946 : List Nat := [3, 1, 1, 1, 3, 2, 4, 2, 1, 2, 3]
def baseStart_3685946 : Nat := 118140960795 + 3685946 * 2 ^ 59
def prefixEnd_3685946 : Nat := 4983230072969 + 3 ^ 40 * 3685946 * 2
def baseEnd_3685946 : Nat := 1892661964517340953023649

theorem tailTrace_3685946 : CollatzResearch.WordTrace tailWord_3685946 prefixEnd_3685946 1892661964517340953023649 := by
  unfold tailWord_3685946
  simp only [CollatzResearch.WordTrace]
  refine ⟨33609373776113656576025423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89624996736303084202734461 33609373776113656576025423)
  ·
    refine ⟨50414060664170484864038135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33609373776113656576025423 50414060664170484864038135)
    ·
      refine ⟨75621090996255727296057203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50414060664170484864038135 75621090996255727296057203)
      ·
        refine ⟨113431636494383590944085805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75621090996255727296057203 113431636494383590944085805)
        ·
          refine ⟨42536863685393846604032177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113431636494383590944085805 42536863685393846604032177)
          ·
            refine ⟨31902647764045384953024133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42536863685393846604032177 31902647764045384953024133)
            ·
              refine ⟨5981746455758509678692025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31902647764045384953024133 5981746455758509678692025)
              ·
                refine ⟨4486309841818882259019019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5981746455758509678692025 4486309841818882259019019)
                ·
                  refine ⟨6729464762728323388528529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4486309841818882259019019 6729464762728323388528529)
                  ·
                    refine ⟨5047098572046242541396397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6729464762728323388528529 5047098572046242541396397)
                    ·
                      refine ⟨1892661964517340953023649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5047098572046242541396397 1892661964517340953023649)
                      ·
                        rfl

theorem cell23_3685946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 2, 1, 2, 3].length) (baseStart_3685946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3685946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3685946 prefixEnd_3685946 := by exact prefixLift 3685946
  have htrace : WordTrace (prefixWord ++ tailWord_3685946) baseStart_3685946 baseEnd_3685946 := by
    simpa [prefixWord, tailWord_3685946, baseEnd_3685946] using wordTrace_append hprefix tailTrace_3685946
  have hstable : (prefixWord ++ tailWord_3685946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3685946).length < 2 ^ (prefixWord ++ tailWord_3685946).sum := by decide
  have hdescent : baseEnd_3685946 < baseStart_3685946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3685946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3685949 : List Nat := [1, 4, 1, 3, 3, 1, 1, 9]
def baseStart_3685949 : Nat := 118140960795 + 3685949 * 2 ^ 59
def prefixEnd_3685949 : Nat := 4983230072969 + 3 ^ 40 * 3685949 * 2
def baseEnd_3685949 : Nat := 70098648331826090418005

theorem tailTrace_3685949 : CollatzResearch.WordTrace tailWord_3685949 prefixEnd_3685949 70098648331826090418005 := by
  unfold tailWord_3685949
  simp only [CollatzResearch.WordTrace]
  refine ⟨134437604523443757816460901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89625069682295838544307267 134437604523443757816460901)
  ·
    refine ⟨25207050848145704590586419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134437604523443757816460901 25207050848145704590586419)
    ·
      refine ⟨37810576272218556885879629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25207050848145704590586419 37810576272218556885879629)
      ·
        refine ⟨14178966102081958832204861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37810576272218556885879629 14178966102081958832204861)
        ·
          refine ⟨5317112288280734562076823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14178966102081958832204861 5317112288280734562076823)
          ·
            refine ⟨7975668432421101843115235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5317112288280734562076823 7975668432421101843115235)
            ·
              refine ⟨11963502648631652764672853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7975668432421101843115235 11963502648631652764672853)
              ·
                refine ⟨70098648331826090418005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11963502648631652764672853 70098648331826090418005)
                ·
                  rfl

theorem cell23_3685949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 9].length) (baseStart_3685949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3685949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3685949 prefixEnd_3685949 := by exact prefixLift 3685949
  have htrace : WordTrace (prefixWord ++ tailWord_3685949) baseStart_3685949 baseEnd_3685949 := by
    simpa [prefixWord, tailWord_3685949, baseEnd_3685949] using wordTrace_append hprefix tailTrace_3685949
  have hstable : (prefixWord ++ tailWord_3685949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3685949).length < 2 ^ (prefixWord ++ tailWord_3685949).sum := by decide
  have hdescent : baseEnd_3685949 < baseStart_3685949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3685949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3685976 : List Nat := [2, 1, 2, 2, 1, 2, 1, 6, 2, 1, 3]
def baseStart_3685976 : Nat := 118140960795 + 3685976 * 2 ^ 59
def prefixEnd_3685976 : Nat := 4983230072969 + 3 ^ 40 * 3685976 * 2
def baseEnd_3685976 : Nat := 1892677368936975835648511

theorem tailTrace_3685976 : CollatzResearch.WordTrace tailWord_3685976 prefixEnd_3685976 1892677368936975835648511 := by
  unfold tailWord_3685976
  simp only [CollatzResearch.WordTrace]
  refine ⟨67219294647172970713846891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89625726196230627618462521 67219294647172970713846891)
  ·
    refine ⟨100828941970759456070770337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67219294647172970713846891 100828941970759456070770337)
    ·
      refine ⟨75621706478069592053077753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100828941970759456070770337 75621706478069592053077753)
      ·
        refine ⟨56716279858552194039808315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75621706478069592053077753 56716279858552194039808315)
        ·
          refine ⟨85074419787828291059712473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56716279858552194039808315 85074419787828291059712473)
          ·
            refine ⟨63805814840871218294784355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85074419787828291059712473 63805814840871218294784355)
            ·
              refine ⟨95708722261306827442176533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63805814840871218294784355 95708722261306827442176533)
              ·
                refine ⟨4486346355998757536352025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 95708722261306827442176533 4486346355998757536352025)
                ·
                  refine ⟨3364759766999068152264019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4486346355998757536352025 3364759766999068152264019)
                  ·
                    refine ⟨5047139650498602228396029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3364759766999068152264019 5047139650498602228396029)
                    ·
                      refine ⟨1892677368936975835648511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5047139650498602228396029 1892677368936975835648511)
                      ·
                        rfl

theorem cell23_3685976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 6, 2, 1, 3].length) (baseStart_3685976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3685976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3685976 prefixEnd_3685976 := by exact prefixLift 3685976
  have htrace : WordTrace (prefixWord ++ tailWord_3685976) baseStart_3685976 baseEnd_3685976 := by
    simpa [prefixWord, tailWord_3685976, baseEnd_3685976] using wordTrace_append hprefix tailTrace_3685976
  have hstable : (prefixWord ++ tailWord_3685976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3685976).length < 2 ^ (prefixWord ++ tailWord_3685976).sum := by decide
  have hdescent : baseEnd_3685976 < baseStart_3685976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3685976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3685993 : List Nat := [1, 2, 1, 1, 1, 4, 6, 1, 2, 1, 3]
def baseStart_3685993 : Nat := 118140960795 + 3685993 * 2 ^ 59
def prefixEnd_3685993 : Nat := 4983230072969 + 3 ^ 40 * 3685993 * 2
def baseEnd_3685993 : Nat := 1892686098108102269135933

theorem tailTrace_3685993 : CollatzResearch.WordTrace tailWord_3685993 prefixEnd_3685993 1892686098108102269135933 := by
  unfold tailWord_3685993
  simp only [CollatzResearch.WordTrace]
  refine ⟨134439209335284353331062633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89626139556856235554041755 134439209335284353331062633)
  ·
    refine ⟨100829407001463264998296975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134439209335284353331062633 100829407001463264998296975)
    ·
      refine ⟨151244110502194897497445463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100829407001463264998296975 151244110502194897497445463)
      ·
        refine ⟨226866165753292346246168195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151244110502194897497445463 226866165753292346246168195)
        ·
          refine ⟨340299248629938519369252293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226866165753292346246168195 340299248629938519369252293)
          ·
            refine ⟨63806109118113472381734805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 340299248629938519369252293 63806109118113472381734805)
            ·
              refine ⟨2990911364911569017893819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 63806109118113472381734805 2990911364911569017893819)
              ·
                refine ⟨4486367047367353526840729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2990911364911569017893819 4486367047367353526840729)
                ·
                  refine ⟨3364775285525515145130547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4486367047367353526840729 3364775285525515145130547)
                  ·
                    refine ⟨5047162928288272717695821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3364775285525515145130547 5047162928288272717695821)
                    ·
                      refine ⟨1892686098108102269135933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5047162928288272717695821 1892686098108102269135933)
                      ·
                        rfl

theorem cell23_3685993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 6, 1, 2, 1, 3].length) (baseStart_3685993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3685993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3685993 prefixEnd_3685993 := by exact prefixLift 3685993
  have htrace : WordTrace (prefixWord ++ tailWord_3685993) baseStart_3685993 baseEnd_3685993 := by
    simpa [prefixWord, tailWord_3685993, baseEnd_3685993] using wordTrace_append hprefix tailTrace_3685993
  have hstable : (prefixWord ++ tailWord_3685993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3685993).length < 2 ^ (prefixWord ++ tailWord_3685993).sum := by decide
  have hdescent : baseEnd_3685993 < baseStart_3685993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3685993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3686016 : List Nat := [2, 1, 1, 2, 1, 4, 3, 2, 1, 4, 2]
def baseStart_3686016 : Nat := 118140960795 + 3686016 * 2 ^ 59
def prefixEnd_3686016 : Nat := 4983230072969 + 3 ^ 40 * 3686016 * 2
def baseEnd_3686016 : Nat := 1892697908163155679148327

theorem tailTrace_3686016 : CollatzResearch.WordTrace tailWord_3686016 prefixEnd_3686016 1892697908163155679148327 := by
  unfold tailWord_3686016
  simp only [CollatzResearch.WordTrace]
  refine ⟨67220024107100514129574951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89626698809467352172766601 67220024107100514129574951)
  ·
    refine ⟨100830036160650771194362427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67220024107100514129574951 100830036160650771194362427)
    ·
      refine ⟨151245054240976156791543641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100830036160650771194362427 151245054240976156791543641)
      ·
        refine ⟨113433790680732117593657731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151245054240976156791543641 113433790680732117593657731)
        ·
          refine ⟨170150686021098176390486597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113433790680732117593657731 170150686021098176390486597)
          ·
            refine ⟨31903253628955908073216237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 170150686021098176390486597 31903253628955908073216237)
            ·
              refine ⟨11963720110858465527456089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31903253628955908073216237 11963720110858465527456089)
              ·
                refine ⟨8972790083143849145592067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11963720110858465527456089 8972790083143849145592067)
                ·
                  refine ⟨13459185124715773718388101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8972790083143849145592067 13459185124715773718388101)
                  ·
                    refine ⟨2523597210884207572197769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13459185124715773718388101 2523597210884207572197769)
                    ·
                      refine ⟨1892697908163155679148327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2523597210884207572197769 1892697908163155679148327)
                      ·
                        rfl

theorem cell23_3686016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 2, 1, 4, 2].length) (baseStart_3686016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3686016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3686016 prefixEnd_3686016 := by exact prefixLift 3686016
  have htrace : WordTrace (prefixWord ++ tailWord_3686016) baseStart_3686016 baseEnd_3686016 := by
    simpa [prefixWord, tailWord_3686016, baseEnd_3686016] using wordTrace_append hprefix tailTrace_3686016
  have hstable : (prefixWord ++ tailWord_3686016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3686016).length < 2 ^ (prefixWord ++ tailWord_3686016).sum := by decide
  have hdescent : baseEnd_3686016 < baseStart_3686016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3686016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3686032 : List Nat := [2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 7]
def baseStart_3686032 : Nat := 118140960795 + 3686032 * 2 ^ 59
def prefixEnd_3686032 : Nat := 4983230072969 + 3 ^ 40 * 3686032 * 2
def baseEnd_3686032 : Nat := 1892706123853627616548253

theorem tailTrace_3686032 : CollatzResearch.WordTrace tailWord_3686032 prefixEnd_3686032 1892706123853627616548253 := by
  unfold tailWord_3686032
  simp only [CollatzResearch.WordTrace]
  refine ⟨67220315891071531495866175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89627087854762041994488233 67220315891071531495866175)
  ·
    refine ⟨100830473836607297243799263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67220315891071531495866175 100830473836607297243799263)
    ·
      refine ⟨151245710754910945865698895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100830473836607297243799263 151245710754910945865698895)
      ·
        refine ⟨226868566132366418798548343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151245710754910945865698895 226868566132366418798548343)
        ·
          refine ⟨340302849198549628197822515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226868566132366418798548343 340302849198549628197822515)
          ·
            refine ⟨510454273797824442296733773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340302849198549628197822515 510454273797824442296733773)
            ·
              refine ⟨191420352674184165861275165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 510454273797824442296733773 191420352674184165861275165)
              ·
                refine ⟨71782632252819062197978187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 191420352674184165861275165 71782632252819062197978187)
                ·
                  refine ⟨107673948379228593296967281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71782632252819062197978187 107673948379228593296967281)
                  ·
                    refine ⟨80755461284421444972725461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 107673948379228593296967281 80755461284421444972725461)
                    ·
                      refine ⟨1892706123853627616548253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 80755461284421444972725461 1892706123853627616548253)
                      ·
                        rfl

theorem cell23_3686032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 7].length) (baseStart_3686032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3686032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3686032 prefixEnd_3686032 := by exact prefixLift 3686032
  have htrace : WordTrace (prefixWord ++ tailWord_3686032) baseStart_3686032 baseEnd_3686032 := by
    simpa [prefixWord, tailWord_3686032, baseEnd_3686032] using wordTrace_append hprefix tailTrace_3686032
  have hstable : (prefixWord ++ tailWord_3686032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3686032).length < 2 ^ (prefixWord ++ tailWord_3686032).sum := by decide
  have hdescent : baseEnd_3686032 < baseStart_3686032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3686032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3686046 : List Nat := [4, 3, 1, 1, 1, 2, 1, 1, 1, 4, 4]
def baseStart_3686046 : Nat := 118140960795 + 3686046 * 2 ^ 59
def prefixEnd_3686046 : Nat := 4983230072969 + 3 ^ 40 * 3686046 * 2
def baseEnd_3686046 : Nat := 1892713312582790561773189

theorem tailTrace_3686046 : CollatzResearch.WordTrace tailWord_3686046 prefixEnd_3686046 1892713312582790561773189 := by
  unfold tailWord_3686046
  simp only [CollatzResearch.WordTrace]
  refine ⟨16805142800511542922842749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89627428269394895588494661 16805142800511542922842749)
  ·
    refine ⟨6301928550191828596066031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16805142800511542922842749 6301928550191828596066031)
    ·
      refine ⟨9452892825287742894099047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6301928550191828596066031 9452892825287742894099047)
      ·
        refine ⟨14179339237931614341148571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9452892825287742894099047 14179339237931614341148571)
        ·
          refine ⟨21269008856897421511722857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14179339237931614341148571 21269008856897421511722857)
          ·
            refine ⟨15951756642673066133792143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21269008856897421511722857 15951756642673066133792143)
            ·
              refine ⟨23927634964009599200688215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15951756642673066133792143 23927634964009599200688215)
              ·
                refine ⟨35891452446014398801032323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23927634964009599200688215 35891452446014398801032323)
                ·
                  refine ⟨53837178669021598201548485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35891452446014398801032323 53837178669021598201548485)
                  ·
                    refine ⟨10094471000441549662790341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53837178669021598201548485 10094471000441549662790341)
                    ·
                      refine ⟨1892713312582790561773189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10094471000441549662790341 1892713312582790561773189)
                      ·
                        rfl

theorem cell23_3686046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_3686046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3686046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3686046 prefixEnd_3686046 := by exact prefixLift 3686046
  have htrace : WordTrace (prefixWord ++ tailWord_3686046) baseStart_3686046 baseEnd_3686046 := by
    simpa [prefixWord, tailWord_3686046, baseEnd_3686046] using wordTrace_append hprefix tailTrace_3686046
  have hstable : (prefixWord ++ tailWord_3686046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3686046).length < 2 ^ (prefixWord ++ tailWord_3686046).sum := by decide
  have hdescent : baseEnd_3686046 < baseStart_3686046 := by decide
  rcases family_descends (prefixWord ++ tailWord_3686046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3686116 : List Nat := [2, 3, 1, 1, 1, 3, 1, 4, 3, 4]
def baseStart_3686116 : Nat := 118140960795 + 3686116 * 2 ^ 59
def prefixEnd_3686116 : Nat := 4983230072969 + 3 ^ 40 * 3686116 * 2
def baseEnd_3686116 : Nat := 630916418742868429299289

theorem tailTrace_3686116 : CollatzResearch.WordTrace tailWord_3686116 prefixEnd_3686116 630916418742868429299289 := by
  unfold tailWord_3686116
  simp only [CollatzResearch.WordTrace]
  refine ⟨67221847756919372668895101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89629130342559163558526801 67221847756919372668895101)
  ·
    refine ⟨25208192908844764750835663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67221847756919372668895101 25208192908844764750835663)
    ·
      refine ⟨37812289363267147126253495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25208192908844764750835663 37812289363267147126253495)
      ·
        refine ⟨56718434044900720689380243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37812289363267147126253495 56718434044900720689380243)
        ·
          refine ⟨85077651067351081034070365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56718434044900720689380243 85077651067351081034070365)
          ·
            refine ⟨31904119150256655387776387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85077651067351081034070365 31904119150256655387776387)
            ·
              refine ⟨47856178725384983081664581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31904119150256655387776387 47856178725384983081664581)
              ·
                refine ⟨8973033511009684327812109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47856178725384983081664581 8973033511009684327812109)
                ·
                  refine ⟨3364887566628631622929541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8973033511009684327812109 3364887566628631622929541)
                  ·
                    refine ⟨630916418742868429299289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3364887566628631622929541 630916418742868429299289)
                    ·
                      rfl

theorem cell23_3686116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 4, 3, 4].length) (baseStart_3686116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3686116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3686116 prefixEnd_3686116 := by exact prefixLift 3686116
  have htrace : WordTrace (prefixWord ++ tailWord_3686116) baseStart_3686116 baseEnd_3686116 := by
    simpa [prefixWord, tailWord_3686116, baseEnd_3686116] using wordTrace_append hprefix tailTrace_3686116
  have hstable : (prefixWord ++ tailWord_3686116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3686116).length < 2 ^ (prefixWord ++ tailWord_3686116).sum := by decide
  have hdescent : baseEnd_3686116 < baseStart_3686116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3686116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3686126 : List Nat := [4, 1, 2, 1, 1, 2, 1, 3, 1, 4, 3]
def baseStart_3686126 : Nat := 118140960795 + 3686126 * 2 ^ 59
def prefixEnd_3686126 : Nat := 4983230072969 + 3 ^ 40 * 3686126 * 2
def baseEnd_3686126 : Nat := 1892754391035150248772821

theorem tailTrace_3686126 : CollatzResearch.WordTrace tailWord_3686126 prefixEnd_3686126 1892754391035150248772821 := by
  unfold tailWord_3686126
  simp only [CollatzResearch.WordTrace]
  refine ⟨16805507530475314630706779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89629373495868344697102821 16805507530475314630706779)
  ·
    refine ⟨25208261295712971946060169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16805507530475314630706779 25208261295712971946060169)
    ·
      refine ⟨18906195971784728959545127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25208261295712971946060169 18906195971784728959545127)
      ·
        refine ⟨28359293957677093439317691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18906195971784728959545127 28359293957677093439317691)
        ·
          refine ⟨42538940936515640158976537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28359293957677093439317691 42538940936515640158976537)
          ·
            refine ⟨31904205702386730119232403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42538940936515640158976537 31904205702386730119232403)
            ·
              refine ⟨47856308553580095178848605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31904205702386730119232403 47856308553580095178848605)
              ·
                refine ⟨17946115707592535692068227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47856308553580095178848605 17946115707592535692068227)
                ·
                  refine ⟨26919173561388803538102341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17946115707592535692068227 26919173561388803538102341)
                  ·
                    refine ⟨5047345042760400663394189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26919173561388803538102341 5047345042760400663394189)
                    ·
                      refine ⟨1892754391035150248772821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5047345042760400663394189 1892754391035150248772821)
                      ·
                        rfl

theorem cell23_3686126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 3, 1, 4, 3].length) (baseStart_3686126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3686126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3686126 prefixEnd_3686126 := by exact prefixLift 3686126
  have htrace : WordTrace (prefixWord ++ tailWord_3686126) baseStart_3686126 baseEnd_3686126 := by
    simpa [prefixWord, tailWord_3686126, baseEnd_3686126] using wordTrace_append hprefix tailTrace_3686126
  have hstable : (prefixWord ++ tailWord_3686126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3686126).length < 2 ^ (prefixWord ++ tailWord_3686126).sum := by decide
  have hdescent : baseEnd_3686126 < baseStart_3686126 := by decide
  rcases family_descends (prefixWord ++ tailWord_3686126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3686129 : List Nat := [1, 2, 2, 2, 2, 3, 1, 2, 8]
def baseStart_3686129 : Nat := 118140960795 + 3686129 * 2 ^ 59
def prefixEnd_3686129 : Nat := 4983230072969 + 3 ^ 40 * 3686129 * 2
def baseEnd_3686129 : Nat := 210306214608568193003923

theorem tailTrace_3686129 : CollatzResearch.WordTrace tailWord_3686129 prefixEnd_3686129 210306214608568193003923 := by
  unfold tailWord_3686129
  simp only [CollatzResearch.WordTrace]
  refine ⟨134444169662791648558013441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89629446441861099038675627 134444169662791648558013441)
  ·
    refine ⟨100833127247093736418510081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134444169662791648558013441 100833127247093736418510081)
    ·
      refine ⟨75624845435320302313882561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100833127247093736418510081 75624845435320302313882561)
      ·
        refine ⟨56718634076490226735411921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75624845435320302313882561 56718634076490226735411921)
        ·
          refine ⟨42538975557367670051558941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56718634076490226735411921 42538975557367670051558941)
          ·
            refine ⟨15952115834012876269334603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42538975557367670051558941 15952115834012876269334603)
            ·
              refine ⟨23928173751019314404001905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15952115834012876269334603 23928173751019314404001905)
              ·
                refine ⟨17946130313264485803001429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23928173751019314404001905 17946130313264485803001429)
                ·
                  refine ⟨210306214608568193003923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17946130313264485803001429 210306214608568193003923)
                  ·
                    rfl

theorem cell23_3686129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 2, 8].length) (baseStart_3686129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3686129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3686129 prefixEnd_3686129 := by exact prefixLift 3686129
  have htrace : WordTrace (prefixWord ++ tailWord_3686129) baseStart_3686129 baseEnd_3686129 := by
    simpa [prefixWord, tailWord_3686129, baseEnd_3686129] using wordTrace_append hprefix tailTrace_3686129
  have hstable : (prefixWord ++ tailWord_3686129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3686129).length < 2 ^ (prefixWord ++ tailWord_3686129).sum := by decide
  have hdescent : baseEnd_3686129 < baseStart_3686129 := by decide
  rcases family_descends (prefixWord ++ tailWord_3686129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3686146 : List Nat := [3, 4, 1, 1, 1, 1, 1, 3, 8]
def baseStart_3686146 : Nat := 118140960795 + 3686146 * 2 ^ 59
def prefixEnd_3686146 : Nat := 4983230072969 + 3 ^ 40 * 3686146 * 2
def baseEnd_3686146 : Nat := 210307184516471130058081

theorem tailTrace_3686146 : CollatzResearch.WordTrace tailWord_3686146 prefixEnd_3686146 210307184516471130058081 := by
  unfold tailWord_3686146
  simp only [CollatzResearch.WordTrace]
  refine ⟨33611197425932515115345573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89629859802486706974254861 33611197425932515115345573)
  ·
    refine ⟨6302099517362346584127295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33611197425932515115345573 6302099517362346584127295)
    ·
      refine ⟨9453149276043519876190943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6302099517362346584127295 9453149276043519876190943)
      ·
        refine ⟨14179723914065279814286415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9453149276043519876190943 14179723914065279814286415)
        ·
          refine ⟨21269585871097919721429623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14179723914065279814286415 21269585871097919721429623)
          ·
            refine ⟨31904378806646879582144435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21269585871097919721429623 31904378806646879582144435)
            ·
              refine ⟨47856568209970319373216653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31904378806646879582144435 47856568209970319373216653)
              ·
                refine ⟨17946213078738869764956245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47856568209970319373216653 17946213078738869764956245)
                ·
                  refine ⟨210307184516471130058081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17946213078738869764956245 210307184516471130058081)
                  ·
                    rfl

theorem cell23_3686146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 3, 8].length) (baseStart_3686146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3686146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3686146 prefixEnd_3686146 := by exact prefixLift 3686146
  have htrace : WordTrace (prefixWord ++ tailWord_3686146) baseStart_3686146 baseEnd_3686146 := by
    simpa [prefixWord, tailWord_3686146, baseEnd_3686146] using wordTrace_append hprefix tailTrace_3686146
  have hstable : (prefixWord ++ tailWord_3686146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3686146).length < 2 ^ (prefixWord ++ tailWord_3686146).sum := by decide
  have hdescent : baseEnd_3686146 < baseStart_3686146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3686146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3686176 : List Nat := [2, 1, 1, 5, 1, 1, 3, 1, 3, 5]
def baseStart_3686176 : Nat := 118140960795 + 3686176 * 2 ^ 59
def prefixEnd_3686176 : Nat := 4983230072969 + 3 ^ 40 * 3686176 * 2
def baseEnd_3686176 : Nat := 630926688355958351049197

theorem tailTrace_3686176 : CollatzResearch.WordTrace tailWord_3686176 prefixEnd_3686176 630926688355958351049197 := by
  unfold tailWord_3686176
  simp only [CollatzResearch.WordTrace]
  refine ⟨67222941946810687792487191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89630589262414250389982921 67222941946810687792487191)
  ·
    refine ⟨100834412920216031688730787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67222941946810687792487191 100834412920216031688730787)
    ·
      refine ⟨151251619380324047533096181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100834412920216031688730787 151251619380324047533096181)
      ·
        refine ⟨14179839316905379456227767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 151251619380324047533096181 14179839316905379456227767)
        ·
          refine ⟨21269758975358069184341651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14179839316905379456227767 21269758975358069184341651)
          ·
            refine ⟨31904638463037103776512477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21269758975358069184341651 31904638463037103776512477)
            ·
              refine ⟨11964239423638913916192179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31904638463037103776512477 11964239423638913916192179)
              ·
                refine ⟨17946359135458370874288269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11964239423638913916192179 17946359135458370874288269)
                ·
                  refine ⟨6729884675796889077858101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17946359135458370874288269 6729884675796889077858101)
                  ·
                    refine ⟨630926688355958351049197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6729884675796889077858101 630926688355958351049197)
                    ·
                      rfl

theorem cell23_3686176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 1, 3, 5].length) (baseStart_3686176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3686176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3686176 prefixEnd_3686176 := by exact prefixLift 3686176
  have htrace : WordTrace (prefixWord ++ tailWord_3686176) baseStart_3686176 baseEnd_3686176 := by
    simpa [prefixWord, tailWord_3686176, baseEnd_3686176] using wordTrace_append hprefix tailTrace_3686176
  have hstable : (prefixWord ++ tailWord_3686176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3686176).length < 2 ^ (prefixWord ++ tailWord_3686176).sum := by decide
  have hdescent : baseEnd_3686176 < baseStart_3686176 := by decide
  rcases family_descends (prefixWord ++ tailWord_3686176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3686201 : List Nat := [1, 2, 1, 7, 2, 1, 2, 2, 1, 4]
def baseStart_3686201 : Nat := 118140960795 + 3686201 * 2 ^ 59
def prefixEnd_3686201 : Nat := 4983230072969 + 3 ^ 40 * 3686201 * 2
def baseEnd_3686201 : Nat := 630930967361412485111659

theorem tailTrace_3686201 : CollatzResearch.WordTrace tailWord_3686201 prefixEnd_3686201 630930967361412485111659 := by
  unfold tailWord_3686201
  simp only [CollatzResearch.WordTrace]
  refine ⟨134446795718530804854634457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89631197145687203236422971 134446795718530804854634457)
  ·
    refine ⟨100835096788898103640975843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134446795718530804854634457 100835096788898103640975843)
    ·
      refine ⟨151252645183347155461463765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100835096788898103640975843 151252645183347155461463765)
      ·
        refine ⟨3544983871484698956128057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 151252645183347155461463765 3544983871484698956128057)
        ·
          refine ⟨2658737903613524217096043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3544983871484698956128057 2658737903613524217096043)
          ·
            refine ⟨3988106855420286325644065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2658737903613524217096043 3988106855420286325644065)
            ·
              refine ⟨2991080141565214744233049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3988106855420286325644065 2991080141565214744233049)
              ·
                refine ⟨2243310106173911058174787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2991080141565214744233049 2243310106173911058174787)
                ·
                  refine ⟨3364965159260866587262181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2243310106173911058174787 3364965159260866587262181)
                  ·
                    refine ⟨630930967361412485111659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3364965159260866587262181 630930967361412485111659)
                    ·
                      rfl

theorem cell23_3686201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 2, 2, 1, 4].length) (baseStart_3686201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3686201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3686201 prefixEnd_3686201 := by exact prefixLift 3686201
  have htrace : WordTrace (prefixWord ++ tailWord_3686201) baseStart_3686201 baseEnd_3686201 := by
    simpa [prefixWord, tailWord_3686201, baseEnd_3686201] using wordTrace_append hprefix tailTrace_3686201
  have hstable : (prefixWord ++ tailWord_3686201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3686201).length < 2 ^ (prefixWord ++ tailWord_3686201).sum := by decide
  have hdescent : baseEnd_3686201 < baseStart_3686201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3686201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3686207 : List Nat := [1, 1, 2, 2, 6, 1, 1, 4, 1, 1, 3]
def baseStart_3686207 : Nat := 118140960795 + 3686207 * 2 ^ 59
def prefixEnd_3686207 : Nat := 4983230072969 + 3 ^ 40 * 3686207 * 2
def baseEnd_3686207 : Nat := 1892795982968164431859949

theorem tailTrace_3686207 : CollatzResearch.WordTrace tailWord_3686207 prefixEnd_3686207 1892795982968164431859949 := by
  unfold tailWord_3686207
  simp only [CollatzResearch.WordTrace]
  refine ⟨134447014556509067879352875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89631343037672711919568583 134447014556509067879352875)
  ·
    refine ⟨201670521834763601819029313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134447014556509067879352875 201670521834763601819029313)
    ·
      refine ⟨151252891376072701364271985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201670521834763601819029313 151252891376072701364271985)
      ·
        refine ⟨113439668532054526023203989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151252891376072701364271985 113439668532054526023203989)
        ·
          refine ⟨5317484462440055907337687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 113439668532054526023203989 5317484462440055907337687)
          ·
            refine ⟨7976226693660083861006531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5317484462440055907337687 7976226693660083861006531)
            ·
              refine ⟨11964340040490125791509797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7976226693660083861006531 11964340040490125791509797)
              ·
                refine ⟨2243313757591898585908087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11964340040490125791509797 2243313757591898585908087)
                ·
                  refine ⟨3364970636387847878862131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2243313757591898585908087 3364970636387847878862131)
                  ·
                    refine ⟨5047455954581771818293197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3364970636387847878862131 5047455954581771818293197)
                    ·
                      refine ⟨1892795982968164431859949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5047455954581771818293197 1892795982968164431859949)
                      ·
                        rfl

theorem cell23_3686207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 4, 1, 1, 3].length) (baseStart_3686207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3686207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3686207 prefixEnd_3686207 := by exact prefixLift 3686207
  have htrace : WordTrace (prefixWord ++ tailWord_3686207) baseStart_3686207 baseEnd_3686207 := by
    simpa [prefixWord, tailWord_3686207, baseEnd_3686207] using wordTrace_append hprefix tailTrace_3686207
  have hstable : (prefixWord ++ tailWord_3686207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3686207).length < 2 ^ (prefixWord ++ tailWord_3686207).sum := by decide
  have hdescent : baseEnd_3686207 < baseStart_3686207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3686207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3686233 : List Nat := [1, 2, 1, 2, 2, 3, 2, 4, 1, 2, 3]
def baseStart_3686233 : Nat := 118140960795 + 3686233 * 2 ^ 59
def prefixEnd_3686233 : Nat := 4983230072969 + 3 ^ 40 * 3686233 * 2
def baseEnd_3686233 : Nat := 1892809333465181330134829

theorem tailTrace_3686233 : CollatzResearch.WordTrace tailWord_3686233 prefixEnd_3686233 1892809333465181330134829 := by
  unfold tailWord_3686233
  simp only [CollatzResearch.WordTrace]
  refine ⟨134447962854414874319799353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89631975236276582879866235 134447962854414874319799353)
  ·
    refine ⟨100835972140811155739849515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134447962854414874319799353 100835972140811155739849515)
    ·
      refine ⟨151253958211216733609774273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100835972140811155739849515 151253958211216733609774273)
      ·
        refine ⟨113440468658412550207330705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151253958211216733609774273 113440468658412550207330705)
        ·
          refine ⟨85080351493809412655498029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113440468658412550207330705 85080351493809412655498029)
          ·
            refine ⟨31905131810178529745811761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85080351493809412655498029 31905131810178529745811761)
            ·
              refine ⟨23928848857633897309358821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31905131810178529745811761 23928848857633897309358821)
              ·
                refine ⟨4486659160806355745504779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23928848857633897309358821 4486659160806355745504779)
                ·
                  refine ⟨6729988741209533618257169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4486659160806355745504779 6729988741209533618257169)
                  ·
                    refine ⟨5047491555907150213692877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6729988741209533618257169 5047491555907150213692877)
                    ·
                      refine ⟨1892809333465181330134829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5047491555907150213692877 1892809333465181330134829)
                      ·
                        rfl

theorem cell23_3686233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 4, 1, 2, 3].length) (baseStart_3686233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3686233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3686233 prefixEnd_3686233 := by exact prefixLift 3686233
  have htrace : WordTrace (prefixWord ++ tailWord_3686233) baseStart_3686233 baseEnd_3686233 := by
    simpa [prefixWord, tailWord_3686233, baseEnd_3686233] using wordTrace_append hprefix tailTrace_3686233
  have hstable : (prefixWord ++ tailWord_3686233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3686233).length < 2 ^ (prefixWord ++ tailWord_3686233).sum := by decide
  have hdescent : baseEnd_3686233 < baseStart_3686233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3686233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3686410 : List Nat := [3, 1, 2, 2, 4, 1, 1, 1, 1, 3, 4]
def baseStart_3686410 : Nat := 118140960795 + 3686410 * 2 ^ 59
def prefixEnd_3686410 : Nat := 4983230072969 + 3 ^ 40 * 3686410 * 2
def baseEnd_3686410 : Nat := 1892900219541027137621515

theorem tailTrace_3686410 : CollatzResearch.WordTrace tailWord_3686410 prefixEnd_3686410 1892900219541027137621515 := by
  unfold tailWord_3686410
  simp only [CollatzResearch.WordTrace]
  refine ⟨33613604643693408387248171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89636279049849089032661789 33613604643693408387248171)
  ·
    refine ⟨50420406965540112580872257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33613604643693408387248171 50420406965540112580872257)
    ·
      refine ⟨37815305224155084435654193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50420406965540112580872257 37815305224155084435654193)
      ·
        refine ⟨28361478918116313326740645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37815305224155084435654193 28361478918116313326740645)
        ·
          refine ⟨5317777297146808748763871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28361478918116313326740645 5317777297146808748763871)
          ·
            refine ⟨7976665945720213123145807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5317777297146808748763871 7976665945720213123145807)
            ·
              refine ⟨11964998918580319684718711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7976665945720213123145807 11964998918580319684718711)
              ·
                refine ⟨17947498377870479527078067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11964998918580319684718711 17947498377870479527078067)
                ·
                  refine ⟨26921247566805719290617101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17947498377870479527078067 26921247566805719290617101)
                  ·
                    refine ⟨10095467837552144733981413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26921247566805719290617101 10095467837552144733981413)
                    ·
                      refine ⟨1892900219541027137621515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10095467837552144733981413 1892900219541027137621515)
                      ·
                        rfl

theorem cell23_3686410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 1, 1, 3, 4].length) (baseStart_3686410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3686410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3686410 prefixEnd_3686410 := by exact prefixLift 3686410
  have htrace : WordTrace (prefixWord ++ tailWord_3686410) baseStart_3686410 baseEnd_3686410 := by
    simpa [prefixWord, tailWord_3686410, baseEnd_3686410] using wordTrace_append hprefix tailTrace_3686410
  have hstable : (prefixWord ++ tailWord_3686410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3686410).length < 2 ^ (prefixWord ++ tailWord_3686410).sum := by decide
  have hdescent : baseEnd_3686410 < baseStart_3686410 := by decide
  rcases family_descends (prefixWord ++ tailWord_3686410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3686416 : List Nat := [2, 1, 1, 1, 1, 1, 1, 5, 10]
def baseStart_3686416 : Nat := 118140960795 + 3686416 * 2 ^ 59
def prefixEnd_3686416 : Nat := 4983230072969 + 3 ^ 40 * 3686416 * 2
def baseEnd_3686416 : Nat := 210322588936106012682943

theorem tailTrace_3686416 : CollatzResearch.WordTrace tailWord_3686416 prefixEnd_3686416 210322588936106012682943 := by
  unfold tailWord_3686416
  simp only [CollatzResearch.WordTrace]
  refine ⟨67227318706375948286855551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89636424941834597715807401 67227318706375948286855551)
  ·
    refine ⟨100840978059563922430283327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67227318706375948286855551 100840978059563922430283327)
    ·
      refine ⟨151261467089345883645424991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100840978059563922430283327 151261467089345883645424991)
      ·
        refine ⟨226892200634018825468137487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151261467089345883645424991 226892200634018825468137487)
        ·
          refine ⟨340338300951028238202206231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226892200634018825468137487 340338300951028238202206231)
          ·
            refine ⟨510507451426542357303309347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340338300951028238202206231 510507451426542357303309347)
            ·
              refine ⟨765761177139813535954964021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 510507451426542357303309347 765761177139813535954964021)
              ·
                refine ⟨71790110356857518995777877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 765761177139813535954964021 71790110356857518995777877)
                ·
                  refine ⟨210322588936106012682943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 71790110356857518995777877 210322588936106012682943)
                  ·
                    rfl

theorem cell23_3686416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 10].length) (baseStart_3686416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3686416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3686416 prefixEnd_3686416 := by exact prefixLift 3686416
  have htrace : WordTrace (prefixWord ++ tailWord_3686416) baseStart_3686416 baseEnd_3686416 := by
    simpa [prefixWord, tailWord_3686416, baseEnd_3686416] using wordTrace_append hprefix tailTrace_3686416
  have hstable : (prefixWord ++ tailWord_3686416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3686416).length < 2 ^ (prefixWord ++ tailWord_3686416).sum := by decide
  have hdescent : baseEnd_3686416 < baseStart_3686416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3686416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3686437 : List Nat := [1, 3, 1, 2, 2, 3, 2, 4, 1, 4]
def baseStart_3686437 : Nat := 118140960795 + 3686437 * 2 ^ 59
def prefixEnd_3686437 : Nat := 4983230072969 + 3 ^ 40 * 3686437 * 2
def baseEnd_3686437 : Nat := 630971361172899510661297

theorem tailTrace_3686437 : CollatzResearch.WordTrace tailWord_3686437 prefixEnd_3686437 630971361172899510661297 := by
  unfold tailWord_3686437
  simp only [CollatzResearch.WordTrace]
  refine ⟨134455403345675817160225565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89636935563783878106817043 134455403345675817160225565)
  ·
    refine ⟨50420776254628431435084587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134455403345675817160225565 50420776254628431435084587)
    ·
      refine ⟨75631164381942647152626881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50420776254628431435084587 75631164381942647152626881)
      ·
        refine ⟨56723373286456985364470161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75631164381942647152626881 56723373286456985364470161)
        ·
          refine ⟨42542529964842739023352621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56723373286456985364470161 42542529964842739023352621)
          ·
            refine ⟨15953448736816027133757233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42542529964842739023352621 15953448736816027133757233)
            ·
              refine ⟨11965086552612020350317925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15953448736816027133757233 11965086552612020350317925)
              ·
                refine ⟨2243453728614753815684611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11965086552612020350317925 2243453728614753815684611)
                ·
                  refine ⟨3365180592922130723526917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2243453728614753815684611 3365180592922130723526917)
                  ·
                    refine ⟨630971361172899510661297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3365180592922130723526917 630971361172899510661297)
                    ·
                      rfl

theorem cell23_3686437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 4, 1, 4].length) (baseStart_3686437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3686437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3686437 prefixEnd_3686437 := by exact prefixLift 3686437
  have htrace : WordTrace (prefixWord ++ tailWord_3686437) baseStart_3686437 baseEnd_3686437 := by
    simpa [prefixWord, tailWord_3686437, baseEnd_3686437] using wordTrace_append hprefix tailTrace_3686437
  have hstable : (prefixWord ++ tailWord_3686437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3686437).length < 2 ^ (prefixWord ++ tailWord_3686437).sum := by decide
  have hdescent : baseEnd_3686437 < baseStart_3686437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3686437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3686463 : List Nat := [1, 1, 2, 2, 3, 1, 2, 3, 3, 5]
def baseStart_3686463 : Nat := 118140960795 + 3686463 * 2 ^ 59
def prefixEnd_3686463 : Nat := 4983230072969 + 3 ^ 40 * 3686463 * 2
def baseEnd_3686463 : Nat := 630975811338571810086257

theorem tailTrace_3686463 : CollatzResearch.WordTrace tailWord_3686463 prefixEnd_3686463 630975811338571810086257 := by
  unfold tailWord_3686463
  simp only [CollatzResearch.WordTrace]
  refine ⟨134456351643581623600672043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89637567762387749067114695 134456351643581623600672043)
  ·
    refine ⟨201684527465372435401008065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134456351643581623600672043 201684527465372435401008065)
    ·
      refine ⟨151263395599029326550756049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201684527465372435401008065 151263395599029326550756049)
      ·
        refine ⟨113447546699271994913067037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151263395599029326550756049 113447546699271994913067037)
        ·
          refine ⟨42542830012226998092400139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113447546699271994913067037 42542830012226998092400139)
          ·
            refine ⟨63814245018340497138600209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42542830012226998092400139 63814245018340497138600209)
            ·
              refine ⟨47860683763755372853950157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63814245018340497138600209 47860683763755372853950157)
              ·
                refine ⟨17947756411408264820231309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47860683763755372853950157 17947756411408264820231309)
                ·
                  refine ⟨6730408654278099307586741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17947756411408264820231309 6730408654278099307586741)
                  ·
                    refine ⟨630975811338571810086257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6730408654278099307586741 630975811338571810086257)
                    ·
                      rfl

theorem cell23_3686463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3, 3, 5].length) (baseStart_3686463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3686463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3686463 prefixEnd_3686463 := by exact prefixLift 3686463
  have htrace : WordTrace (prefixWord ++ tailWord_3686463) baseStart_3686463 baseEnd_3686463 := by
    simpa [prefixWord, tailWord_3686463, baseEnd_3686463] using wordTrace_append hprefix tailTrace_3686463
  have hstable : (prefixWord ++ tailWord_3686463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3686463).length < 2 ^ (prefixWord ++ tailWord_3686463).sum := by decide
  have hdescent : baseEnd_3686463 < baseStart_3686463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3686463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3686510 : List Nat := [4, 1, 2, 2, 1, 1, 2, 3, 1, 6]
def baseStart_3686510 : Nat := 118140960795 + 3686510 * 2 ^ 59
def prefixEnd_3686510 : Nat := 4983230072969 + 3 ^ 40 * 3686510 * 2
def baseEnd_3686510 : Nat := 630983855868825582123685

theorem tailTrace_3686510 : CollatzResearch.WordTrace tailWord_3686510 prefixEnd_3686510 630983855868825582123685 := by
  unfold tailWord_3686510
  simp only [CollatzResearch.WordTrace]
  refine ⟨16807258234301418828454123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89638710582940900418421989 16807258234301418828454123)
  ·
    refine ⟨25210887351452128242681185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16807258234301418828454123 25210887351452128242681185)
    ·
      refine ⟨18908165513589096182010889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25210887351452128242681185 18908165513589096182010889)
      ·
        refine ⟨14181124135191822136508167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18908165513589096182010889 14181124135191822136508167)
        ·
          refine ⟨21271686202787733204762251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14181124135191822136508167 21271686202787733204762251)
          ·
            refine ⟨31907529304181599807143377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21271686202787733204762251 31907529304181599807143377)
            ·
              refine ⟨23930646978136199855357533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31907529304181599807143377 23930646978136199855357533)
              ·
                refine ⟨8973992616801074945759075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23930646978136199855357533 8973992616801074945759075)
                ·
                  refine ⟨13460988925201612418638613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8973992616801074945759075 13460988925201612418638613)
                  ·
                    refine ⟨630983855868825582123685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13460988925201612418638613 630983855868825582123685)
                    ·
                      rfl

theorem cell23_3686510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 3, 1, 6].length) (baseStart_3686510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3686510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3686510 prefixEnd_3686510 := by exact prefixLift 3686510
  have htrace : WordTrace (prefixWord ++ tailWord_3686510) baseStart_3686510 baseEnd_3686510 := by
    simpa [prefixWord, tailWord_3686510, baseEnd_3686510] using wordTrace_append hprefix tailTrace_3686510
  have hstable : (prefixWord ++ tailWord_3686510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3686510).length < 2 ^ (prefixWord ++ tailWord_3686510).sum := by decide
  have hdescent : baseEnd_3686510 < baseStart_3686510 := by decide
  rcases family_descends (prefixWord ++ tailWord_3686510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3686513 : List Nat := [1, 2, 2, 2, 1, 1, 3, 3, 1, 1, 6]
def baseStart_3686513 : Nat := 118140960795 + 3686513 * 2 ^ 59
def prefixEnd_3686513 : Nat := 4983230072969 + 3 ^ 40 * 3686513 * 2
def baseEnd_3686513 : Nat := 1892953108048440234633541

theorem tailTrace_3686513 : CollatzResearch.WordTrace tailWord_3686513 prefixEnd_3686513 1892953108048440234633541 := by
  unfold tailWord_3686513
  simp only [CollatzResearch.WordTrace]
  refine ⟨134458175293400482139992193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89638783528933654759994795 134458175293400482139992193)
  ·
    refine ⟨100843631470050361604994145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134458175293400482139992193 100843631470050361604994145)
    ·
      refine ⟨75632723602537771203745609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100843631470050361604994145 75632723602537771203745609)
      ·
        refine ⟨56724542701903328402809207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75632723602537771203745609 56724542701903328402809207)
        ·
          refine ⟨85086814052854992604213811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56724542701903328402809207 85086814052854992604213811)
          ·
            refine ⟨127630221079282488906320717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85086814052854992604213811 127630221079282488906320717)
            ·
              refine ⟨47861332904730933339870269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127630221079282488906320717 47861332904730933339870269)
              ·
                refine ⟨17947999839274100002451351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47861332904730933339870269 17947999839274100002451351)
                ·
                  refine ⟨26921999758911150003677027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17947999839274100002451351 26921999758911150003677027)
                  ·
                    refine ⟨40382999638366725005515541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26921999758911150003677027 40382999638366725005515541)
                    ·
                      refine ⟨1892953108048440234633541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40382999638366725005515541 1892953108048440234633541)
                      ·
                        rfl

theorem cell23_3686513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3, 1, 1, 6].length) (baseStart_3686513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3686513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3686513 prefixEnd_3686513 := by exact prefixLift 3686513
  have htrace : WordTrace (prefixWord ++ tailWord_3686513) baseStart_3686513 baseEnd_3686513 := by
    simpa [prefixWord, tailWord_3686513, baseEnd_3686513] using wordTrace_append hprefix tailTrace_3686513
  have hstable : (prefixWord ++ tailWord_3686513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3686513).length < 2 ^ (prefixWord ++ tailWord_3686513).sum := by decide
  have hdescent : baseEnd_3686513 < baseStart_3686513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3686513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3686563 : List Nat := [1, 1, 1, 4, 1, 1, 1, 1, 3, 4, 5]
def baseStart_3686563 : Nat := 118140960795 + 3686563 * 2 ^ 59
def prefixEnd_3686563 : Nat := 4983230072969 + 3 ^ 40 * 3686563 * 2
def baseEnd_3686563 : Nat := 1892978782081165039008311

theorem tailTrace_3686563 : CollatzResearch.WordTrace tailWord_3686563 prefixEnd_3686563 1892978782081165039008311 := by
  unfold tailWord_3686563
  simp only [CollatzResearch.WordTrace]
  refine ⟨134459998943219340679312343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89639999295479560452874895 134459998943219340679312343)
  ·
    refine ⟨201689998414829011018968515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134459998943219340679312343 201689998414829011018968515)
    ·
      refine ⟨302534997622243516528452773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201689998414829011018968515 302534997622243516528452773)
      ·
        refine ⟨56725312054170659349084895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 302534997622243516528452773 56725312054170659349084895)
        ·
          refine ⟨85087968081255989023627343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56725312054170659349084895 85087968081255989023627343)
          ·
            refine ⟨127631952121883983535441015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85087968081255989023627343 127631952121883983535441015)
            ·
              refine ⟨191447928182825975303161523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127631952121883983535441015 191447928182825975303161523)
              ·
                refine ⟨287171892274238962954742285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191447928182825975303161523 287171892274238962954742285)
                ·
                  refine ⟨107689459602839611108028357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 287171892274238962954742285 107689459602839611108028357)
                  ·
                    refine ⟨20191773675532427082755317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 107689459602839611108028357 20191773675532427082755317)
                    ·
                      refine ⟨1892978782081165039008311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20191773675532427082755317 1892978782081165039008311)
                      ·
                        rfl

theorem cell23_3686563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 4, 5].length) (baseStart_3686563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3686563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3686563 prefixEnd_3686563 := by exact prefixLift 3686563
  have htrace : WordTrace (prefixWord ++ tailWord_3686563) baseStart_3686563 baseEnd_3686563 := by
    simpa [prefixWord, tailWord_3686563, baseEnd_3686563] using wordTrace_append hprefix tailTrace_3686563
  have hstable : (prefixWord ++ tailWord_3686563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3686563).length < 2 ^ (prefixWord ++ tailWord_3686563).sum := by decide
  have hdescent : baseEnd_3686563 < baseStart_3686563 := by decide
  rcases family_descends (prefixWord ++ tailWord_3686563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3686588 : List Nat := [2, 2, 2, 3, 4, 1, 2, 1, 1, 2, 3]
def baseStart_3686588 : Nat := 118140960795 + 3686588 * 2 ^ 59
def prefixEnd_3686588 : Nat := 4983230072969 + 3 ^ 40 * 3686588 * 2
def baseEnd_3686588 : Nat := 1892991619097527441195697

theorem tailTrace_3686588 : CollatzResearch.WordTrace tailWord_3686588 prefixEnd_3686588 1892991619097527441195697 := by
  unfold tailWord_3686588
  simp only [CollatzResearch.WordTrace]
  refine ⟨67230455384064384974486209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89640607178752513299314945 67230455384064384974486209)
  ·
    refine ⟨50422841538048288730864657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67230455384064384974486209 50422841538048288730864657)
    ·
      refine ⟨37817131153536216548148493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50422841538048288730864657 37817131153536216548148493)
      ·
        refine ⟨14181424182576081205555685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37817131153536216548148493 14181424182576081205555685)
        ·
          refine ⟨2659017034233015226041691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14181424182576081205555685 2659017034233015226041691)
          ·
            refine ⟨3988525551349522839062537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2659017034233015226041691 3988525551349522839062537)
            ·
              refine ⟨2991394163512142129296903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3988525551349522839062537 2991394163512142129296903)
              ·
                refine ⟨4487091245268213193945355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2991394163512142129296903 4487091245268213193945355)
                ·
                  refine ⟨6730636867902319790918033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4487091245268213193945355 6730636867902319790918033)
                  ·
                    refine ⟨5047977650926739843188525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6730636867902319790918033 5047977650926739843188525)
                    ·
                      refine ⟨1892991619097527441195697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5047977650926739843188525 1892991619097527441195697)
                      ·
                        rfl

theorem cell23_3686588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 2, 1, 1, 2, 3].length) (baseStart_3686588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3686588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3686588 prefixEnd_3686588 := by exact prefixLift 3686588
  have htrace : WordTrace (prefixWord ++ tailWord_3686588) baseStart_3686588 baseEnd_3686588 := by
    simpa [prefixWord, tailWord_3686588, baseEnd_3686588] using wordTrace_append hprefix tailTrace_3686588
  have hstable : (prefixWord ++ tailWord_3686588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3686588).length < 2 ^ (prefixWord ++ tailWord_3686588).sum := by decide
  have hdescent : baseEnd_3686588 < baseStart_3686588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3686588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3686640 : List Nat := [2, 1, 1, 1, 3, 1, 1, 4, 1, 5, 3]
def baseStart_3686640 : Nat := 118140960795 + 3686640 * 2 ^ 59
def prefixEnd_3686640 : Nat := 4983230072969 + 3 ^ 40 * 3686640 * 2
def baseEnd_3686640 : Nat := 1893018320091561237745457

theorem tailTrace_3686640 : CollatzResearch.WordTrace tailWord_3686640 prefixEnd_3686640 1893018320091561237745457 := by
  unfold tailWord_3686640
  simp only [CollatzResearch.WordTrace]
  refine ⟨67231403681970191414932687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89641871575960255219910249 67231403681970191414932687)
  ·
    refine ⟨100847105522955287122399031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67231403681970191414932687 100847105522955287122399031)
    ·
      refine ⟨151270658284432930683598547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100847105522955287122399031 151270658284432930683598547)
      ·
        refine ⟨226905987426649396025397821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151270658284432930683598547 226905987426649396025397821)
        ·
          refine ⟨85089745284993523509524183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226905987426649396025397821 85089745284993523509524183)
          ·
            refine ⟨127634617927490285264286275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85089745284993523509524183 127634617927490285264286275)
            ·
              refine ⟨191451926891235427896429413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127634617927490285264286275 191451926891235427896429413)
              ·
                refine ⟨35897236292106642730580515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 191451926891235427896429413 35897236292106642730580515)
                ·
                  refine ⟨53845854438159964095870773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35897236292106642730580515 53845854438159964095870773)
                  ·
                    refine ⟨5048048853577496633987885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53845854438159964095870773 5048048853577496633987885)
                    ·
                      refine ⟨1893018320091561237745457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5048048853577496633987885 1893018320091561237745457)
                      ·
                        rfl

theorem cell23_3686640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 1, 5, 3].length) (baseStart_3686640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3686640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3686640 prefixEnd_3686640 := by exact prefixLift 3686640
  have htrace : WordTrace (prefixWord ++ tailWord_3686640) baseStart_3686640 baseEnd_3686640 := by
    simpa [prefixWord, tailWord_3686640, baseEnd_3686640] using wordTrace_append hprefix tailTrace_3686640
  have hstable : (prefixWord ++ tailWord_3686640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3686640).length < 2 ^ (prefixWord ++ tailWord_3686640).sum := by decide
  have hdescent : baseEnd_3686640 < baseStart_3686640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3686640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3686667 : List Nat := [1, 1, 1, 1, 5, 2, 2, 1, 2, 5, 2]
def baseStart_3686667 : Nat := 118140960795 + 3686667 * 2 ^ 59
def prefixEnd_3686667 : Nat := 4983230072969 + 3 ^ 40 * 3686667 * 2
def baseEnd_3686667 : Nat := 1893032184069232632107833

theorem tailTrace_3686667 : CollatzResearch.WordTrace tailWord_3686667 prefixEnd_3686667 1893032184069232632107833 := by
  unfold tailWord_3686667
  simp only [CollatzResearch.WordTrace]
  refine ⟨134463792134842566441098255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89642528089895044294065503 134463792134842566441098255)
  ·
    refine ⟨201695688202263849661647383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134463792134842566441098255 201695688202263849661647383)
    ·
      refine ⟨302543532303395774492471075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201695688202263849661647383 302543532303395774492471075)
      ·
        refine ⟨453815298455093661738706613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302543532303395774492471075 453815298455093661738706613)
        ·
          refine ⟨42545184230165030788003745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 453815298455093661738706613 42545184230165030788003745)
          ·
            refine ⟨31908888172623773091002809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42545184230165030788003745 31908888172623773091002809)
            ·
              refine ⟨23931666129467829818252107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31908888172623773091002809 23931666129467829818252107)
              ·
                refine ⟨35897499194201744727378161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23931666129467829818252107 35897499194201744727378161)
                ·
                  refine ⟨26923124395651308545533621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35897499194201744727378161 26923124395651308545533621)
                  ·
                    refine ⟨2524042912092310176143777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26923124395651308545533621 2524042912092310176143777)
                    ·
                      refine ⟨1893032184069232632107833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2524042912092310176143777 1893032184069232632107833)
                      ·
                        rfl

theorem cell23_3686667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 2, 5, 2].length) (baseStart_3686667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3686667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3686667 prefixEnd_3686667 := by exact prefixLift 3686667
  have htrace : WordTrace (prefixWord ++ tailWord_3686667) baseStart_3686667 baseEnd_3686667 := by
    simpa [prefixWord, tailWord_3686667, baseEnd_3686667] using wordTrace_append hprefix tailTrace_3686667
  have hstable : (prefixWord ++ tailWord_3686667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3686667).length < 2 ^ (prefixWord ++ tailWord_3686667).sum := by decide
  have hdescent : baseEnd_3686667 < baseStart_3686667 := by decide
  rcases family_descends (prefixWord ++ tailWord_3686667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3686737 : List Nat := [1, 2, 2, 1, 4, 2, 2, 3, 6]
def baseStart_3686737 : Nat := 118140960795 + 3686737 * 2 ^ 59
def prefixEnd_3686737 : Nat := 4983230072969 + 3 ^ 40 * 3686737 * 2
def baseEnd_3686737 : Nat := 210340903079449706470279

theorem tailTrace_3686737 : CollatzResearch.WordTrace tailWord_3686737 prefixEnd_3686737 210340903079449706470279 := by
  unfold tailWord_3686737
  simp only [CollatzResearch.WordTrace]
  refine ⟨134466345244588968396146465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89644230163059312264097643 134466345244588968396146465)
  ·
    refine ⟨100849758933441726297109849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134466345244588968396146465 100849758933441726297109849)
    ·
      refine ⟨75637319200081294722832387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100849758933441726297109849 75637319200081294722832387)
      ·
        refine ⟨113455978800121942084248581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75637319200081294722832387 113455978800121942084248581)
        ·
          refine ⟨21272996025022864140796609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113455978800121942084248581 21272996025022864140796609)
          ·
            refine ⟨15954747018767148105597457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21272996025022864140796609 15954747018767148105597457)
            ·
              refine ⟨11966060264075361079198093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15954747018767148105597457 11966060264075361079198093)
              ·
                refine ⟨4487272599028260404699285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11966060264075361079198093 4487272599028260404699285)
                ·
                  refine ⟨210340903079449706470279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4487272599028260404699285 210340903079449706470279)
                  ·
                    rfl

theorem cell23_3686737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 3, 6].length) (baseStart_3686737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3686737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3686737 prefixEnd_3686737 := by exact prefixLift 3686737
  have htrace : WordTrace (prefixWord ++ tailWord_3686737) baseStart_3686737 baseEnd_3686737 := by
    simpa [prefixWord, tailWord_3686737, baseEnd_3686737] using wordTrace_append hprefix tailTrace_3686737
  have hstable : (prefixWord ++ tailWord_3686737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3686737).length < 2 ^ (prefixWord ++ tailWord_3686737).sum := by decide
  have hdescent : baseEnd_3686737 < baseStart_3686737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3686737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3686748 : List Nat := [2, 2, 4, 3, 1, 2, 1, 1, 2, 1, 4]
def baseStart_3686748 : Nat := 118140960795 + 3686748 * 2 ^ 59
def prefixEnd_3686748 : Nat := 4983230072969 + 3 ^ 40 * 3686748 * 2
def baseEnd_3686748 : Nat := 1893073776002246815194961

theorem tailTrace_3686748 : CollatzResearch.WordTrace tailWord_3686748 prefixEnd_3686748 1893073776002246815194961 := by
  unfold tailWord_3686748
  simp only [CollatzResearch.WordTrace]
  refine ⟨67233373223774558637398449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89644497631699411516531265 67233373223774558637398449)
  ·
    refine ⟨50425029917830918978048837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67233373223774558637398449 50425029917830918978048837)
    ·
      refine ⟨9454693109593297308384157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50425029917830918978048837 9454693109593297308384157)
      ·
        refine ⟨3545509916097486490644059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9454693109593297308384157 3545509916097486490644059)
        ·
          refine ⟨5318264874146229735966089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3545509916097486490644059 5318264874146229735966089)
          ·
            refine ⟨3988698655609672301974567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5318264874146229735966089 3988698655609672301974567)
            ·
              refine ⟨5983047983414508452961851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3988698655609672301974567 5983047983414508452961851)
              ·
                refine ⟨8974571975121762679442777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5983047983414508452961851 8974571975121762679442777)
                ·
                  refine ⟨6730928981341322009582083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8974571975121762679442777 6730928981341322009582083)
                  ·
                    refine ⟨10096393472011983014373125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6730928981341322009582083 10096393472011983014373125)
                    ·
                      refine ⟨1893073776002246815194961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10096393472011983014373125 1893073776002246815194961)
                      ·
                        rfl

theorem cell23_3686748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_3686748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3686748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3686748 prefixEnd_3686748 := by exact prefixLift 3686748
  have htrace : WordTrace (prefixWord ++ tailWord_3686748) baseStart_3686748 baseEnd_3686748 := by
    simpa [prefixWord, tailWord_3686748, baseEnd_3686748] using wordTrace_append hprefix tailTrace_3686748
  have hstable : (prefixWord ++ tailWord_3686748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3686748).length < 2 ^ (prefixWord ++ tailWord_3686748).sum := by decide
  have hdescent : baseEnd_3686748 < baseStart_3686748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3686748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3686781 : List Nat := [1, 4, 1, 1, 2, 4, 2, 1, 3, 1, 3]
def baseStart_3686781 : Nat := 118140960795 + 3686781 * 2 ^ 59
def prefixEnd_3686781 : Nat := 4983230072969 + 3 ^ 40 * 3686781 * 2
def baseEnd_3686781 : Nat := 1893090720863845186082309

theorem tailTrace_3686781 : CollatzResearch.WordTrace tailWord_3686781 prefixEnd_3686781 1893090720863845186082309 := by
  unfold tailWord_3686781
  simp only [CollatzResearch.WordTrace]
  refine ⟨134467950056429563910748197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89645300037619709273832131 134467950056429563910748197)
  ·
    refine ⟨25212740635580543233265287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134467950056429563910748197 25212740635580543233265287)
    ·
      refine ⟨37819110953370814849897931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25212740635580543233265287 37819110953370814849897931)
      ·
        refine ⟨56728666430056222274846897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37819110953370814849897931 56728666430056222274846897)
        ·
          refine ⟨42546499822542166706135173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56728666430056222274846897 42546499822542166706135173)
          ·
            refine ⟨7977468716726656257400345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42546499822542166706135173 7977468716726656257400345)
            ·
              refine ⟨5983101537544992193050259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7977468716726656257400345 5983101537544992193050259)
              ·
                refine ⟨8974652306317488289575389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5983101537544992193050259 8974652306317488289575389)
                ·
                  refine ⟨3365494614869058108590771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8974652306317488289575389 3365494614869058108590771)
                  ·
                    refine ⟨5048241922303587162886157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3365494614869058108590771 5048241922303587162886157)
                    ·
                      refine ⟨1893090720863845186082309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5048241922303587162886157 1893090720863845186082309)
                      ·
                        rfl

theorem cell23_3686781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 1, 3, 1, 3].length) (baseStart_3686781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3686781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3686781 prefixEnd_3686781 := by exact prefixLift 3686781
  have htrace : WordTrace (prefixWord ++ tailWord_3686781) baseStart_3686781 baseEnd_3686781 := by
    simpa [prefixWord, tailWord_3686781, baseEnd_3686781] using wordTrace_append hprefix tailTrace_3686781
  have hstable : (prefixWord ++ tailWord_3686781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3686781).length < 2 ^ (prefixWord ++ tailWord_3686781).sum := by decide
  have hdescent : baseEnd_3686781 < baseStart_3686781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3686781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3686844 : List Nat := [2, 2, 2, 4, 1, 2, 2, 8]
def baseStart_3686844 : Nat := 118140960795 + 3686844 * 2 ^ 59
def prefixEnd_3686844 : Nat := 4983230072969 + 3 ^ 40 * 3686844 * 2
def baseEnd_3686844 : Nat := 70115669264632534799797

theorem tailTrace_3686844 : CollatzResearch.WordTrace tailWord_3686844 prefixEnd_3686844 70115669264632534799797 := by
  unfold tailWord_3686844
  simp only [CollatzResearch.WordTrace]
  refine ⟨67235123927600662835145793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89646831903467550446861057 67235123927600662835145793)
  ·
    refine ⟨50426342945700497126359345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67235123927600662835145793 50426342945700497126359345)
    ·
      refine ⟨37819757209275372844769509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50426342945700497126359345 37819757209275372844769509)
      ·
        refine ⟨7091204476739132408394283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37819757209275372844769509 7091204476739132408394283)
        ·
          refine ⟨10636806715108698612591425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7091204476739132408394283 10636806715108698612591425)
          ·
            refine ⟨7977605036331523959443569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10636806715108698612591425 7977605036331523959443569)
            ·
              refine ⟨5983203777248642969582677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7977605036331523959443569 5983203777248642969582677)
              ·
                refine ⟨70115669264632534799797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5983203777248642969582677 70115669264632534799797)
                ·
                  rfl

theorem cell23_3686844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 8].length) (baseStart_3686844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3686844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3686844 prefixEnd_3686844 := by exact prefixLift 3686844
  have htrace : WordTrace (prefixWord ++ tailWord_3686844) baseStart_3686844 baseEnd_3686844 := by
    simpa [prefixWord, tailWord_3686844, baseEnd_3686844] using wordTrace_append hprefix tailTrace_3686844
  have hstable : (prefixWord ++ tailWord_3686844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3686844).length < 2 ^ (prefixWord ++ tailWord_3686844).sum := by decide
  have hdescent : baseEnd_3686844 < baseStart_3686844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3686844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3686888 : List Nat := [2, 1, 4, 1, 1, 4, 2, 2, 2, 1, 3]
def baseStart_3686888 : Nat := 118140960795 + 3686888 * 2 ^ 59
def prefixEnd_3686888 : Nat := 4983230072969 + 3 ^ 40 * 3686888 * 2
def baseEnd_3686888 : Nat := 1893145663293876267444317

theorem tailTrace_3686888 : CollatzResearch.WordTrace tailWord_3686888 prefixEnd_3686888 1893145663293876267444317 := by
  unfold tailWord_3686888
  simp only [CollatzResearch.WordTrace]
  refine ⟨67235926333520960592446659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89647901778027947456595545 67235926333520960592446659)
  ·
    refine ⟨100853889500281440888669989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67235926333520960592446659 100853889500281440888669989)
    ·
      refine ⟨18910104281302770166625623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100853889500281440888669989 18910104281302770166625623)
      ·
        refine ⟨28365156421954155249938435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18910104281302770166625623 28365156421954155249938435)
        ·
          refine ⟨42547734632931232874907653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28365156421954155249938435 42547734632931232874907653)
          ·
            refine ⟨7977700243674606164045185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42547734632931232874907653 7977700243674606164045185)
            ·
              refine ⟨5983275182755954623033889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7977700243674606164045185 5983275182755954623033889)
              ·
                refine ⟨4487456387066965967275417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5983275182755954623033889 4487456387066965967275417)
                ·
                  refine ⟨3365592290300224475456563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4487456387066965967275417 3365592290300224475456563)
                  ·
                    refine ⟨5048388435450336713184845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3365592290300224475456563 5048388435450336713184845)
                    ·
                      refine ⟨1893145663293876267444317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5048388435450336713184845 1893145663293876267444317)
                      ·
                        rfl

theorem cell23_3686888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 2, 2, 1, 3].length) (baseStart_3686888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3686888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3686888 prefixEnd_3686888 := by exact prefixLift 3686888
  have htrace : WordTrace (prefixWord ++ tailWord_3686888) baseStart_3686888 baseEnd_3686888 := by
    simpa [prefixWord, tailWord_3686888, baseEnd_3686888] using wordTrace_append hprefix tailTrace_3686888
  have hstable : (prefixWord ++ tailWord_3686888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3686888).length < 2 ^ (prefixWord ++ tailWord_3686888).sum := by decide
  have hdescent : baseEnd_3686888 < baseStart_3686888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3686888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3686894 : List Nat := [4, 1, 2, 1, 2, 2, 1, 1, 2, 3, 4]
def baseStart_3686894 : Nat := 118140960795 + 3686894 * 2 ^ 59
def prefixEnd_3686894 : Nat := 4983230072969 + 3 ^ 40 * 3686894 * 2
def baseEnd_3686894 : Nat := 1893148744177803243969289

theorem tailTrace_3686894 : CollatzResearch.WordTrace tailWord_3686894 prefixEnd_3686894 1893148744177803243969289 := by
  unfold tailWord_3686894
  simp only [CollatzResearch.WordTrace]
  refine ⟨16809008938127523026201467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89648047670013456139741157 16809008938127523026201467)
  ·
    refine ⟨25213513407191284539302201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16809008938127523026201467 25213513407191284539302201)
    ·
      refine ⟨18910135055393463404476651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25213513407191284539302201 18910135055393463404476651)
      ·
        refine ⟨28365202583090195106714977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18910135055393463404476651 28365202583090195106714977)
        ·
          refine ⟨21273901937317646330036233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28365202583090195106714977 21273901937317646330036233)
          ·
            refine ⟨15955426452988234747527175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21273901937317646330036233 15955426452988234747527175)
            ·
              refine ⟨23933139679482352121290763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15955426452988234747527175 23933139679482352121290763)
              ·
                refine ⟨35899709519223528181936145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23933139679482352121290763 35899709519223528181936145)
                ·
                  refine ⟨26924782139417646136452109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35899709519223528181936145 26924782139417646136452109)
                  ·
                    refine ⟨10096793302281617301169541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26924782139417646136452109 10096793302281617301169541)
                    ·
                      refine ⟨1893148744177803243969289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10096793302281617301169541 1893148744177803243969289)
                      ·
                        rfl

theorem cell23_3686894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_3686894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3686894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3686894 prefixEnd_3686894 := by exact prefixLift 3686894
  have htrace : WordTrace (prefixWord ++ tailWord_3686894) baseStart_3686894 baseEnd_3686894 := by
    simpa [prefixWord, tailWord_3686894, baseEnd_3686894] using wordTrace_append hprefix tailTrace_3686894
  have hstable : (prefixWord ++ tailWord_3686894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3686894).length < 2 ^ (prefixWord ++ tailWord_3686894).sum := by decide
  have hdescent : baseEnd_3686894 < baseStart_3686894 := by decide
  rcases family_descends (prefixWord ++ tailWord_3686894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3686911 : List Nat := [1, 1, 2, 2, 1, 2, 6, 1, 1, 4, 2]
def baseStart_3686911 : Nat := 118140960795 + 3686911 * 2 ^ 59
def prefixEnd_3686911 : Nat := 4983230072969 + 3 ^ 40 * 3686911 * 2
def baseEnd_3686911 : Nat := 1893157473348929677456711

theorem tailTrace_3686911 : CollatzResearch.WordTrace tailWord_3686911 prefixEnd_3686911 1893157473348929677456711 := by
  unfold tailWord_3686911
  simp only [CollatzResearch.WordTrace]
  refine ⟨134472691545958596112980587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89648461030639064075320391 134472691545958596112980587)
  ·
    refine ⟨201709037318937894169470881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134472691545958596112980587 201709037318937894169470881)
    ·
      refine ⟨151281777989203420627103161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201709037318937894169470881 151281777989203420627103161)
      ·
        refine ⟨113461333491902565470327371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151281777989203420627103161 113461333491902565470327371)
        ·
          refine ⟨170192000237853848205491057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113461333491902565470327371 170192000237853848205491057)
          ·
            refine ⟨127644000178390386154118293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170192000237853848205491057 127644000178390386154118293)
            ·
              refine ⟨5983312508362049350974295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 127644000178390386154118293 5983312508362049350974295)
              ·
                refine ⟨8974968762543074026461443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5983312508362049350974295 8974968762543074026461443)
                ·
                  refine ⟨13462453143814611039692165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8974968762543074026461443 13462453143814611039692165)
                  ·
                    refine ⟨2524209964465239569942281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13462453143814611039692165 2524209964465239569942281)
                    ·
                      refine ⟨1893157473348929677456711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2524209964465239569942281 1893157473348929677456711)
                      ·
                        rfl

theorem cell23_3686911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 1, 1, 4, 2].length) (baseStart_3686911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3686911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3686911 prefixEnd_3686911 := by exact prefixLift 3686911
  have htrace : WordTrace (prefixWord ++ tailWord_3686911) baseStart_3686911 baseEnd_3686911 := by
    simpa [prefixWord, tailWord_3686911, baseEnd_3686911] using wordTrace_append hprefix tailTrace_3686911
  have hstable : (prefixWord ++ tailWord_3686911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3686911).length < 2 ^ (prefixWord ++ tailWord_3686911).sum := by decide
  have hdescent : baseEnd_3686911 < baseStart_3686911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3686911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3686917 : List Nat := [1, 3, 1, 1, 2, 2, 3, 1, 9]
def baseStart_3686917 : Nat := 118140960795 + 3686917 * 2 ^ 59
def prefixEnd_3686917 : Nat := 4983230072969 + 3 ^ 40 * 3686917 * 2
def baseEnd_3686917 : Nat := 210351172692539628220187

theorem tailTrace_3686917 : CollatzResearch.WordTrace tailWord_3686917 prefixEnd_3686917 210351172692539628220187 := by
  unfold tailWord_3686917
  simp only [CollatzResearch.WordTrace]
  refine ⟨134472910383936859137699005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89648606922624572758466003 134472910383936859137699005)
  ·
    refine ⟨50427341393976322176637127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134472910383936859137699005 50427341393976322176637127)
    ·
      refine ⟨75641012090964483264955691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50427341393976322176637127 75641012090964483264955691)
      ·
        refine ⟨113461518136446724897433537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75641012090964483264955691 113461518136446724897433537)
        ·
          refine ⟨85096138602335043673075153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113461518136446724897433537 85096138602335043673075153)
          ·
            refine ⟨63822103951751282754806365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85096138602335043673075153 63822103951751282754806365)
            ·
              refine ⟨23933288981906731033052387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63822103951751282754806365 23933288981906731033052387)
              ·
                refine ⟨35899933472860096549578581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23933288981906731033052387 35899933472860096549578581)
                ·
                  refine ⟨210351172692539628220187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 35899933472860096549578581 210351172692539628220187)
                  ·
                    rfl

theorem cell23_3686917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 9].length) (baseStart_3686917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3686917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3686917 prefixEnd_3686917 := by exact prefixLift 3686917
  have htrace : WordTrace (prefixWord ++ tailWord_3686917) baseStart_3686917 baseEnd_3686917 := by
    simpa [prefixWord, tailWord_3686917, baseEnd_3686917] using wordTrace_append hprefix tailTrace_3686917
  have hstable : (prefixWord ++ tailWord_3686917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3686917).length < 2 ^ (prefixWord ++ tailWord_3686917).sum := by decide
  have hdescent : baseEnd_3686917 < baseStart_3686917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3686917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3686932 : List Nat := [2, 4, 3, 1, 1, 1, 4, 1, 1, 3, 2]
def baseStart_3686932 : Nat := 118140960795 + 3686932 * 2 ^ 59
def prefixEnd_3686932 : Nat := 4983230072969 + 3 ^ 40 * 3686932 * 2
def baseEnd_3686932 : Nat := 1893168256442674095294115

theorem tailTrace_3686932 : CollatzResearch.WordTrace tailWord_3686932 prefixEnd_3686932 1893168256442674095294115 := by
  unfold tailWord_3686932
  simp only [CollatzResearch.WordTrace]
  refine ⟨67236728739441258349747525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89648971652588344466330033 67236728739441258349747525)
  ·
    refine ⟨12606886638645235940577661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67236728739441258349747525 12606886638645235940577661)
    ·
      refine ⟨4727582489491963477716623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12606886638645235940577661 4727582489491963477716623)
      ·
        refine ⟨7091373734237945216574935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4727582489491963477716623 7091373734237945216574935)
        ·
          refine ⟨10637060601356917824862403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7091373734237945216574935 10637060601356917824862403)
          ·
            refine ⟨15955590902035376737293605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10637060601356917824862403 15955590902035376737293605)
            ·
              refine ⟨2991673294131633138242551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15955590902035376737293605 2991673294131633138242551)
              ·
                refine ⟨4487509941197449707363827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2991673294131633138242551 4487509941197449707363827)
                ·
                  refine ⟨6731264911796174561045741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4487509941197449707363827 6731264911796174561045741)
                  ·
                    refine ⟨2524224341923565460392153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6731264911796174561045741 2524224341923565460392153)
                    ·
                      refine ⟨1893168256442674095294115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2524224341923565460392153 1893168256442674095294115)
                      ·
                        rfl

theorem cell23_3686932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_3686932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3686932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3686932 prefixEnd_3686932 := by exact prefixLift 3686932
  have htrace : WordTrace (prefixWord ++ tailWord_3686932) baseStart_3686932 baseEnd_3686932 := by
    simpa [prefixWord, tailWord_3686932, baseEnd_3686932] using wordTrace_append hprefix tailTrace_3686932
  have hstable : (prefixWord ++ tailWord_3686932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3686932).length < 2 ^ (prefixWord ++ tailWord_3686932).sum := by decide
  have hdescent : baseEnd_3686932 < baseStart_3686932 := by decide
  rcases family_descends (prefixWord ++ tailWord_3686932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3686984 : List Nat := [2, 1, 3, 1, 1, 1, 1, 2, 6, 1, 4]
def baseStart_3686984 : Nat := 118140960795 + 3686984 * 2 ^ 59
def prefixEnd_3686984 : Nat := 4983230072969 + 3 ^ 40 * 3686984 * 2
def baseEnd_3686984 : Nat := 1893194957436707891843875

theorem tailTrace_3686984 : CollatzResearch.WordTrace tailWord_3686984 prefixEnd_3686984 1893194957436707891843875 := by
  unfold tailWord_3686984
  simp only [CollatzResearch.WordTrace]
  refine ⟨67237677037347064790194003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89650236049796086386925337 67237677037347064790194003)
  ·
    refine ⟨100856515556020597185291005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67237677037347064790194003 100856515556020597185291005)
    ·
      refine ⟨37821193333507723944484127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100856515556020597185291005 37821193333507723944484127)
      ·
        refine ⟨56731790000261585916726191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37821193333507723944484127 56731790000261585916726191)
        ·
          refine ⟨85097685000392378875089287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56731790000261585916726191 85097685000392378875089287)
          ·
            refine ⟨127646527500588568312633931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85097685000392378875089287 127646527500588568312633931)
            ·
              refine ⟨191469791250882852468950897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127646527500588568312633931 191469791250882852468950897)
              ·
                refine ⟨143602343438162139351713173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191469791250882852468950897 143602343438162139351713173)
                ·
                  refine ⟨6731359848663850282111555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 143602343438162139351713173 6731359848663850282111555)
                  ·
                    refine ⟨10097039772995775423167333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6731359848663850282111555 10097039772995775423167333)
                    ·
                      refine ⟨1893194957436707891843875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10097039772995775423167333 1893194957436707891843875)
                      ·
                        rfl

theorem cell23_3686984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 6, 1, 4].length) (baseStart_3686984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3686984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3686984 prefixEnd_3686984 := by exact prefixLift 3686984
  have htrace : WordTrace (prefixWord ++ tailWord_3686984) baseStart_3686984 baseEnd_3686984 := by
    simpa [prefixWord, tailWord_3686984, baseEnd_3686984] using wordTrace_append hprefix tailTrace_3686984
  have hstable : (prefixWord ++ tailWord_3686984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3686984).length < 2 ^ (prefixWord ++ tailWord_3686984).sum := by decide
  have hdescent : baseEnd_3686984 < baseStart_3686984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3686984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687051 : List Nat := [1, 1, 1, 1, 4, 1, 2, 1, 7, 1, 3]
def baseStart_3687051 : Nat := 118140960795 + 3687051 * 2 ^ 59
def prefixEnd_3687051 : Nat := 4983230072969 + 3 ^ 40 * 3687051 * 2
def baseEnd_3687051 : Nat := 1893229360640559129706067

theorem tailTrace_3687051 : CollatzResearch.WordTrace tailWord_3687051 prefixEnd_3687051 1893229360640559129706067 := by
  unfold tailWord_3687051
  simp only [CollatzResearch.WordTrace]
  refine ⟨134477797765451400023077007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89651865176967600015384671 134477797765451400023077007)
  ·
    refine ⟨201716696648177100034615511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134477797765451400023077007 201716696648177100034615511)
    ·
      refine ⟨302575044972265650051923267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201716696648177100034615511 302575044972265650051923267)
      ·
        refine ⟨453862567458398475077884901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302575044972265650051923267 453862567458398475077884901)
        ·
          refine ⟨85099231398449714077103419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 453862567458398475077884901 85099231398449714077103419)
          ·
            refine ⟨127648847097674571115655129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85099231398449714077103419 127648847097674571115655129)
            ·
              refine ⟨95736635323255928336741347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127648847097674571115655129 95736635323255928336741347)
              ·
                refine ⟨143604952984883892505112021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95736635323255928336741347 143604952984883892505112021)
                ·
                  refine ⟨3365741085583216230588563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 143604952984883892505112021 3365741085583216230588563)
                  ·
                    refine ⟨5048611628374824345882845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3365741085583216230588563 5048611628374824345882845)
                    ·
                      refine ⟨1893229360640559129706067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5048611628374824345882845 1893229360640559129706067)
                      ·
                        rfl

theorem cell23_3687051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 7, 1, 3].length) (baseStart_3687051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3687051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3687051 prefixEnd_3687051 := by exact prefixLift 3687051
  have htrace : WordTrace (prefixWord ++ tailWord_3687051) baseStart_3687051 baseEnd_3687051 := by
    simpa [prefixWord, tailWord_3687051, baseEnd_3687051] using wordTrace_append hprefix tailTrace_3687051
  have hstable : (prefixWord ++ tailWord_3687051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687051).length < 2 ^ (prefixWord ++ tailWord_3687051).sum := by decide
  have hdescent : baseEnd_3687051 < baseStart_3687051 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687058 : List Nat := [3, 2, 3, 1, 2, 2, 2, 2, 6]
def baseStart_3687058 : Nat := 118140960795 + 3687058 * 2 ^ 59
def prefixEnd_3687058 : Nat := 4983230072969 + 3 ^ 40 * 3687058 * 2
def baseEnd_3687058 : Nat := 210359217222793400257615

theorem tailTrace_3687058 : CollatzResearch.WordTrace tailWord_3687058 prefixEnd_3687058 210359217222793400257615 := by
  unfold tailWord_3687058
  simp only [CollatzResearch.WordTrace]
  refine ⟨33619513269106510054645457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89652035384284026812387885 33619513269106510054645457)
  ·
    refine ⟨25214634951829882540984093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33619513269106510054645457 25214634951829882540984093)
    ·
      refine ⟨9455488106936205952869035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25214634951829882540984093 9455488106936205952869035)
      ·
        refine ⟨14183232160404308929303553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9455488106936205952869035 14183232160404308929303553)
        ·
          refine ⟨10637424120303231696977665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14183232160404308929303553 10637424120303231696977665)
          ·
            refine ⟨7978068090227423772733249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10637424120303231696977665 7978068090227423772733249)
            ·
              refine ⟨5983551067670567829549937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7978068090227423772733249 5983551067670567829549937)
              ·
                refine ⟨4487663300752925872162453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5983551067670567829549937 4487663300752925872162453)
                ·
                  refine ⟨210359217222793400257615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4487663300752925872162453 210359217222793400257615)
                  ·
                    rfl

theorem cell23_3687058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 2, 6].length) (baseStart_3687058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3687058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3687058 prefixEnd_3687058 := by exact prefixLift 3687058
  have htrace : WordTrace (prefixWord ++ tailWord_3687058) baseStart_3687058 baseEnd_3687058 := by
    simpa [prefixWord, tailWord_3687058, baseEnd_3687058] using wordTrace_append hprefix tailTrace_3687058
  have hstable : (prefixWord ++ tailWord_3687058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687058).length < 2 ^ (prefixWord ++ tailWord_3687058).sum := by decide
  have hdescent : baseEnd_3687058 < baseStart_3687058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687061 : List Nat := [1, 3, 2, 1, 1, 1, 1, 1, 5, 5, 2]
def baseStart_3687061 : Nat := 118140960795 + 3687061 * 2 ^ 59
def prefixEnd_3687061 : Nat := 4983230072969 + 3 ^ 40 * 3687061 * 2
def baseEnd_3687061 : Nat := 1893234495447104090581021

theorem tailTrace_3687061 : CollatzResearch.WordTrace tailWord_3687061 prefixEnd_3687061 1893234495447104090581021 := by
  unfold tailWord_3687061
  simp only [CollatzResearch.WordTrace]
  refine ⟨134478162495415171730941037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89652108330276781153960691 134478162495415171730941037)
  ·
    refine ⟨50429310935780689399102889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134478162495415171730941037 50429310935780689399102889)
    ·
      refine ⟨37821983201835517049327167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50429310935780689399102889 37821983201835517049327167)
      ·
        refine ⟨56732974802753275573990751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37821983201835517049327167 56732974802753275573990751)
        ·
          refine ⟨85099462204129913360986127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56732974802753275573990751 85099462204129913360986127)
          ·
            refine ⟨127649193306194870041479191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85099462204129913360986127 127649193306194870041479191)
            ·
              refine ⟨191473789959292305062218787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127649193306194870041479191 191473789959292305062218787)
              ·
                refine ⟨287210684938938457593328181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191473789959292305062218787 287210684938938457593328181)
                ·
                  refine ⟨26926001713025480399374517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 287210684938938457593328181 26926001713025480399374517)
                  ·
                    refine ⟨2524312660596138787441361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26926001713025480399374517 2524312660596138787441361)
                    ·
                      refine ⟨1893234495447104090581021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2524312660596138787441361 1893234495447104090581021)
                      ·
                        rfl

theorem cell23_3687061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 5, 2].length) (baseStart_3687061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3687061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3687061 prefixEnd_3687061 := by exact prefixLift 3687061
  have htrace : WordTrace (prefixWord ++ tailWord_3687061) baseStart_3687061 baseEnd_3687061 := by
    simpa [prefixWord, tailWord_3687061, baseEnd_3687061] using wordTrace_append hprefix tailTrace_3687061
  have hstable : (prefixWord ++ tailWord_3687061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687061).length < 2 ^ (prefixWord ++ tailWord_3687061).sum := by decide
  have hdescent : baseEnd_3687061 < baseStart_3687061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687085 : List Nat := [1, 5, 2, 1, 1, 3, 1, 2, 3, 1, 3]
def baseStart_3687085 : Nat := 118140960795 + 3687085 * 2 ^ 59
def prefixEnd_3687085 : Nat := 4983230072969 + 3 ^ 40 * 3687085 * 2
def baseEnd_3687085 : Nat := 1893246818982811996680911

theorem tailTrace_3687085 : CollatzResearch.WordTrace tailWord_3687085 prefixEnd_3687085 1893246818982811996680911 := by
  unfold tailWord_3687085
  simp only [CollatzResearch.WordTrace]
  refine ⟨134479037847328223829814709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89652691898218815886543139 134479037847328223829814709)
  ·
    refine ⟨12607409798187020984045129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 134479037847328223829814709 12607409798187020984045129)
    ·
      refine ⟨9455557348640265738033847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12607409798187020984045129 9455557348640265738033847)
      ·
        refine ⟨14183336022960398607050771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9455557348640265738033847 14183336022960398607050771)
        ·
          refine ⟨21275004034440597910576157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14183336022960398607050771 21275004034440597910576157)
          ·
            refine ⟨7978126512915224216466059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21275004034440597910576157 7978126512915224216466059)
            ·
              refine ⟨11967189769372836324699089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7978126512915224216466059 11967189769372836324699089)
              ·
                refine ⟨8975392327029627243524317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11967189769372836324699089 8975392327029627243524317)
                ·
                  refine ⟨3365772122636110216321619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8975392327029627243524317 3365772122636110216321619)
                  ·
                    refine ⟨5048658183954165324482429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3365772122636110216321619 5048658183954165324482429)
                    ·
                      refine ⟨1893246818982811996680911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5048658183954165324482429 1893246818982811996680911)
                      ·
                        rfl

theorem cell23_3687085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_3687085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3687085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3687085 prefixEnd_3687085 := by exact prefixLift 3687085
  have htrace : WordTrace (prefixWord ++ tailWord_3687085) baseStart_3687085 baseEnd_3687085 := by
    simpa [prefixWord, tailWord_3687085, baseEnd_3687085] using wordTrace_append hprefix tailTrace_3687085
  have hstable : (prefixWord ++ tailWord_3687085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687085).length < 2 ^ (prefixWord ++ tailWord_3687085).sum := by decide
  have hdescent : baseEnd_3687085 < baseStart_3687085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687091 : List Nat := [1, 1, 1, 2, 3, 4, 2, 1, 3, 1, 4]
def baseStart_3687091 : Nat := 118140960795 + 3687091 * 2 ^ 59
def prefixEnd_3687091 : Nat := 4983230072969 + 3 ^ 40 * 3687091 * 2
def baseEnd_3687091 : Nat := 1893249899866738973205883

theorem tailTrace_3687091 : CollatzResearch.WordTrace tailWord_3687091 prefixEnd_3687091 1893249899866738973205883 := by
  unfold tailWord_3687091
  simp only [CollatzResearch.WordTrace]
  refine ⟨134479256685306486854533127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89652837790204324569688751 134479256685306486854533127)
  ·
    refine ⟨201718885027959730281799691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134479256685306486854533127 201718885027959730281799691)
    ·
      refine ⟨302578327541939595422699537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201718885027959730281799691 302578327541939595422699537)
      ·
        refine ⟨226933745656454696567024653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302578327541939595422699537 226933745656454696567024653)
        ·
          refine ⟨85100154621170511212634245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226933745656454696567024653 85100154621170511212634245)
          ·
            refine ⟨15956278991469470852368921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85100154621170511212634245 15956278991469470852368921)
            ·
              refine ⟨11967209243602103139276691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15956278991469470852368921 11967209243602103139276691)
              ·
                refine ⟨17950813865403154708915037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11967209243602103139276691 17950813865403154708915037)
                ·
                  refine ⟨6731555199526183015843139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17950813865403154708915037 6731555199526183015843139)
                  ·
                    refine ⟨10097332799289274523764709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6731555199526183015843139 10097332799289274523764709)
                    ·
                      refine ⟨1893249899866738973205883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10097332799289274523764709 1893249899866738973205883)
                      ·
                        rfl

theorem cell23_3687091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 1, 3, 1, 4].length) (baseStart_3687091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3687091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3687091 prefixEnd_3687091 := by exact prefixLift 3687091
  have htrace : WordTrace (prefixWord ++ tailWord_3687091) baseStart_3687091 baseEnd_3687091 := by
    simpa [prefixWord, tailWord_3687091, baseEnd_3687091] using wordTrace_append hprefix tailTrace_3687091
  have hstable : (prefixWord ++ tailWord_3687091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687091).length < 2 ^ (prefixWord ++ tailWord_3687091).sum := by decide
  have hdescent : baseEnd_3687091 < baseStart_3687091 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687101 : List Nat := [1, 4, 1, 2, 1, 3, 2, 2, 1, 6]
def baseStart_3687101 : Nat := 118140960795 + 3687101 * 2 ^ 59
def prefixEnd_3687101 : Nat := 4983230072969 + 3 ^ 40 * 3687101 * 2
def baseEnd_3687101 : Nat := 631085011557761311360279

theorem tailTrace_3687101 : CollatzResearch.WordTrace tailWord_3687101 prefixEnd_3687101 631085011557761311360279 := by
  unfold tailWord_3687101
  simp only [CollatzResearch.WordTrace]
  refine ⟨134479621415270258562397157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89653080943513505708264771 134479621415270258562397157)
  ·
    refine ⟨25214929015363173480449467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134479621415270258562397157 25214929015363173480449467)
    ·
      refine ⟨37822393523044760220674201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25214929015363173480449467 37822393523044760220674201)
      ·
        refine ⟨28366795142283570165505651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37822393523044760220674201 28366795142283570165505651)
        ·
          refine ⟨42550192713425355248258477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28366795142283570165505651 42550192713425355248258477)
          ·
            refine ⟨15956322267534508218096929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42550192713425355248258477 15956322267534508218096929)
            ·
              refine ⟨11967241700650881163572697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15956322267534508218096929 11967241700650881163572697)
              ·
                refine ⟨8975431275488160872679523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11967241700650881163572697 8975431275488160872679523)
                ·
                  refine ⟨13463146913232241309019285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8975431275488160872679523 13463146913232241309019285)
                  ·
                    refine ⟨631085011557761311360279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13463146913232241309019285 631085011557761311360279)
                    ·
                      rfl

theorem cell23_3687101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 2, 1, 6].length) (baseStart_3687101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3687101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3687101 prefixEnd_3687101 := by exact prefixLift 3687101
  have htrace : WordTrace (prefixWord ++ tailWord_3687101) baseStart_3687101 baseEnd_3687101 := by
    simpa [prefixWord, tailWord_3687101, baseEnd_3687101] using wordTrace_append hprefix tailTrace_3687101
  have hstable : (prefixWord ++ tailWord_3687101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687101).length < 2 ^ (prefixWord ++ tailWord_3687101).sum := by decide
  have hdescent : baseEnd_3687101 < baseStart_3687101 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687102 : List Nat := [4, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3]
def baseStart_3687102 : Nat := 118140960795 + 3687102 * 2 ^ 59
def prefixEnd_3687102 : Nat := 4983230072969 + 3 ^ 40 * 3687102 * 2
def baseEnd_3687102 : Nat := 1893255548153938430168333

theorem tailTrace_3687102 : CollatzResearch.WordTrace tailWord_3687102 prefixEnd_3687102 1893255548153938430168333 := by
  unfold tailWord_3687102
  simp only [CollatzResearch.WordTrace]
  refine ⟨16809957236033329466647945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89653105258844423822122373 16809957236033329466647945)
  ·
    refine ⟨12607467927024997099985959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16809957236033329466647945 12607467927024997099985959)
    ·
      refine ⟨18911201890537495649978939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12607467927024997099985959 18911201890537495649978939)
      ·
        refine ⟨28366802835806243474968409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18911201890537495649978939 28366802835806243474968409)
        ·
          refine ⟨21275102126854682606226307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28366802835806243474968409 21275102126854682606226307)
          ·
            refine ⟨31912653190282023909339461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21275102126854682606226307 31912653190282023909339461)
            ·
              refine ⟨5983622473177879483001149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31912653190282023909339461 5983622473177879483001149)
              ·
                refine ⟨2243858427441704806125431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5983622473177879483001149 2243858427441704806125431)
                ·
                  refine ⟨3365787641162557209188147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2243858427441704806125431 3365787641162557209188147)
                  ·
                    refine ⟨5048681461743835813782221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3365787641162557209188147 5048681461743835813782221)
                    ·
                      refine ⟨1893255548153938430168333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5048681461743835813782221 1893255548153938430168333)
                      ·
                        rfl

theorem cell23_3687102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3].length) (baseStart_3687102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3687102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3687102 prefixEnd_3687102 := by exact prefixLift 3687102
  have htrace : WordTrace (prefixWord ++ tailWord_3687102) baseStart_3687102 baseEnd_3687102 := by
    simpa [prefixWord, tailWord_3687102, baseEnd_3687102] using wordTrace_append hprefix tailTrace_3687102
  have hstable : (prefixWord ++ tailWord_3687102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687102).length < 2 ^ (prefixWord ++ tailWord_3687102).sum := by decide
  have hdescent : baseEnd_3687102 < baseStart_3687102 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687111 : List Nat := [1, 1, 4, 1, 1, 1, 2, 2, 5, 2, 3]
def baseStart_3687111 : Nat := 118140960795 + 3687111 * 2 ^ 59
def prefixEnd_3687111 : Nat := 4983230072969 + 3 ^ 40 * 3687111 * 2
def baseEnd_3687111 : Nat := 1893260169479828894955791

theorem tailTrace_3687111 : CollatzResearch.WordTrace tailWord_3687111 prefixEnd_3687111 1893260169479828894955791 := by
  unfold tailWord_3687111
  simp only [CollatzResearch.WordTrace]
  refine ⟨134479986145234030270261187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89653324096822686846840791 134479986145234030270261187)
  ·
    refine ⟨201719979217851045405391781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134479986145234030270261187 201719979217851045405391781)
    ·
      refine ⟨37822496103347071013510959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 201719979217851045405391781 37822496103347071013510959)
      ·
        refine ⟨56733744155020606520266439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37822496103347071013510959 56733744155020606520266439)
        ·
          refine ⟨85100616232530909780399659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56733744155020606520266439 85100616232530909780399659)
          ·
            refine ⟨127650924348796364670599489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85100616232530909780399659 127650924348796364670599489)
            ·
              refine ⟨95738193261597273502949617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127650924348796364670599489 95738193261597273502949617)
              ·
                refine ⟨71803644946197955127212213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95738193261597273502949617 71803644946197955127212213)
                ·
                  refine ⟨6731591713706058293176145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71803644946197955127212213 6731591713706058293176145)
                  ·
                    refine ⟨5048693785279543719882109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6731591713706058293176145 5048693785279543719882109)
                    ·
                      refine ⟨1893260169479828894955791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5048693785279543719882109 1893260169479828894955791)
                      ·
                        rfl

theorem cell23_3687111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 5, 2, 3].length) (baseStart_3687111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3687111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3687111 prefixEnd_3687111 := by exact prefixLift 3687111
  have htrace : WordTrace (prefixWord ++ tailWord_3687111) baseStart_3687111 baseEnd_3687111 := by
    simpa [prefixWord, tailWord_3687111, baseEnd_3687111] using wordTrace_append hprefix tailTrace_3687111
  have hstable : (prefixWord ++ tailWord_3687111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687111).length < 2 ^ (prefixWord ++ tailWord_3687111).sum := by decide
  have hdescent : baseEnd_3687111 < baseStart_3687111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687118 : List Nat := [4, 1, 1, 1, 3, 3, 1, 1, 4, 4]
def baseStart_3687118 : Nat := 118140960795 + 3687118 * 2 ^ 59
def prefixEnd_3687118 : Nat := 4983230072969 + 3 ^ 40 * 3687118 * 2
def baseEnd_3687118 : Nat := 631087921281470122522753

theorem tailTrace_3687118 : CollatzResearch.WordTrace tailWord_3687118 prefixEnd_3687118 631087921281470122522753 := by
  unfold tailWord_3687118
  simp only [CollatzResearch.WordTrace]
  refine ⟨16810030182026083808220751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89653494304139113643844005 16810030182026083808220751)
  ·
    refine ⟨25215045273039125712331127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16810030182026083808220751 25215045273039125712331127)
    ·
      refine ⟨37822567909558688568496691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25215045273039125712331127 37822567909558688568496691)
      ·
        refine ⟨56733851864338032852745037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37822567909558688568496691 56733851864338032852745037)
        ·
          refine ⟨21275194449126762319779389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56733851864338032852745037 21275194449126762319779389)
          ·
            refine ⟨7978197918422535869917271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21275194449126762319779389 7978197918422535869917271)
            ·
              refine ⟨11967296877633803804875907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7978197918422535869917271 11967296877633803804875907)
              ·
                refine ⟨17950945316450705707313861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11967296877633803804875907 17950945316450705707313861)
                ·
                  refine ⟨3365802246834507320121349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17950945316450705707313861 3365802246834507320121349)
                  ·
                    refine ⟨631087921281470122522753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3365802246834507320121349 631087921281470122522753)
                    ·
                      rfl

theorem cell23_3687118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 1, 4, 4].length) (baseStart_3687118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3687118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3687118 prefixEnd_3687118 := by exact prefixLift 3687118
  have htrace : WordTrace (prefixWord ++ tailWord_3687118) baseStart_3687118 baseEnd_3687118 := by
    simpa [prefixWord, tailWord_3687118, baseEnd_3687118] using wordTrace_append hprefix tailTrace_3687118
  have hstable : (prefixWord ++ tailWord_3687118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687118).length < 2 ^ (prefixWord ++ tailWord_3687118).sum := by decide
  have hdescent : baseEnd_3687118 < baseStart_3687118 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687135 : List Nat := [1, 1, 2, 3, 2, 4, 3, 1, 2, 4]
def baseStart_3687135 : Nat := 118140960795 + 3687135 * 2 ^ 59
def prefixEnd_3687135 : Nat := 4983230072969 + 3 ^ 40 * 3687135 * 2
def baseEnd_3687135 : Nat := 631090831005178933685227

theorem tailTrace_3687135 : CollatzResearch.WordTrace tailWord_3687135 prefixEnd_3687135 631090831005178933685227 := by
  unfold tailWord_3687135
  simp only [CollatzResearch.WordTrace]
  refine ⟨134480861497147082369134859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89653907664764721579423239 134480861497147082369134859)
  ·
    refine ⟨201721292245720623553702289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134480861497147082369134859 201721292245720623553702289)
    ·
      refine ⟨151290969184290467665276717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201721292245720623553702289 151290969184290467665276717)
      ·
        refine ⟨56734113444108925374478769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151290969184290467665276717 56734113444108925374478769)
        ·
          refine ⟨42550585083081694030859077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56734113444108925374478769 42550585083081694030859077)
          ·
            refine ⟨7978234703077817630786077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42550585083081694030859077 7978234703077817630786077)
            ·
              refine ⟨2991838013654181611544779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7978234703077817630786077 2991838013654181611544779)
              ·
                refine ⟨4487757020481272417317169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2991838013654181611544779 4487757020481272417317169)
                ·
                  refine ⟨3365817765360954312987877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4487757020481272417317169 3365817765360954312987877)
                  ·
                    refine ⟨631090831005178933685227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3365817765360954312987877 631090831005178933685227)
                    ·
                      rfl

theorem cell23_3687135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 3, 1, 2, 4].length) (baseStart_3687135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3687135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3687135 prefixEnd_3687135 := by exact prefixLift 3687135
  have htrace : WordTrace (prefixWord ++ tailWord_3687135) baseStart_3687135 baseEnd_3687135 := by
    simpa [prefixWord, tailWord_3687135, baseEnd_3687135] using wordTrace_append hprefix tailTrace_3687135
  have hstable : (prefixWord ++ tailWord_3687135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687135).length < 2 ^ (prefixWord ++ tailWord_3687135).sum := by decide
  have hdescent : baseEnd_3687135 < baseStart_3687135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687158 : List Nat := [5, 1, 1, 1, 1, 2, 2, 1, 3, 3, 3]
def baseStart_3687158 : Nat := 118140960795 + 3687158 * 2 ^ 59
def prefixEnd_3687158 : Nat := 4983230072969 + 3 ^ 40 * 3687158 * 2
def baseEnd_3687158 : Nat := 1893284303070590211068075

theorem tailTrace_3687158 : CollatzResearch.WordTrace tailWord_3687158 prefixEnd_3687158 1893284303070590211068075 := by
  unfold tailWord_3687158
  simp only [CollatzResearch.WordTrace]
  refine ⟨8405106273503984831076383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89654466917375838198148085 8405106273503984831076383)
  ·
    refine ⟨12607659410255977246614575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8405106273503984831076383 12607659410255977246614575)
    ·
      refine ⟨18911489115383965869921863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12607659410255977246614575 18911489115383965869921863)
      ·
        refine ⟨28367233673075948804882795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18911489115383965869921863 28367233673075948804882795)
        ·
          refine ⟨42550850509613923207324193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28367233673075948804882795 42550850509613923207324193)
          ·
            refine ⟨31913137882210442405493145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42550850509613923207324193 31913137882210442405493145)
            ·
              refine ⟨23934853411657831804119859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31913137882210442405493145 23934853411657831804119859)
              ·
                refine ⟨35902280117486747706179789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23934853411657831804119859 35902280117486747706179789)
                ·
                  refine ⟨13463355044057530389817421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35902280117486747706179789 13463355044057530389817421)
                  ·
                    refine ⟨5048758141521573896181533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13463355044057530389817421 5048758141521573896181533)
                    ·
                      refine ⟨1893284303070590211068075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5048758141521573896181533 1893284303070590211068075)
                      ·
                        rfl

theorem cell23_3687158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 3, 3, 3].length) (baseStart_3687158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3687158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3687158 prefixEnd_3687158 := by exact prefixLift 3687158
  have htrace : WordTrace (prefixWord ++ tailWord_3687158) baseStart_3687158 baseEnd_3687158 := by
    simpa [prefixWord, tailWord_3687158, baseEnd_3687158] using wordTrace_append hprefix tailTrace_3687158
  have hstable : (prefixWord ++ tailWord_3687158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687158).length < 2 ^ (prefixWord ++ tailWord_3687158).sum := by decide
  have hdescent : baseEnd_3687158 < baseStart_3687158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687175 : List Nat := [1, 1, 4, 4, 1, 1, 2, 1, 4, 1, 3]
def baseStart_3687175 : Nat := 118140960795 + 3687175 * 2 ^ 59
def prefixEnd_3687175 : Nat := 4983230072969 + 3 ^ 40 * 3687175 * 2
def baseEnd_3687175 : Nat := 1893293032241716644555497

theorem tailTrace_3687175 : CollatzResearch.WordTrace tailWord_3687175 prefixEnd_3687175 1893293032241716644555497 := by
  unfold tailWord_3687175
  simp only [CollatzResearch.WordTrace]
  refine ⟨134482320417002169200590979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89654880278001446133727319 134482320417002169200590979)
  ·
    refine ⟨201723480625503253800886469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134482320417002169200590979 201723480625503253800886469)
    ·
      refine ⟨37823152617281860087666213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 201723480625503253800886469 37823152617281860087666213)
      ·
        refine ⟨7091841115740348766437415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37823152617281860087666213 7091841115740348766437415)
        ·
          refine ⟨10637761673610523149656123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7091841115740348766437415 10637761673610523149656123)
          ·
            refine ⟨15956642510415784724484185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10637761673610523149656123 15956642510415784724484185)
            ·
              refine ⟨11967481882811838543363139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15956642510415784724484185 11967481882811838543363139)
              ·
                refine ⟨17951222824217757815044709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11967481882811838543363139 17951222824217757815044709)
                ·
                  refine ⟨3365854279540829590320883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17951222824217757815044709 3365854279540829590320883)
                  ·
                    refine ⟨5048781419311244385481325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3365854279540829590320883 5048781419311244385481325)
                    ·
                      refine ⟨1893293032241716644555497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5048781419311244385481325 1893293032241716644555497)
                      ·
                        rfl

theorem cell23_3687175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_3687175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3687175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3687175 prefixEnd_3687175 := by exact prefixLift 3687175
  have htrace : WordTrace (prefixWord ++ tailWord_3687175) baseStart_3687175 baseEnd_3687175 := by
    simpa [prefixWord, tailWord_3687175, baseEnd_3687175] using wordTrace_append hprefix tailTrace_3687175
  have hstable : (prefixWord ++ tailWord_3687175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687175).length < 2 ^ (prefixWord ++ tailWord_3687175).sum := by decide
  have hdescent : baseEnd_3687175 < baseStart_3687175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687186 : List Nat := [3, 2, 4, 1, 3, 1, 2, 1, 2, 4]
def baseStart_3687186 : Nat := 118140960795 + 3687186 * 2 ^ 59
def prefixEnd_3687186 : Nat := 4983230072969 + 3 ^ 40 * 3687186 * 2
def baseEnd_3687186 : Nat := 631099560176305367172649

theorem tailTrace_3687186 : CollatzResearch.WordTrace tailWord_3687186 prefixEnd_3687186 631099560176305367172649 := by
  unfold tailWord_3687186
  simp only [CollatzResearch.WordTrace]
  refine ⟨33620680404990579519810353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89655147746641545386160941 33620680404990579519810353)
  ·
    refine ⟨25215510303742934639857765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33620680404990579519810353 25215510303742934639857765)
    ·
      refine ⟨4727908181951800244973331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25215510303742934639857765 4727908181951800244973331)
      ·
        refine ⟨7091862272927700367459997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4727908181951800244973331 7091862272927700367459997)
        ·
          refine ⟨2659448352347887637797499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7091862272927700367459997 2659448352347887637797499)
          ·
            refine ⟨3989172528521831456696249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2659448352347887637797499 3989172528521831456696249)
            ·
              refine ⟨2991879396391373592522187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3989172528521831456696249 2991879396391373592522187)
              ·
                refine ⟨4487819094587060388783281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2991879396391373592522187 4487819094587060388783281)
                ·
                  refine ⟨3365864320940295291587461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4487819094587060388783281 3365864320940295291587461)
                  ·
                    refine ⟨631099560176305367172649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3365864320940295291587461 631099560176305367172649)
                    ·
                      rfl

theorem cell23_3687186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_3687186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3687186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3687186 prefixEnd_3687186 := by exact prefixLift 3687186
  have htrace : WordTrace (prefixWord ++ tailWord_3687186) baseStart_3687186 baseEnd_3687186 := by
    simpa [prefixWord, tailWord_3687186, baseEnd_3687186] using wordTrace_append hprefix tailTrace_3687186
  have hstable : (prefixWord ++ tailWord_3687186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687186).length < 2 ^ (prefixWord ++ tailWord_3687186).sum := by decide
  have hdescent : baseEnd_3687186 < baseStart_3687186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687201 : List Nat := [1, 2, 3, 2, 1, 2, 1, 1, 4, 1, 5]
def baseStart_3687201 : Nat := 118140960795 + 3687201 * 2 ^ 59
def prefixEnd_3687201 : Nat := 4983230072969 + 3 ^ 40 * 3687201 * 2
def baseEnd_3687201 : Nat := 1893306382738733542830377

theorem tailTrace_3687201 : CollatzResearch.WordTrace tailWord_3687201 prefixEnd_3687201 1893306382738733542830377 := by
  unfold tailWord_3687201
  simp only [CollatzResearch.WordTrace]
  refine ⟨134483268714907975641037457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89655512476605317094024971 134483268714907975641037457)
  ·
    refine ⟨100862451536180981730778093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134483268714907975641037457 100862451536180981730778093)
    ·
      refine ⟨37823419326067868149041785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100862451536180981730778093 37823419326067868149041785)
      ·
        refine ⟨28367564494550901111781339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37823419326067868149041785 28367564494550901111781339)
        ·
          refine ⟨42551346741826351667672009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28367564494550901111781339 42551346741826351667672009)
          ·
            refine ⟨31913510056369763750754007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42551346741826351667672009 31913510056369763750754007)
            ·
              refine ⟨47870265084554645626131011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31913510056369763750754007 47870265084554645626131011)
              ·
                refine ⟨71805397626831968439196517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47870265084554645626131011 71805397626831968439196517)
                ·
                  refine ⟨13463512055030994082349347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71805397626831968439196517 13463512055030994082349347)
                  ·
                    refine ⟨20195268082546491123524021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13463512055030994082349347 20195268082546491123524021)
                    ·
                      refine ⟨1893306382738733542830377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20195268082546491123524021 1893306382738733542830377)
                      ·
                        rfl

theorem cell23_3687201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_3687201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3687201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3687201 prefixEnd_3687201 := by exact prefixLift 3687201
  have htrace : WordTrace (prefixWord ++ tailWord_3687201) baseStart_3687201 baseEnd_3687201 := by
    simpa [prefixWord, tailWord_3687201, baseEnd_3687201] using wordTrace_append hprefix tailTrace_3687201
  have hstable : (prefixWord ++ tailWord_3687201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687201).length < 2 ^ (prefixWord ++ tailWord_3687201).sum := by decide
  have hdescent : baseEnd_3687201 < baseStart_3687201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687202 : List Nat := [3, 3, 1, 1, 2, 2, 3, 2, 1, 3, 2]
def baseStart_3687202 : Nat := 118140960795 + 3687202 * 2 ^ 59
def prefixEnd_3687202 : Nat := 4983230072969 + 3 ^ 40 * 3687202 * 2
def baseEnd_3687202 : Nat := 1893306896219388038917873

theorem tailTrace_3687202 : CollatzResearch.WordTrace tailWord_3687202 prefixEnd_3687202 1893306896219388038917873 := by
  unfold tailWord_3687202
  simp only [CollatzResearch.WordTrace]
  refine ⟨33620826296976088202955965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89655536791936235207882573 33620826296976088202955965)
  ·
    refine ⟨12607809861366033076108487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33620826296976088202955965 12607809861366033076108487)
    ·
      refine ⟨18911714792049049614162731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12607809861366033076108487 18911714792049049614162731)
      ·
        refine ⟨28367572188073574421244097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18911714792049049614162731 28367572188073574421244097)
        ·
          refine ⟨21275679141055180815933073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28367572188073574421244097 21275679141055180815933073)
          ·
            refine ⟨15956759355791385611949805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21275679141055180815933073 15956759355791385611949805)
            ·
              refine ⟨5983784758421769604481177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15956759355791385611949805 5983784758421769604481177)
              ·
                refine ⟨4487838568816327203360883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5983784758421769604481177 4487838568816327203360883)
                ·
                  refine ⟨6731757853224490805041325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4487838568816327203360883 6731757853224490805041325)
                  ·
                    refine ⟨2524409194959184051890497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6731757853224490805041325 2524409194959184051890497)
                    ·
                      refine ⟨1893306896219388038917873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2524409194959184051890497 1893306896219388038917873)
                      ·
                        rfl

theorem cell23_3687202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 2, 1, 3, 2].length) (baseStart_3687202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3687202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3687202 prefixEnd_3687202 := by exact prefixLift 3687202
  have htrace : WordTrace (prefixWord ++ tailWord_3687202) baseStart_3687202 baseEnd_3687202 := by
    simpa [prefixWord, tailWord_3687202, baseEnd_3687202] using wordTrace_append hprefix tailTrace_3687202
  have hstable : (prefixWord ++ tailWord_3687202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687202).length < 2 ^ (prefixWord ++ tailWord_3687202).sum := by decide
  have hdescent : baseEnd_3687202 < baseStart_3687202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687251 : List Nat := [1, 1, 1, 2, 1, 1, 3, 4, 4, 5]
def baseStart_3687251 : Nat := 118140960795 + 3687251 * 2 ^ 59
def prefixEnd_3687251 : Nat := 4983230072969 + 3 ^ 40 * 3687251 * 2
def baseEnd_3687251 : Nat := 631110685590486115735049

theorem tailTrace_3687251 : CollatzResearch.WordTrace tailWord_3687251 prefixEnd_3687251 631110685590486115735049 := by
  unfold tailWord_3687251
  simp only [CollatzResearch.WordTrace]
  refine ⟨134485092364726834180357607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89656728243151222786905071 134485092364726834180357607)
  ·
    refine ⟨201727638547090251270536411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134485092364726834180357607 201727638547090251270536411)
    ·
      refine ⟨302591457820635376905804617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201727638547090251270536411 302591457820635376905804617)
      ·
        refine ⟨226943593365476532679353463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302591457820635376905804617 226943593365476532679353463)
        ·
          refine ⟨340415390048214799019030195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226943593365476532679353463 340415390048214799019030195)
          ·
            refine ⟨510623085072322198528545293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340415390048214799019030195 510623085072322198528545293)
            ·
              refine ⟨191483656902120824448204485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 510623085072322198528545293 191483656902120824448204485)
              ·
                refine ⟨35903185669147654584038341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 191483656902120824448204485 35903185669147654584038341)
                ·
                  refine ⟨6731847312965185234507189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35903185669147654584038341 6731847312965185234507189)
                  ·
                    refine ⟨631110685590486115735049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6731847312965185234507189 631110685590486115735049)
                    ·
                      rfl

theorem cell23_3687251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 4, 5].length) (baseStart_3687251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3687251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3687251 prefixEnd_3687251 := by exact prefixLift 3687251
  have htrace : WordTrace (prefixWord ++ tailWord_3687251) baseStart_3687251 baseEnd_3687251 := by
    simpa [prefixWord, tailWord_3687251, baseEnd_3687251] using wordTrace_append hprefix tailTrace_3687251
  have hstable : (prefixWord ++ tailWord_3687251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687251).length < 2 ^ (prefixWord ++ tailWord_3687251).sum := by decide
  have hdescent : baseEnd_3687251 < baseStart_3687251 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687268 : List Nat := [2, 3, 1, 1, 4, 2, 1, 1, 1, 7]
def baseStart_3687268 : Nat := 118140960795 + 3687268 * 2 ^ 59
def prefixEnd_3687268 : Nat := 4983230072969 + 3 ^ 40 * 3687268 * 2
def baseEnd_3687268 : Nat := 631113595314194926897523

theorem tailTrace_3687268 : CollatzResearch.WordTrace tailWord_3687268 prefixEnd_3687268 631113595314194926897523 := by
  unfold tailWord_3687268
  simp only [CollatzResearch.WordTrace]
  refine ⟨67242856202832623041863229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89657141603776830722484305 67242856202832623041863229)
  ·
    refine ⟨25216071076062233640698711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67242856202832623041863229 25216071076062233640698711)
    ·
      refine ⟨37824106614093350461048067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25216071076062233640698711 37824106614093350461048067)
      ·
        refine ⟨56736159921140025691572101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37824106614093350461048067 56736159921140025691572101)
        ·
          refine ⟨10638029985213754817169769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56736159921140025691572101 10638029985213754817169769)
          ·
            refine ⟨7978522488910316112877327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10638029985213754817169769 7978522488910316112877327)
            ·
              refine ⟨11967783733365474169315991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7978522488910316112877327 11967783733365474169315991)
              ·
                refine ⟨17951675600048211253973987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11967783733365474169315991 17951675600048211253973987)
                ·
                  refine ⟨26927513400072316880960981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17951675600048211253973987 26927513400072316880960981)
                  ·
                    refine ⟨631113595314194926897523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26927513400072316880960981 631113595314194926897523)
                    ·
                      rfl

theorem cell23_3687268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 1, 1, 7].length) (baseStart_3687268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3687268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3687268 prefixEnd_3687268 := by exact prefixLift 3687268
  have htrace : WordTrace (prefixWord ++ tailWord_3687268) baseStart_3687268 baseEnd_3687268 := by
    simpa [prefixWord, tailWord_3687268, baseEnd_3687268] using wordTrace_append hprefix tailTrace_3687268
  have hstable : (prefixWord ++ tailWord_3687268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687268).length < 2 ^ (prefixWord ++ tailWord_3687268).sum := by decide
  have hdescent : baseEnd_3687268 < baseStart_3687268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687291 : List Nat := [1, 1, 1, 1, 1, 5, 2, 1, 2, 3, 5]
def baseStart_3687291 : Nat := 118140960795 + 3687291 * 2 ^ 59
def prefixEnd_3687291 : Nat := 4983230072969 + 3 ^ 40 * 3687291 * 2
def baseEnd_3687291 : Nat := 1893352595997638190704963

theorem tailTrace_3687291 : CollatzResearch.WordTrace tailWord_3687291 prefixEnd_3687291 1893352595997638190704963 := by
  unfold tailWord_3687291
  simp only [CollatzResearch.WordTrace]
  refine ⟨134486551284581921011813727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89657700856387947341209151 134486551284581921011813727)
  ·
    refine ⟨201729826926872881517720591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134486551284581921011813727 201729826926872881517720591)
    ·
      refine ⟨302594740390309322276580887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201729826926872881517720591 302594740390309322276580887)
      ·
        refine ⟨453892110585463983414871331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302594740390309322276580887 453892110585463983414871331)
        ·
          refine ⟨680838165878195975122306997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 453892110585463983414871331 680838165878195975122306997)
          ·
            refine ⟨63828578051080872667716281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 680838165878195975122306997 63828578051080872667716281)
            ·
              refine ⟨47871433538310654500787211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63828578051080872667716281 47871433538310654500787211)
              ·
                refine ⟨71807150307465981751180817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47871433538310654500787211 71807150307465981751180817)
                ·
                  refine ⟨53855362730599486313385613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71807150307465981751180817 53855362730599486313385613)
                  ·
                    refine ⟨20195761023974807367519605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53855362730599486313385613 20195761023974807367519605)
                    ·
                      refine ⟨1893352595997638190704963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20195761023974807367519605 1893352595997638190704963)
                      ·
                        rfl

theorem cell23_3687291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 3, 5].length) (baseStart_3687291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3687291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3687291 prefixEnd_3687291 := by exact prefixLift 3687291
  have htrace : WordTrace (prefixWord ++ tailWord_3687291) baseStart_3687291 baseEnd_3687291 := by
    simpa [prefixWord, tailWord_3687291, baseEnd_3687291] using wordTrace_append hprefix tailTrace_3687291
  have hstable : (prefixWord ++ tailWord_3687291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687291).length < 2 ^ (prefixWord ++ tailWord_3687291).sum := by decide
  have hdescent : baseEnd_3687291 < baseStart_3687291 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687305 : List Nat := [1, 2, 1, 1, 5, 2, 2, 1, 2, 4, 2]
def baseStart_3687305 : Nat := 118140960795 + 3687305 * 2 ^ 59
def prefixEnd_3687305 : Nat := 4983230072969 + 3 ^ 40 * 3687305 * 2
def baseEnd_3687305 : Nat := 1893359784726801135929899

theorem tailTrace_3687305 : CollatzResearch.WordTrace tailWord_3687305 prefixEnd_3687305 1893359784726801135929899 := by
  unfold tailWord_3687305
  simp only [CollatzResearch.WordTrace]
  refine ⟨134487061906531201402823369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89658041271020800935215579 134487061906531201402823369)
  ·
    refine ⟨100865296429898401052117527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134487061906531201402823369 100865296429898401052117527)
    ·
      refine ⟨151297944644847601578176291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100865296429898401052117527 151297944644847601578176291)
      ·
        refine ⟨226946916967271402367264437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151297944644847601578176291 226946916967271402367264437)
        ·
          refine ⟨21276273465681693971931041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 226946916967271402367264437 21276273465681693971931041)
          ·
            refine ⟨15957205099261270478948281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21276273465681693971931041 15957205099261270478948281)
            ·
              refine ⟨11967903824445952859211211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15957205099261270478948281 11967903824445952859211211)
              ·
                refine ⟨17951855736668929288816817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11967903824445952859211211 17951855736668929288816817)
                ·
                  refine ⟨13463891802501696966612613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17951855736668929288816817 13463891802501696966612613)
                  ·
                    refine ⟨2524479712969068181239865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13463891802501696966612613 2524479712969068181239865)
                    ·
                      refine ⟨1893359784726801135929899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2524479712969068181239865 1893359784726801135929899)
                      ·
                        rfl

theorem cell23_3687305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 1, 2, 4, 2].length) (baseStart_3687305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3687305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3687305 prefixEnd_3687305 := by exact prefixLift 3687305
  have htrace : WordTrace (prefixWord ++ tailWord_3687305) baseStart_3687305 baseEnd_3687305 := by
    simpa [prefixWord, tailWord_3687305, baseEnd_3687305] using wordTrace_append hprefix tailTrace_3687305
  have hstable : (prefixWord ++ tailWord_3687305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687305).length < 2 ^ (prefixWord ++ tailWord_3687305).sum := by decide
  have hdescent : baseEnd_3687305 < baseStart_3687305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687308 : List Nat := [2, 2, 1, 2, 1, 2, 3, 2, 1, 4, 3]
def baseStart_3687308 : Nat := 118140960795 + 3687308 * 2 ^ 59
def prefixEnd_3687308 : Nat := 4983230072969 + 3 ^ 40 * 3687308 * 2
def baseEnd_3687308 : Nat := 1893361325168764624192385

theorem tailTrace_3687308 : CollatzResearch.WordTrace tailWord_3687308 prefixEnd_3687308 1893361325168764624192385 := by
  unfold tailWord_3687308
  simp only [CollatzResearch.WordTrace]
  refine ⟨67243585662760166457591289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89658114217013555276788385 67243585662760166457591289)
  ·
    refine ⟨50432689247070124843193467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67243585662760166457591289 50432689247070124843193467)
    ·
      refine ⟨75649033870605187264790201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50432689247070124843193467 75649033870605187264790201)
      ·
        refine ⟨56736775402953890448592651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75649033870605187264790201 56736775402953890448592651)
        ·
          refine ⟨85105163104430835672888977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56736775402953890448592651 85105163104430835672888977)
          ·
            refine ⟨63828872328323126754666733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85105163104430835672888977 63828872328323126754666733)
            ·
              refine ⟨23935827123121172533000025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63828872328323126754666733 23935827123121172533000025)
              ·
                refine ⟨17951870342340879399750019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23935827123121172533000025 17951870342340879399750019)
                ·
                  refine ⟨26927805513511319099625029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17951870342340879399750019 26927805513511319099625029)
                  ·
                    refine ⟨5048963533783372331179693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26927805513511319099625029 5048963533783372331179693)
                    ·
                      refine ⟨1893361325168764624192385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5048963533783372331179693 1893361325168764624192385)
                      ·
                        rfl

theorem cell23_3687308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2, 1, 4, 3].length) (baseStart_3687308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3687308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3687308 prefixEnd_3687308 := by exact prefixLift 3687308
  have htrace : WordTrace (prefixWord ++ tailWord_3687308) baseStart_3687308 baseEnd_3687308 := by
    simpa [prefixWord, tailWord_3687308, baseEnd_3687308] using wordTrace_append hprefix tailTrace_3687308
  have hstable : (prefixWord ++ tailWord_3687308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687308).length < 2 ^ (prefixWord ++ tailWord_3687308).sum := by decide
  have hdescent : baseEnd_3687308 < baseStart_3687308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687325 : List Nat := [1, 4, 2, 1, 2, 1, 2, 3, 2, 2, 3]
def baseStart_3687325 : Nat := 118140960795 + 3687325 * 2 ^ 59
def prefixEnd_3687325 : Nat := 4983230072969 + 3 ^ 40 * 3687325 * 2
def baseEnd_3687325 : Nat := 1893370054339891057679807

theorem tailTrace_3687325 : CollatzResearch.WordTrace tailWord_3687325 prefixEnd_3687325 1893370054339891057679807 := by
  unfold tailWord_3687325
  simp only [CollatzResearch.WordTrace]
  refine ⟨134487791366458744818551429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89658527577639163212367619 134487791366458744818551429)
  ·
    refine ⟨25216460881211014653478393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134487791366458744818551429 25216460881211014653478393)
    ·
      refine ⟨18912345660908260990108795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25216460881211014653478393 18912345660908260990108795)
      ·
        refine ⟨28368518491362391485163193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18912345660908260990108795 28368518491362391485163193)
        ·
          refine ⟨21276388868521793613872395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28368518491362391485163193 21276388868521793613872395)
          ·
            refine ⟨31914583302782690420808593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21276388868521793613872395 31914583302782690420808593)
            ·
              refine ⟨23935937477087017815606445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31914583302782690420808593 23935937477087017815606445)
              ·
                refine ⟨8975976553907631680852417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23935937477087017815606445 8975976553907631680852417)
                ·
                  refine ⟨6731982415430723760639313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8975976553907631680852417 6731982415430723760639313)
                  ·
                    refine ⟨5048986811573042820479485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6731982415430723760639313 5048986811573042820479485)
                    ·
                      refine ⟨1893370054339891057679807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5048986811573042820479485 1893370054339891057679807)
                      ·
                        rfl

theorem cell23_3687325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 3, 2, 2, 3].length) (baseStart_3687325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3687325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3687325 prefixEnd_3687325 := by exact prefixLift 3687325
  have htrace : WordTrace (prefixWord ++ tailWord_3687325) baseStart_3687325 baseEnd_3687325 := by
    simpa [prefixWord, tailWord_3687325, baseEnd_3687325] using wordTrace_append hprefix tailTrace_3687325
  have hstable : (prefixWord ++ tailWord_3687325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687325).length < 2 ^ (prefixWord ++ tailWord_3687325).sum := by decide
  have hdescent : baseEnd_3687325 < baseStart_3687325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687349 : List Nat := [1, 3, 3, 2, 1, 1, 5, 2, 1, 4]
def baseStart_3687349 : Nat := 118140960795 + 3687349 * 2 ^ 59
def prefixEnd_3687349 : Nat := 4983230072969 + 3 ^ 40 * 3687349 * 2
def baseEnd_3687349 : Nat := 631127459291866321259899

theorem tailTrace_3687349 : CollatzResearch.WordTrace tailWord_3687349 prefixEnd_3687349 631127459291866321259899 := by
  unfold tailWord_3687349
  simp only [CollatzResearch.WordTrace]
  refine ⟨134488666718371796917425101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89659111145581197944950067 134488666718371796917425101)
  ·
    refine ⟨50433250019389423844034413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134488666718371796917425101 50433250019389423844034413)
    ·
      refine ⟨18912468757271033941512905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50433250019389423844034413 18912468757271033941512905)
      ·
        refine ⟨14184351567953275456134679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18912468757271033941512905 14184351567953275456134679)
        ·
          refine ⟨21276527351929913184202019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14184351567953275456134679 21276527351929913184202019)
          ·
            refine ⟨31914791027894869776303029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21276527351929913184202019 31914791027894869776303029)
            ·
              refine ⟨2992011658865144041528409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31914791027894869776303029 2992011658865144041528409)
              ·
                refine ⟨2244008744148858031146307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2992011658865144041528409 2244008744148858031146307)
                ·
                  refine ⟨3366013116223287046719461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2244008744148858031146307 3366013116223287046719461)
                  ·
                    refine ⟨631127459291866321259899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3366013116223287046719461 631127459291866321259899)
                    ·
                      rfl

theorem cell23_3687349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 5, 2, 1, 4].length) (baseStart_3687349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3687349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3687349 prefixEnd_3687349 := by exact prefixLift 3687349
  have htrace : WordTrace (prefixWord ++ tailWord_3687349) baseStart_3687349 baseEnd_3687349 := by
    simpa [prefixWord, tailWord_3687349, baseEnd_3687349] using wordTrace_append hprefix tailTrace_3687349
  have hstable : (prefixWord ++ tailWord_3687349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687349).length < 2 ^ (prefixWord ++ tailWord_3687349).sum := by decide
  have hdescent : baseEnd_3687349 < baseStart_3687349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687375 : List Nat := [1, 1, 2, 1, 1, 6, 3, 2, 1, 5]
def baseStart_3687375 : Nat := 118140960795 + 3687375 * 2 ^ 59
def prefixEnd_3687375 : Nat := 4983230072969 + 3 ^ 40 * 3687375 * 2
def baseEnd_3687375 : Nat := 631131909457538620684859

theorem tailTrace_3687375 : CollatzResearch.WordTrace tailWord_3687375 prefixEnd_3687375 631131909457538620684859 := by
  unfold tailWord_3687375
  simp only [CollatzResearch.WordTrace]
  refine ⟨134489615016277603357871579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89659743344185068905247719 134489615016277603357871579)
  ·
    refine ⟨201734422524416405036807369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134489615016277603357871579 201734422524416405036807369)
    ·
      refine ⟨151300816893312303777605527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201734422524416405036807369 151300816893312303777605527)
      ·
        refine ⟨226951225339968455666408291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151300816893312303777605527 226951225339968455666408291)
        ·
          refine ⟨340426838009952683499612437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226951225339968455666408291 340426838009952683499612437)
          ·
            refine ⟨15957508031716532039044333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 340426838009952683499612437 15957508031716532039044333)
            ·
              refine ⟨5984065511893699514641625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15957508031716532039044333 5984065511893699514641625)
              ·
                refine ⟨4488049133920274635981219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5984065511893699514641625 4488049133920274635981219)
                ·
                  refine ⟨6732073700880411953971829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4488049133920274635981219 6732073700880411953971829)
                  ·
                    refine ⟨631131909457538620684859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6732073700880411953971829 631131909457538620684859)
                    ·
                      rfl

theorem cell23_3687375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 2, 1, 5].length) (baseStart_3687375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3687375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3687375 prefixEnd_3687375 := by exact prefixLift 3687375
  have htrace : WordTrace (prefixWord ++ tailWord_3687375) baseStart_3687375 baseEnd_3687375 := by
    simpa [prefixWord, tailWord_3687375, baseEnd_3687375] using wordTrace_append hprefix tailTrace_3687375
  have hstable : (prefixWord ++ tailWord_3687375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687375).length < 2 ^ (prefixWord ++ tailWord_3687375).sum := by decide
  have hdescent : baseEnd_3687375 < baseStart_3687375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687406 : List Nat := [4, 1, 2, 1, 4, 1, 1, 4, 1, 1, 3]
def baseStart_3687406 : Nat := 118140960795 + 3687406 * 2 ^ 59
def prefixEnd_3687406 : Nat := 4983230072969 + 3 ^ 40 * 3687406 * 2
def baseEnd_3687406 : Nat := 1893411646272905240766935

theorem tailTrace_3687406 : CollatzResearch.WordTrace tailWord_3687406 prefixEnd_3687406 1893411646272905240766935 := by
  unfold tailWord_3687406
  simp only [CollatzResearch.WordTrace]
  refine ⟨16811343209895661956531259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89660497119443530434833381 16811343209895661956531259)
  ·
    refine ⟨25217014814843492934796889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16811343209895661956531259 25217014814843492934796889)
    ·
      refine ⟨18912761111132619701097667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25217014814843492934796889 18912761111132619701097667)
      ·
        refine ⟨28369141666698929551646501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18912761111132619701097667 28369141666698929551646501)
        ·
          refine ⟨5319214062506049290933719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28369141666698929551646501 5319214062506049290933719)
          ·
            refine ⟨7978821093759073936400579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5319214062506049290933719 7978821093759073936400579)
            ·
              refine ⟨11968231640638610904600869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7978821093759073936400579 11968231640638610904600869)
              ·
                refine ⟨2244043432619739544612663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11968231640638610904600869 2244043432619739544612663)
                ·
                  refine ⟨3366065148929609316918995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2244043432619739544612663 3366065148929609316918995)
                  ·
                    refine ⟨5049097723394413975378493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3366065148929609316918995 5049097723394413975378493)
                    ·
                      refine ⟨1893411646272905240766935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5049097723394413975378493 1893411646272905240766935)
                      ·
                        rfl

theorem cell23_3687406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 4, 1, 1, 3].length) (baseStart_3687406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3687406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3687406 prefixEnd_3687406 := by exact prefixLift 3687406
  have htrace : WordTrace (prefixWord ++ tailWord_3687406) baseStart_3687406 baseEnd_3687406 := by
    simpa [prefixWord, tailWord_3687406, baseEnd_3687406] using wordTrace_append hprefix tailTrace_3687406
  have hstable : (prefixWord ++ tailWord_3687406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687406).length < 2 ^ (prefixWord ++ tailWord_3687406).sum := by decide
  have hdescent : baseEnd_3687406 < baseStart_3687406 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687408 : List Nat := [2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 4]
def baseStart_3687408 : Nat := 118140960795 + 3687408 * 2 ^ 59
def prefixEnd_3687408 : Nat := 4983230072969 + 3 ^ 40 * 3687408 * 2
def baseEnd_3687408 : Nat := 1893412673234214232941925

theorem tailTrace_3687408 : CollatzResearch.WordTrace tailWord_3687408 prefixEnd_3687408 1893412673234214232941925 := by
  unfold tailWord_3687408
  simp only [CollatzResearch.WordTrace]
  refine ⟨67245409312579024996911439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89660545750105366662548585 67245409312579024996911439)
  ·
    refine ⟨100868113968868537495367159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67245409312579024996911439 100868113968868537495367159)
    ·
      refine ⟨151302170953302806243050739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100868113968868537495367159 151302170953302806243050739)
      ·
        refine ⟨226953256429954209364576109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151302170953302806243050739 226953256429954209364576109)
        ·
          refine ⟨85107471161232828511716041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226953256429954209364576109 85107471161232828511716041)
          ·
            refine ⟨63830603370924621383787031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85107471161232828511716041 63830603370924621383787031)
            ·
              refine ⟨95745905056386932075680547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63830603370924621383787031 95745905056386932075680547)
              ·
                refine ⟨143618857584580398113520821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95745905056386932075680547 143618857584580398113520821)
                ·
                  refine ⟨13464267898554412323142577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 143618857584580398113520821 13464267898554412323142577)
                  ·
                    refine ⟨10098200923915809242356933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13464267898554412323142577 10098200923915809242356933)
                    ·
                      refine ⟨1893412673234214232941925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10098200923915809242356933 1893412673234214232941925)
                      ·
                        rfl

theorem cell23_3687408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 4].length) (baseStart_3687408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3687408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3687408 prefixEnd_3687408 := by exact prefixLift 3687408
  have htrace : WordTrace (prefixWord ++ tailWord_3687408) baseStart_3687408 baseEnd_3687408 := by
    simpa [prefixWord, tailWord_3687408, baseEnd_3687408] using wordTrace_append hprefix tailTrace_3687408
  have hstable : (prefixWord ++ tailWord_3687408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687408).length < 2 ^ (prefixWord ++ tailWord_3687408).sum := by decide
  have hdescent : baseEnd_3687408 < baseStart_3687408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687425 : List Nat := [1, 2, 4, 1, 2, 2, 1, 3, 1, 2, 4]
def baseStart_3687425 : Nat := 118140960795 + 3687425 * 2 ^ 59
def prefixEnd_3687425 : Nat := 4983230072969 + 3 ^ 40 * 3687425 * 2
def baseEnd_3687425 : Nat := 1893421402405340666429347

theorem tailTrace_3687425 : CollatzResearch.WordTrace tailWord_3687425 prefixEnd_3687425 1893421402405340666429347 := by
  unfold tailWord_3687425
  simp only [CollatzResearch.WordTrace]
  refine ⟨134491438666096461897191729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89660959110730974598127819 134491438666096461897191729)
  ·
    refine ⟨100868578999572346422893797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134491438666096461897191729 100868578999572346422893797)
    ·
      refine ⟨18912858562419814954292587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100868578999572346422893797 18912858562419814954292587)
      ·
        refine ⟨28369287843629722431438881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18912858562419814954292587 28369287843629722431438881)
        ·
          refine ⟨21276965882722291823579161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28369287843629722431438881 21276965882722291823579161)
          ·
            refine ⟨15957724412041718867684371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21276965882722291823579161 15957724412041718867684371)
            ·
              refine ⟨23936586618062578301526557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15957724412041718867684371 23936586618062578301526557)
              ·
                refine ⟨8976219981773466863072459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23936586618062578301526557 8976219981773466863072459)
                ·
                  refine ⟨13464329972660200294608689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8976219981773466863072459 13464329972660200294608689)
                  ·
                    refine ⟨10098247479495150220956517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13464329972660200294608689 10098247479495150220956517)
                    ·
                      refine ⟨1893421402405340666429347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10098247479495150220956517 1893421402405340666429347)
                      ·
                        rfl

theorem cell23_3687425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_3687425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3687425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3687425 prefixEnd_3687425 := by exact prefixLift 3687425
  have htrace : WordTrace (prefixWord ++ tailWord_3687425) baseStart_3687425 baseEnd_3687425 := by
    simpa [prefixWord, tailWord_3687425, baseEnd_3687425] using wordTrace_append hprefix tailTrace_3687425
  have hstable : (prefixWord ++ tailWord_3687425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687425).length < 2 ^ (prefixWord ++ tailWord_3687425).sum := by decide
  have hdescent : baseEnd_3687425 < baseStart_3687425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687435 : List Nat := [1, 1, 1, 1, 6, 3, 3, 7]
def baseStart_3687435 : Nat := 118140960795 + 3687435 * 2 ^ 59
def prefixEnd_3687435 : Nat := 4983230072969 + 3 ^ 40 * 3687435 * 2
def baseEnd_3687435 : Nat := 70126908785625393603863

theorem tailTrace_3687435 : CollatzResearch.WordTrace tailWord_3687435 prefixEnd_3687435 70126908785625393603863 := by
  unfold tailWord_3687435
  simp only [CollatzResearch.WordTrace]
  refine ⟨134491803396060233605055759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89661202264040155736703839 134491803396060233605055759)
  ·
    refine ⟨201737705094090350407583639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134491803396060233605055759 201737705094090350407583639)
    ·
      refine ⟨302606557641135525611375459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201737705094090350407583639 302606557641135525611375459)
      ·
        refine ⟨453909836461703288417063189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302606557641135525611375459 453909836461703288417063189)
        ·
          refine ⟨21277023584142341644549837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 453909836461703288417063189 21277023584142341644549837)
          ·
            refine ⟨7978883844053378116706189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21277023584142341644549837 7978883844053378116706189)
            ·
              refine ⟨2992081441520016793764821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7978883844053378116706189 2992081441520016793764821)
              ·
                refine ⟨70126908785625393603863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2992081441520016793764821 70126908785625393603863)
                ·
                  rfl

theorem cell23_3687435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 3, 7].length) (baseStart_3687435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3687435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3687435 prefixEnd_3687435 := by exact prefixLift 3687435
  have htrace : WordTrace (prefixWord ++ tailWord_3687435) baseStart_3687435 baseEnd_3687435 := by
    simpa [prefixWord, tailWord_3687435, baseEnd_3687435] using wordTrace_append hprefix tailTrace_3687435
  have hstable : (prefixWord ++ tailWord_3687435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687435).length < 2 ^ (prefixWord ++ tailWord_3687435).sum := by decide
  have hdescent : baseEnd_3687435 < baseStart_3687435 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687456 : List Nat := [2, 1, 1, 7, 1, 2, 1, 2, 2, 4]
def baseStart_3687456 : Nat := 118140960795 + 3687456 * 2 ^ 59
def prefixEnd_3687456 : Nat := 4983230072969 + 3 ^ 40 * 3687456 * 2
def baseEnd_3687456 : Nat := 631145773435210015047235

theorem tailTrace_3687456 : CollatzResearch.WordTrace tailWord_3687456 prefixEnd_3687456 631145773435210015047235 := by
  unfold tailWord_3687456
  simp only [CollatzResearch.WordTrace]
  refine ⟨67246284664492077095785111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89661712885989436127713481 67246284664492077095785111)
  ·
    refine ⟨100869426996738115643677667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67246284664492077095785111 100869426996738115643677667)
    ·
      refine ⟨151304140495107173465516501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100869426996738115643677667 151304140495107173465516501)
      ·
        refine ⟨3546190792854074378098043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 151304140495107173465516501 3546190792854074378098043)
        ·
          refine ⟨5319286189281111567147065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3546190792854074378098043 5319286189281111567147065)
          ·
            refine ⟨3989464641960833675360299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5319286189281111567147065 3989464641960833675360299)
            ·
              refine ⟨5984196962941250513040449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3989464641960833675360299 5984196962941250513040449)
              ·
                refine ⟨4488147722205937884780337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5984196962941250513040449 4488147722205937884780337)
                ·
                  refine ⟨3366110791654453413585253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4488147722205937884780337 3366110791654453413585253)
                  ·
                    refine ⟨631145773435210015047235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3366110791654453413585253 631145773435210015047235)
                    ·
                      rfl

theorem cell23_3687456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 2, 2, 4].length) (baseStart_3687456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3687456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3687456 prefixEnd_3687456 := by exact prefixLift 3687456
  have htrace : WordTrace (prefixWord ++ tailWord_3687456) baseStart_3687456 baseEnd_3687456 := by
    simpa [prefixWord, tailWord_3687456, baseEnd_3687456] using wordTrace_append hprefix tailTrace_3687456
  have hstable : (prefixWord ++ tailWord_3687456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687456).length < 2 ^ (prefixWord ++ tailWord_3687456).sum := by decide
  have hdescent : baseEnd_3687456 < baseStart_3687456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687463 : List Nat := [1, 1, 7, 1, 1, 1, 2, 4, 1, 2, 2]
def baseStart_3687463 : Nat := 118140960795 + 3687463 * 2 ^ 59
def prefixEnd_3687463 : Nat := 4983230072969 + 3 ^ 40 * 3687463 * 2
def baseEnd_3687463 : Nat := 1893440914670211517754173

theorem tailTrace_3687463 : CollatzResearch.WordTrace tailWord_3687463 prefixEnd_3687463 1893440914670211517754173 := by
  unfold tailWord_3687463
  simp only [CollatzResearch.WordTrace]
  refine ⟨134492824639958794387075043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89661883093305862924716695 134492824639958794387075043)
  ·
    refine ⟨201739236959938191580612565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134492824639958794387075043 201739236959938191580612565)
    ·
      refine ⟨4728263366248551365170607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 201739236959938191580612565 4728263366248551365170607)
      ·
        refine ⟨7092395049372827047755911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4728263366248551365170607 7092395049372827047755911)
        ·
          refine ⟨10638592574059240571633867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7092395049372827047755911 10638592574059240571633867)
          ·
            refine ⟨15957888861088860857450801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10638592574059240571633867 15957888861088860857450801)
            ·
              refine ⟨11968416645816645643088101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15957888861088860857450801 11968416645816645643088101)
              ·
                refine ⟨2244078121090621058079019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11968416645816645643088101 2244078121090621058079019)
                ·
                  refine ⟨3366117181635931587118529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2244078121090621058079019 3366117181635931587118529)
                  ·
                    refine ⟨2524587886226948690338897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3366117181635931587118529 2524587886226948690338897)
                    ·
                      refine ⟨1893440914670211517754173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2524587886226948690338897 1893440914670211517754173)
                      ·
                        rfl

theorem cell23_3687463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_3687463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3687463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3687463 prefixEnd_3687463 := by exact prefixLift 3687463
  have htrace : WordTrace (prefixWord ++ tailWord_3687463) baseStart_3687463 baseEnd_3687463 := by
    simpa [prefixWord, tailWord_3687463, baseEnd_3687463] using wordTrace_append hprefix tailTrace_3687463
  have hstable : (prefixWord ++ tailWord_3687463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687463).length < 2 ^ (prefixWord ++ tailWord_3687463).sum := by decide
  have hdescent : baseEnd_3687463 < baseStart_3687463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687502 : List Nat := [4, 1, 1, 1, 1, 3, 2, 1, 3, 4, 2]
def baseStart_3687502 : Nat := 118140960795 + 3687502 * 2 ^ 59
def prefixEnd_3687502 : Nat := 4983230072969 + 3 ^ 40 * 3687502 * 2
def baseEnd_3687502 : Nat := 1893460940415736865166493

theorem tailTrace_3687502 : CollatzResearch.WordTrace tailWord_3687502 prefixEnd_3687502 1893460940415736865166493 := by
  unfold tailWord_3687502
  simp only [CollatzResearch.WordTrace]
  refine ⟨16811780885852188005968095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89662831391211669365163173 16811780885852188005968095)
  ·
    refine ⟨25217671328778282008952143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16811780885852188005968095 25217671328778282008952143)
    ·
      refine ⟨37826506993167423013428215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25217671328778282008952143 37826506993167423013428215)
      ·
        refine ⟨56739760489751134520142323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37826506993167423013428215 56739760489751134520142323)
        ·
          refine ⟨85109640734626701780213485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56739760489751134520142323 85109640734626701780213485)
          ·
            refine ⟨31916115275485013167580057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85109640734626701780213485 31916115275485013167580057)
            ·
              refine ⟨23937086456613759875685043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31916115275485013167580057 23937086456613759875685043)
              ·
                refine ⟨35905629684920639813527565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23937086456613759875685043 35905629684920639813527565)
                ·
                  refine ⟨13464611131845239930072837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35905629684920639813527565 13464611131845239930072837)
                  ·
                    refine ⟨2524614587220982486888657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13464611131845239930072837 2524614587220982486888657)
                    ·
                      refine ⟨1893460940415736865166493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2524614587220982486888657 1893460940415736865166493)
                      ·
                        rfl

theorem cell23_3687502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 3, 4, 2].length) (baseStart_3687502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3687502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3687502 prefixEnd_3687502 := by exact prefixLift 3687502
  have htrace : WordTrace (prefixWord ++ tailWord_3687502) baseStart_3687502 baseEnd_3687502 := by
    simpa [prefixWord, tailWord_3687502, baseEnd_3687502] using wordTrace_append hprefix tailTrace_3687502
  have hstable : (prefixWord ++ tailWord_3687502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687502).length < 2 ^ (prefixWord ++ tailWord_3687502).sum := by decide
  have hdescent : baseEnd_3687502 < baseStart_3687502 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687519 : List Nat := [1, 1, 2, 3, 1, 1, 4, 4, 2, 2, 2]
def baseStart_3687519 : Nat := 118140960795 + 3687519 * 2 ^ 59
def prefixEnd_3687519 : Nat := 4983230072969 + 3 ^ 40 * 3687519 * 2
def baseEnd_3687519 : Nat := 1893469669586863298653915

theorem tailTrace_3687519 : CollatzResearch.WordTrace tailWord_3687519 prefixEnd_3687519 1893469669586863298653915 := by
  unfold tailWord_3687519
  simp only [CollatzResearch.WordTrace]
  refine ⟨134494867127755915951113611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89663244751837277300742407 134494867127755915951113611)
  ·
    refine ⟨201742300691633873926670417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134494867127755915951113611 201742300691633873926670417)
    ·
      refine ⟨151306725518725405445002813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201742300691633873926670417 151306725518725405445002813)
      ·
        refine ⟨56740022069522027041876055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151306725518725405445002813 56740022069522027041876055)
        ·
          refine ⟨85110033104283040562814083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56740022069522027041876055 85110033104283040562814083)
          ·
            refine ⟨127665049656424560844221125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85110033104283040562814083 127665049656424560844221125)
            ·
              refine ⟨23937196810579605158291461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 127665049656424560844221125 23937196810579605158291461)
              ·
                refine ⟨4488224401983675967179649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23937196810579605158291461 4488224401983675967179649)
                ·
                  refine ⟨3366168301487756975384737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4488224401983675967179649 3366168301487756975384737)
                  ·
                    refine ⟨2524626226115817731538553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3366168301487756975384737 2524626226115817731538553)
                    ·
                      refine ⟨1893469669586863298653915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2524626226115817731538553 1893469669586863298653915)
                      ·
                        rfl

theorem cell23_3687519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 4, 2, 2, 2].length) (baseStart_3687519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3687519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3687519 prefixEnd_3687519 := by exact prefixLift 3687519
  have htrace : WordTrace (prefixWord ++ tailWord_3687519) baseStart_3687519 baseEnd_3687519 := by
    simpa [prefixWord, tailWord_3687519, baseEnd_3687519] using wordTrace_append hprefix tailTrace_3687519
  have hstable : (prefixWord ++ tailWord_3687519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687519).length < 2 ^ (prefixWord ++ tailWord_3687519).sum := by decide
  have hdescent : baseEnd_3687519 < baseStart_3687519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687535 : List Nat := [1, 1, 2, 1, 3, 3, 2, 1, 1, 5, 3]
def baseStart_3687535 : Nat := 118140960795 + 3687535 * 2 ^ 59
def prefixEnd_3687535 : Nat := 4983230072969 + 3 ^ 40 * 3687535 * 2
def baseEnd_3687535 : Nat := 1893477885277335236053841

theorem tailTrace_3687535 : CollatzResearch.WordTrace tailWord_3687535 prefixEnd_3687535 1893477885277335236053841 := by
  unfold tailWord_3687535
  simp only [CollatzResearch.WordTrace]
  refine ⟨134495450695697950683696059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89663633797131967122464039 134495450695697950683696059)
  ·
    refine ⟨201743176043546926025544089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134495450695697950683696059 201743176043546926025544089)
    ·
      refine ⟨151307382032660194519158067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201743176043546926025544089 151307382032660194519158067)
      ·
        refine ⟨226961073048990291778737101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151307382032660194519158067 226961073048990291778737101)
        ·
          refine ⟨85110402393371359417026413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226961073048990291778737101 85110402393371359417026413)
          ·
            refine ⟨31916400897514259781384905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85110402393371359417026413 31916400897514259781384905)
            ·
              refine ⟨23937300673135694836038679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31916400897514259781384905 23937300673135694836038679)
              ·
                refine ⟨35905951009703542254058019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23937300673135694836038679 35905951009703542254058019)
                ·
                  refine ⟨53858926514555313381087029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35905951009703542254058019 53858926514555313381087029)
                  ·
                    refine ⟨5049274360739560629476909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53858926514555313381087029 5049274360739560629476909)
                    ·
                      refine ⟨1893477885277335236053841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5049274360739560629476909 1893477885277335236053841)
                      ·
                        rfl

theorem cell23_3687535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 5, 3].length) (baseStart_3687535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3687535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3687535 prefixEnd_3687535 := by exact prefixLift 3687535
  have htrace : WordTrace (prefixWord ++ tailWord_3687535) baseStart_3687535 baseEnd_3687535 := by
    simpa [prefixWord, tailWord_3687535, baseEnd_3687535] using wordTrace_append hprefix tailTrace_3687535
  have hstable : (prefixWord ++ tailWord_3687535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687535).length < 2 ^ (prefixWord ++ tailWord_3687535).sum := by decide
  have hdescent : baseEnd_3687535 < baseStart_3687535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687576 : List Nat := [2, 1, 2, 4, 2, 3, 2, 2, 5]
def baseStart_3687576 : Nat := 118140960795 + 3687576 * 2 ^ 59
def prefixEnd_3687576 : Nat := 4983230072969 + 3 ^ 40 * 3687576 * 2
def baseEnd_3687576 : Nat := 210388770887129952849017

theorem tailTrace_3687576 : CollatzResearch.WordTrace tailWord_3687576 prefixEnd_3687576 210388770887129952849017 := by
  unfold tailWord_3687576
  simp only [CollatzResearch.WordTrace]
  refine ⟨67248473044274707342969291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89664630725699609790625721 67248473044274707342969291)
  ·
    refine ⟨100872709566412061014453937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67248473044274707342969291 100872709566412061014453937)
    ·
      refine ⟨75654532174809045760840453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100872709566412061014453937 75654532174809045760840453)
      ·
        refine ⟨14185224782776696080157585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75654532174809045760840453 14185224782776696080157585)
        ·
          refine ⟨10638918587082522060118189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14185224782776696080157585 10638918587082522060118189)
          ·
            refine ⟨3989594470155945772544321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10638918587082522060118189 3989594470155945772544321)
            ·
              refine ⟨2992195852616959329408241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3989594470155945772544321 2992195852616959329408241)
              ·
                refine ⟨2244146889462719497056181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2992195852616959329408241 2244146889462719497056181)
                ·
                  refine ⟨210388770887129952849017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2244146889462719497056181 210388770887129952849017)
                  ·
                    rfl

theorem cell23_3687576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 2, 2, 5].length) (baseStart_3687576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3687576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3687576 prefixEnd_3687576 := by exact prefixLift 3687576
  have htrace : WordTrace (prefixWord ++ tailWord_3687576) baseStart_3687576 baseEnd_3687576 := by
    simpa [prefixWord, tailWord_3687576, baseEnd_3687576] using wordTrace_append hprefix tailTrace_3687576
  have hstable : (prefixWord ++ tailWord_3687576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687576).length < 2 ^ (prefixWord ++ tailWord_3687576).sum := by decide
  have hdescent : baseEnd_3687576 < baseStart_3687576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687602 : List Nat := [3, 2, 1, 1, 1, 4, 1, 1, 5, 4]
def baseStart_3687602 : Nat := 118140960795 + 3687602 * 2 ^ 59
def prefixEnd_3687602 : Nat := 4983230072969 + 3 ^ 40 * 3687602 * 2
def baseEnd_3687602 : Nat := 631170762827062157972011

theorem tailTrace_3687602 : CollatzResearch.WordTrace tailWord_3687602 prefixEnd_3687602 631170762827062157972011 := by
  unfold tailWord_3687602
  simp only [CollatzResearch.WordTrace]
  refine ⟨33624473596613805281596265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89665262924303480750923373 33624473596613805281596265)
  ·
    refine ⟨25218355197460353961197199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33624473596613805281596265 25218355197460353961197199)
    ·
      refine ⟨37827532796190530941795799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25218355197460353961197199 37827532796190530941795799)
      ·
        refine ⟨56741299194285796412693699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37827532796190530941795799 56741299194285796412693699)
        ·
          refine ⟨85111948791428694619040549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56741299194285796412693699 85111948791428694619040549)
          ·
            refine ⟨15958490398392880241070103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85111948791428694619040549 15958490398392880241070103)
            ·
              refine ⟨23937735597589320361605155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15958490398392880241070103 23937735597589320361605155)
              ·
                refine ⟨35906603396383980542407733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23937735597589320361605155 35906603396383980542407733)
                ·
                  refine ⟨3366244068410998175850725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35906603396383980542407733 3366244068410998175850725)
                  ·
                    refine ⟨631170762827062157972011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3366244068410998175850725 631170762827062157972011)
                    ·
                      rfl

theorem cell23_3687602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 5, 4].length) (baseStart_3687602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3687602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3687602 prefixEnd_3687602 := by exact prefixLift 3687602
  have htrace : WordTrace (prefixWord ++ tailWord_3687602) baseStart_3687602 baseEnd_3687602 := by
    simpa [prefixWord, tailWord_3687602, baseEnd_3687602] using wordTrace_append hprefix tailTrace_3687602
  have hstable : (prefixWord ++ tailWord_3687602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687602).length < 2 ^ (prefixWord ++ tailWord_3687602).sum := by decide
  have hdescent : baseEnd_3687602 < baseStart_3687602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687606 : List Nat := [5, 1, 3, 2, 1, 1, 1, 1, 1, 7]
def baseStart_3687606 : Nat := 118140960795 + 3687606 * 2 ^ 59
def prefixEnd_3687606 : Nat := 4983230072969 + 3 ^ 40 * 3687606 * 2
def baseEnd_3687606 : Nat := 631171447467934819422005

theorem tailTrace_3687606 : CollatzResearch.WordTrace tailWord_3687606 prefixEnd_3687606 631171447467934819422005 := by
  unfold tailWord_3687606
  simp only [CollatzResearch.WordTrace]
  refine ⟨8406127517402545613095667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89665360185627153206353781 8406127517402545613095667)
  ·
    refine ⟨12609191276103818419643501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8406127517402545613095667 12609191276103818419643501)
    ·
      refine ⟨4728446728538931907366313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12609191276103818419643501 4728446728538931907366313)
      ·
        refine ⟨3546335046404198930524735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4728446728538931907366313 3546335046404198930524735)
        ·
          refine ⟨5319502569606298395787103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3546335046404198930524735 5319502569606298395787103)
          ·
            refine ⟨7979253854409447593680655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5319502569606298395787103 7979253854409447593680655)
            ·
              refine ⟨11968880781614171390520983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7979253854409447593680655 11968880781614171390520983)
              ·
                refine ⟨17953321172421257085781475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11968880781614171390520983 17953321172421257085781475)
                ·
                  refine ⟨26929981758631885628672213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17953321172421257085781475 26929981758631885628672213)
                  ·
                    refine ⟨631171447467934819422005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26929981758631885628672213 631171447467934819422005)
                    ·
                      rfl

theorem cell23_3687606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_3687606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3687606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3687606 prefixEnd_3687606 := by exact prefixLift 3687606
  have htrace : WordTrace (prefixWord ++ tailWord_3687606) baseStart_3687606 baseEnd_3687606 := by
    simpa [prefixWord, tailWord_3687606, baseEnd_3687606] using wordTrace_append hprefix tailTrace_3687606
  have hstable : (prefixWord ++ tailWord_3687606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687606).length < 2 ^ (prefixWord ++ tailWord_3687606).sum := by decide
  have hdescent : baseEnd_3687606 < baseStart_3687606 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687609 : List Nat := [1, 2, 1, 4, 1, 5, 1, 1, 2, 1, 4]
def baseStart_3687609 : Nat := 118140960795 + 3687609 * 2 ^ 59
def prefixEnd_3687609 : Nat := 4983230072969 + 3 ^ 40 * 3687609 * 2
def baseEnd_3687609 : Nat := 1893515882845767946528501

theorem tailTrace_3687609 : CollatzResearch.WordTrace tailWord_3687609 prefixEnd_3687609 1893515882845767946528501 := by
  unfold tailWord_3687609
  simp only [CollatzResearch.WordTrace]
  refine ⟨134498149697429861321889881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89665433131619907547926587 134498149697429861321889881)
  ·
    refine ⟨100873612273072395991417411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134498149697429861321889881 100873612273072395991417411)
    ·
      refine ⟨151310418409608593987126117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100873612273072395991417411 151310418409608593987126117)
      ·
        refine ⟨28370703451801611372586147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 151310418409608593987126117 28370703451801611372586147)
        ·
          refine ⟨42556055177702417058879221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28370703451801611372586147 42556055177702417058879221)
          ·
            refine ⟨3989630172909601599269927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42556055177702417058879221 3989630172909601599269927)
            ·
              refine ⟨5984445259364402398904891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3989630172909601599269927 5984445259364402398904891)
              ·
                refine ⟨8976667889046603598357337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5984445259364402398904891 8976667889046603598357337)
                ·
                  refine ⟨6732500916784952698768003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8976667889046603598357337 6732500916784952698768003)
                  ·
                    refine ⟨10098751375177429048152005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6732500916784952698768003 10098751375177429048152005)
                    ·
                      refine ⟨1893515882845767946528501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10098751375177429048152005 1893515882845767946528501)
                      ·
                        rfl

theorem cell23_3687609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 1, 2, 1, 4].length) (baseStart_3687609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3687609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3687609 prefixEnd_3687609 := by exact prefixLift 3687609
  have htrace : WordTrace (prefixWord ++ tailWord_3687609) baseStart_3687609 baseEnd_3687609 := by
    simpa [prefixWord, tailWord_3687609, baseEnd_3687609] using wordTrace_append hprefix tailTrace_3687609
  have hstable : (prefixWord ++ tailWord_3687609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687609).length < 2 ^ (prefixWord ++ tailWord_3687609).sum := by decide
  have hdescent : baseEnd_3687609 < baseStart_3687609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687649 : List Nat := [1, 2, 3, 1, 3, 3, 3, 1, 6]
def baseStart_3687649 : Nat := 118140960795 + 3687649 * 2 ^ 59
def prefixEnd_3687649 : Nat := 4983230072969 + 3 ^ 40 * 3687649 * 2
def baseEnd_3687649 : Nat := 210392935785771976669813

theorem tailTrace_3687649 : CollatzResearch.WordTrace tailWord_3687649 prefixEnd_3687649 210392935785771976669813 := by
  unfold tailWord_3687649
  simp only [CollatzResearch.WordTrace]
  refine ⟨134499608617284948153346001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89666405744856632102230667 134499608617284948153346001)
  ·
    refine ⟨100874706462963711115009501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134499608617284948153346001 100874706462963711115009501)
    ·
      refine ⟨37828014923611391668128563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100874706462963711115009501 37828014923611391668128563)
      ·
        refine ⟨56742022385417087502192845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37828014923611391668128563 56742022385417087502192845)
        ·
          refine ⟨21278258394531407813322317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56742022385417087502192845 21278258394531407813322317)
          ·
            refine ⟨7979346897949277929995869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21278258394531407813322317 7979346897949277929995869)
            ·
              refine ⟨2992255086730979223748451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7979346897949277929995869 2992255086730979223748451)
              ·
                refine ⟨4488382630096468835622677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2992255086730979223748451 4488382630096468835622677)
                ·
                  refine ⟨210392935785771976669813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4488382630096468835622677 210392935785771976669813)
                  ·
                    rfl

theorem cell23_3687649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 3, 1, 6].length) (baseStart_3687649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3687649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3687649 prefixEnd_3687649 := by exact prefixLift 3687649
  have htrace : WordTrace (prefixWord ++ tailWord_3687649) baseStart_3687649 baseEnd_3687649 := by
    simpa [prefixWord, tailWord_3687649, baseEnd_3687649] using wordTrace_append hprefix tailTrace_3687649
  have hstable : (prefixWord ++ tailWord_3687649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687649).length < 2 ^ (prefixWord ++ tailWord_3687649).sum := by decide
  have hdescent : baseEnd_3687649 < baseStart_3687649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687659 : List Nat := [1, 1, 1, 1, 2, 6, 2, 2, 3, 1, 3]
def baseStart_3687659 : Nat := 118140960795 + 3687659 * 2 ^ 59
def prefixEnd_3687659 : Nat := 4983230072969 + 3 ^ 40 * 3687659 * 2
def baseEnd_3687659 : Nat := 1893541556878492750903271

theorem tailTrace_3687659 : CollatzResearch.WordTrace tailWord_3687659 prefixEnd_3687659 1893541556878492750903271 := by
  unfold tailWord_3687659
  simp only [CollatzResearch.WordTrace]
  refine ⟨134499973347248719861210031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89666648898165813240806687 134499973347248719861210031)
  ·
    refine ⟨201749960020873079791815047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134499973347248719861210031 201749960020873079791815047)
    ·
      refine ⟨302624940031309619687722571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201749960020873079791815047 302624940031309619687722571)
      ·
        refine ⟨453937410046964429531583857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302624940031309619687722571 453937410046964429531583857)
        ·
          refine ⟨340453057535223322148687893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 453937410046964429531583857 340453057535223322148687893)
          ·
            refine ⟨15958737071963593225719745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 340453057535223322148687893 15958737071963593225719745)
            ·
              refine ⟨11969052803972694919289809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15958737071963593225719745 11969052803972694919289809)
              ·
                refine ⟨8976789602979521189467357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11969052803972694919289809 8976789602979521189467357)
                ·
                  refine ⟨3366296101117320446050259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8976789602979521189467357 3366296101117320446050259)
                  ·
                    refine ⟨5049444151675980669075389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3366296101117320446050259 5049444151675980669075389)
                    ·
                      refine ⟨1893541556878492750903271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5049444151675980669075389 1893541556878492750903271)
                      ·
                        rfl

theorem cell23_3687659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 2, 3, 1, 3].length) (baseStart_3687659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3687659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3687659 prefixEnd_3687659 := by exact prefixLift 3687659
  have htrace : WordTrace (prefixWord ++ tailWord_3687659) baseStart_3687659 baseEnd_3687659 := by
    simpa [prefixWord, tailWord_3687659, baseEnd_3687659] using wordTrace_append hprefix tailTrace_3687659
  have hstable : (prefixWord ++ tailWord_3687659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687659).length < 2 ^ (prefixWord ++ tailWord_3687659).sum := by decide
  have hdescent : baseEnd_3687659 < baseStart_3687659 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687662 : List Nat := [4, 1, 2, 1, 1, 1, 2, 3, 3, 5]
def baseStart_3687662 : Nat := 118140960795 + 3687662 * 2 ^ 59
def prefixEnd_3687662 : Nat := 4983230072969 + 3 ^ 40 * 3687662 * 2
def baseEnd_3687662 : Nat := 631181032440152079721919

theorem tailTrace_3687662 : CollatzResearch.WordTrace tailWord_3687662 prefixEnd_3687662 631181032440152079721919 := by
  unfold tailWord_3687662
  simp only [CollatzResearch.WordTrace]
  refine ⟨16812510345779731421696155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89666721844158567582379493 16812510345779731421696155)
  ·
    refine ⟨25218765518669597132544233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16812510345779731421696155 25218765518669597132544233)
    ·
      refine ⟨18914074139002197849408175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25218765518669597132544233 18914074139002197849408175)
      ·
        refine ⟨28371111208503296774112263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18914074139002197849408175 28371111208503296774112263)
        ·
          refine ⟨42556666812754945161168395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28371111208503296774112263 42556666812754945161168395)
          ·
            refine ⟨63835000219132417741752593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42556666812754945161168395 63835000219132417741752593)
            ·
              refine ⟨47876250164349313306314445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63835000219132417741752593 47876250164349313306314445)
              ·
                refine ⟨17953593811630992489867917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47876250164349313306314445 17953593811630992489867917)
                ·
                  refine ⟨6732597679361622183700469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17953593811630992489867917 6732597679361622183700469)
                  ·
                    refine ⟨631181032440152079721919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6732597679361622183700469 631181032440152079721919)
                    ·
                      rfl

theorem cell23_3687662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 3, 3, 5].length) (baseStart_3687662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3687662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3687662 prefixEnd_3687662 := by exact prefixLift 3687662
  have htrace : WordTrace (prefixWord ++ tailWord_3687662) baseStart_3687662 baseEnd_3687662 := by
    simpa [prefixWord, tailWord_3687662, baseEnd_3687662] using wordTrace_append hprefix tailTrace_3687662
  have hstable : (prefixWord ++ tailWord_3687662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687662).length < 2 ^ (prefixWord ++ tailWord_3687662).sum := by decide
  have hdescent : baseEnd_3687662 < baseStart_3687662 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687716 : List Nat := [2, 3, 1, 3, 1, 1, 2, 1, 5, 2, 2]
def baseStart_3687716 : Nat := 118140960795 + 3687716 * 2 ^ 59
def prefixEnd_3687716 : Nat := 4983230072969 + 3 ^ 40 * 3687716 * 2
def baseEnd_3687716 : Nat := 1893570825275799027890509

theorem tailTrace_3687716 : CollatzResearch.WordTrace tailWord_3687716 prefixEnd_3687716 1893570825275799027890509 := by
  unfold tailWord_3687716
  simp only [CollatzResearch.WordTrace]
  refine ⟨67251026154021109298017501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89668034872028145730690001 67251026154021109298017501)
  ·
    refine ⟨25219134807757915986756563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67251026154021109298017501 25219134807757915986756563)
    ·
      refine ⟨37828702211636873980134845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25219134807757915986756563 37828702211636873980134845)
      ·
        refine ⟨14185763329363827742550567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37828702211636873980134845 14185763329363827742550567)
        ·
          refine ⟨21278644994045741613825851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14185763329363827742550567 21278644994045741613825851)
          ·
            refine ⟨31917967491068612420738777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21278644994045741613825851 31917967491068612420738777)
            ·
              refine ⟨23938475618301459315554083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31917967491068612420738777 23938475618301459315554083)
              ·
                refine ⟨35907713427452188973331125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23938475618301459315554083 35907713427452188973331125)
                ·
                  refine ⟨3366348133823642716249793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35907713427452188973331125 3366348133823642716249793)
                  ·
                    refine ⟨2524761100367732037187345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3366348133823642716249793 2524761100367732037187345)
                    ·
                      refine ⟨1893570825275799027890509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2524761100367732037187345 1893570825275799027890509)
                      ·
                        rfl

theorem cell23_3687716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 5, 2, 2].length) (baseStart_3687716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3687716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3687716 prefixEnd_3687716 := by exact prefixLift 3687716
  have htrace : WordTrace (prefixWord ++ tailWord_3687716) baseStart_3687716 baseEnd_3687716 := by
    simpa [prefixWord, tailWord_3687716, baseEnd_3687716] using wordTrace_append hprefix tailTrace_3687716
  have hstable : (prefixWord ++ tailWord_3687716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687716).length < 2 ^ (prefixWord ++ tailWord_3687716).sum := by decide
  have hdescent : baseEnd_3687716 < baseStart_3687716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687729 : List Nat := [1, 2, 2, 3, 3, 2, 1, 2, 1, 2, 4]
def baseStart_3687729 : Nat := 118140960795 + 3687729 * 2 ^ 59
def prefixEnd_3687729 : Nat := 4983230072969 + 3 ^ 40 * 3687729 * 2
def baseEnd_3687729 : Nat := 1893577500524307477027949

theorem tailTrace_3687729 : CollatzResearch.WordTrace tailWord_3687729 prefixEnd_3687729 1893577500524307477027949 := by
  unfold tailWord_3687729
  simp only [CollatzResearch.WordTrace]
  refine ⟨134502526456995121816258241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89668350971330081210838827 134502526456995121816258241)
  ·
    refine ⟨100876894842746341362193681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134502526456995121816258241 100876894842746341362193681)
    ·
      refine ⟨75657671132059756021645261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100876894842746341362193681 75657671132059756021645261)
      ·
        refine ⟨28371626674522408508116973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75657671132059756021645261 28371626674522408508116973)
        ·
          refine ⟨10639360002945903190543865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28371626674522408508116973 10639360002945903190543865)
          ·
            refine ⟨7979520002209427392907899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10639360002945903190543865 7979520002209427392907899)
            ·
              refine ⟨11969280003314141089361849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7979520002209427392907899 11969280003314141089361849)
              ·
                refine ⟨8976960002485605817021387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11969280003314141089361849 8976960002485605817021387)
                ·
                  refine ⟨13465440003728408725532081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8976960002485605817021387 13465440003728408725532081)
                  ·
                    refine ⟨10099080002796306544149061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13465440003728408725532081 10099080002796306544149061)
                    ·
                      refine ⟨1893577500524307477027949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10099080002796306544149061 1893577500524307477027949)
                      ·
                        rfl

theorem cell23_3687729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_3687729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3687729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3687729 prefixEnd_3687729 := by exact prefixLift 3687729
  have htrace : WordTrace (prefixWord ++ tailWord_3687729) baseStart_3687729 baseEnd_3687729 := by
    simpa [prefixWord, tailWord_3687729, baseEnd_3687729] using wordTrace_append hprefix tailTrace_3687729
  have hstable : (prefixWord ++ tailWord_3687729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687729).length < 2 ^ (prefixWord ++ tailWord_3687729).sum := by decide
  have hdescent : baseEnd_3687729 < baseStart_3687729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687749 : List Nat := [1, 3, 1, 1, 1, 2, 1, 5, 4, 1, 3]
def baseStart_3687749 : Nat := 118140960795 + 3687749 * 2 ^ 59
def prefixEnd_3687749 : Nat := 4983230072969 + 3 ^ 40 * 3687749 * 2
def baseEnd_3687749 : Nat := 1893587770137397398777857

theorem tailTrace_3687749 : CollatzResearch.WordTrace tailWord_3687749 prefixEnd_3687749 1893587770137397398777857 := by
  unfold tailWord_3687749
  simp only [CollatzResearch.WordTrace]
  refine ⟨134503255916922665231986301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89668837277948443487990867 134503255916922665231986301)
  ·
    refine ⟨50438720968845999461994863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134503255916922665231986301 50438720968845999461994863)
    ·
      refine ⟨75658081453268999192992295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50438720968845999461994863 75658081453268999192992295)
      ·
        refine ⟨113487122179903498789488443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75658081453268999192992295 113487122179903498789488443)
        ·
          refine ⟨170230683269855248184232665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113487122179903498789488443 170230683269855248184232665)
          ·
            refine ⟨127673012452391436138174499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170230683269855248184232665 127673012452391436138174499)
            ·
              refine ⟨191509518678587154207261749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127673012452391436138174499 191509518678587154207261749)
              ·
                refine ⟨17954017376117545706930789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 191509518678587154207261749 17954017376117545706930789)
                ·
                  refine ⟨3366378258022039820049523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17954017376117545706930789 3366378258022039820049523)
                  ·
                    refine ⟨5049567387033059730074285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3366378258022039820049523 5049567387033059730074285)
                    ·
                      refine ⟨1893587770137397398777857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5049567387033059730074285 1893587770137397398777857)
                      ·
                        rfl

theorem cell23_3687749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5, 4, 1, 3].length) (baseStart_3687749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3687749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3687749 prefixEnd_3687749 := by exact prefixLift 3687749
  have htrace : WordTrace (prefixWord ++ tailWord_3687749) baseStart_3687749 baseEnd_3687749 := by
    simpa [prefixWord, tailWord_3687749, baseEnd_3687749] using wordTrace_append hprefix tailTrace_3687749
  have hstable : (prefixWord ++ tailWord_3687749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687749).length < 2 ^ (prefixWord ++ tailWord_3687749).sum := by decide
  have hdescent : baseEnd_3687749 < baseStart_3687749 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687762 : List Nat := [3, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5]
def baseStart_3687762 : Nat := 118140960795 + 3687762 * 2 ^ 59
def prefixEnd_3687762 : Nat := 4983230072969 + 3 ^ 40 * 3687762 * 2
def baseEnd_3687762 : Nat := 1893594445385905847915297

theorem tailTrace_3687762 : CollatzResearch.WordTrace tailWord_3687762 prefixEnd_3687762 1893594445385905847915297 := by
  unfold tailWord_3687762
  simp only [CollatzResearch.WordTrace]
  refine ⟨33625932516468892113052385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89669153377250378968139693 33625932516468892113052385)
  ·
    refine ⟨25219449387351669084789289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33625932516468892113052385 25219449387351669084789289)
    ·
      refine ⟨18914587040513751813591967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25219449387351669084789289 18914587040513751813591967)
      ·
        refine ⟨28371880560770627720387951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18914587040513751813591967 28371880560770627720387951)
        ·
          refine ⟨42557820841155941580581927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28371880560770627720387951 42557820841155941580581927)
          ·
            refine ⟨63836731261733912370872891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42557820841155941580581927 63836731261733912370872891)
            ·
              refine ⟨95755096892600868556309337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63836731261733912370872891 95755096892600868556309337)
              ·
                refine ⟨71816322669450651417232003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95755096892600868556309337 71816322669450651417232003)
                ·
                  refine ⟨107724484004175977125848005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71816322669450651417232003 107724484004175977125848005)
                  ·
                    refine ⟨20198340750782995711096501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 107724484004175977125848005 20198340750782995711096501)
                    ·
                      refine ⟨1893594445385905847915297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20198340750782995711096501 1893594445385905847915297)
                      ·
                        rfl

theorem cell23_3687762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_3687762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3687762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3687762 prefixEnd_3687762 := by exact prefixLift 3687762
  have htrace : WordTrace (prefixWord ++ tailWord_3687762) baseStart_3687762 baseEnd_3687762 := by
    simpa [prefixWord, tailWord_3687762, baseEnd_3687762] using wordTrace_append hprefix tailTrace_3687762
  have hstable : (prefixWord ++ tailWord_3687762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687762).length < 2 ^ (prefixWord ++ tailWord_3687762).sum := by decide
  have hdescent : baseEnd_3687762 < baseStart_3687762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687776 : List Nat := [2, 1, 1, 3, 4, 1, 2, 1, 3, 3, 2]
def baseStart_3687776 : Nat := 118140960795 + 3687776 * 2 ^ 59
def prefixEnd_3687776 : Nat := 4983230072969 + 3 ^ 40 * 3687776 * 2
def baseEnd_3687776 : Nat := 1893601634115068793140233

theorem tailTrace_3687776 : CollatzResearch.WordTrace tailWord_3687776 prefixEnd_3687776 1893601634115068793140233 := by
  unfold tailWord_3687776
  simp only [CollatzResearch.WordTrace]
  refine ⟨67252120343912424421609591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89669493791883232562146121 67252120343912424421609591)
  ·
    refine ⟨100878180515868636632414387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67252120343912424421609591 100878180515868636632414387)
    ·
      refine ⟨151317270773802954948621581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100878180515868636632414387 151317270773802954948621581)
      ·
        refine ⟨56743976540176108105733093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151317270773802954948621581 56743976540176108105733093)
        ·
          refine ⟨10639495601283020269824955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56743976540176108105733093 10639495601283020269824955)
          ·
            refine ⟨15959243401924530404737433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10639495601283020269824955 15959243401924530404737433)
            ·
              refine ⟨11969432551443397803553075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15959243401924530404737433 11969432551443397803553075)
              ·
                refine ⟨17954148827165096705329613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11969432551443397803553075 17954148827165096705329613)
                ·
                  refine ⟨6732805810186911264498605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17954148827165096705329613 6732805810186911264498605)
                  ·
                    refine ⟨2524802178820091724186977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6732805810186911264498605 2524802178820091724186977)
                    ·
                      refine ⟨1893601634115068793140233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2524802178820091724186977 1893601634115068793140233)
                      ·
                        rfl

theorem cell23_3687776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 1, 3, 3, 2].length) (baseStart_3687776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3687776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3687776 prefixEnd_3687776 := by exact prefixLift 3687776
  have htrace : WordTrace (prefixWord ++ tailWord_3687776) baseStart_3687776 baseEnd_3687776 := by
    simpa [prefixWord, tailWord_3687776, baseEnd_3687776] using wordTrace_append hprefix tailTrace_3687776
  have hstable : (prefixWord ++ tailWord_3687776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687776).length < 2 ^ (prefixWord ++ tailWord_3687776).sum := by decide
  have hdescent : baseEnd_3687776 < baseStart_3687776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687792 : List Nat := [2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 5]
def baseStart_3687792 : Nat := 118140960795 + 3687792 * 2 ^ 59
def prefixEnd_3687792 : Nat := 4983230072969 + 3 ^ 40 * 3687792 * 2
def baseEnd_3687792 : Nat := 1893609849805540730540159

theorem tailTrace_3687792 : CollatzResearch.WordTrace tailWord_3687792 prefixEnd_3687792 1893609849805540730540159 := by
  unfold tailWord_3687792
  simp only [CollatzResearch.WordTrace]
  refine ⟨67252412127883441787900815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89669882837177922383867753 67252412127883441787900815)
  ·
    refine ⟨100878618191825162681851223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67252412127883441787900815 100878618191825162681851223)
    ·
      refine ⟨151317927287737744022776835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100878618191825162681851223 151317927287737744022776835)
      ·
        refine ⟨226976890931606616034165253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151317927287737744022776835 226976890931606616034165253)
        ·
          refine ⟨42558167049676240506405985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 226976890931606616034165253 42558167049676240506405985)
          ·
            refine ⟨31918625287257180379804489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42558167049676240506405985 31918625287257180379804489)
            ·
              refine ⟨23938968965442885284853367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31918625287257180379804489 23938968965442885284853367)
              ·
                refine ⟨35908453448164327927280051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23938968965442885284853367 35908453448164327927280051)
                ·
                  refine ⟨53862680172246491890920077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35908453448164327927280051 53862680172246491890920077)
                  ·
                    refine ⟨20198505064592434459095029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53862680172246491890920077 20198505064592434459095029)
                    ·
                      refine ⟨1893609849805540730540159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20198505064592434459095029 1893609849805540730540159)
                      ·
                        rfl

theorem cell23_3687792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 5].length) (baseStart_3687792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3687792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3687792 prefixEnd_3687792 := by exact prefixLift 3687792
  have htrace : WordTrace (prefixWord ++ tailWord_3687792) baseStart_3687792 baseEnd_3687792 := by
    simpa [prefixWord, tailWord_3687792, baseEnd_3687792] using wordTrace_append hprefix tailTrace_3687792
  have hstable : (prefixWord ++ tailWord_3687792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687792).length < 2 ^ (prefixWord ++ tailWord_3687792).sum := by decide
  have hdescent : baseEnd_3687792 < baseStart_3687792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687793 : List Nat := [1, 2, 2, 2, 1, 2, 6, 1, 1, 3, 2]
def baseStart_3687793 : Nat := 118140960795 + 3687793 * 2 ^ 59
def prefixEnd_3687793 : Nat := 4983230072969 + 3 ^ 40 * 3687793 * 2
def baseEnd_3687793 : Nat := 1893610363286195226627655

theorem tailTrace_3687793 : CollatzResearch.WordTrace tailWord_3687793 prefixEnd_3687793 1893610363286195226627655 := by
  unfold tailWord_3687793
  simp only [CollatzResearch.WordTrace]
  refine ⟨134504860728763260746588033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89669907152508840497725355 134504860728763260746588033)
  ·
    refine ⟨100878645546572445559941025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134504860728763260746588033 100878645546572445559941025)
    ·
      refine ⟨75658984159929334169955769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100878645546572445559941025 75658984159929334169955769)
      ·
        refine ⟨56744238119947000627466827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75658984159929334169955769 56744238119947000627466827)
        ·
          refine ⟨85116357179920500941200241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56744238119947000627466827 85116357179920500941200241)
          ·
            refine ⟨63837267884940375705900181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85116357179920500941200241 63837267884940375705900181)
            ·
              refine ⟨2992371932106580111214071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 63837267884940375705900181 2992371932106580111214071)
              ·
                refine ⟨4488557898159870166821107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2992371932106580111214071 4488557898159870166821107)
                ·
                  refine ⟨6732836847239805250231661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4488557898159870166821107 6732836847239805250231661)
                  ·
                    refine ⟨2524813817714926968836873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6732836847239805250231661 2524813817714926968836873)
                    ·
                      refine ⟨1893610363286195226627655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2524813817714926968836873 1893610363286195226627655)
                      ·
                        rfl

theorem cell23_3687793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 6, 1, 1, 3, 2].length) (baseStart_3687793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3687793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3687793 prefixEnd_3687793 := by exact prefixLift 3687793
  have htrace : WordTrace (prefixWord ++ tailWord_3687793) baseStart_3687793 baseEnd_3687793 := by
    simpa [prefixWord, tailWord_3687793, baseEnd_3687793] using wordTrace_append hprefix tailTrace_3687793
  have hstable : (prefixWord ++ tailWord_3687793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687793).length < 2 ^ (prefixWord ++ tailWord_3687793).sum := by decide
  have hdescent : baseEnd_3687793 < baseStart_3687793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687802 : List Nat := [3, 1, 1, 1, 1, 1, 2, 2, 3, 4, 4]
def baseStart_3687802 : Nat := 118140960795 + 3687802 * 2 ^ 59
def prefixEnd_3687802 : Nat := 4983230072969 + 3 ^ 40 * 3687802 * 2
def baseEnd_3687802 : Nat := 1893614984612085691415113

theorem tailTrace_3687802 : CollatzResearch.WordTrace tailWord_3687802 prefixEnd_3687802 1893614984612085691415113 := by
  unfold tailWord_3687802
  simp only [CollatzResearch.WordTrace]
  refine ⟨33626297246432663820916415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89670125990487103522443773 33626297246432663820916415)
  ·
    refine ⟨50439445869648995731374623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33626297246432663820916415 50439445869648995731374623)
    ·
      refine ⟨75659168804473493597061935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50439445869648995731374623 75659168804473493597061935)
      ·
        refine ⟨113488753206710240395592903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75659168804473493597061935 113488753206710240395592903)
        ·
          refine ⟨170233129810065360593389355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113488753206710240395592903 170233129810065360593389355)
          ·
            refine ⟨255349694715098040890084033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170233129810065360593389355 255349694715098040890084033)
            ·
              refine ⟨191512271036323530667563025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255349694715098040890084033 191512271036323530667563025)
              ·
                refine ⟨143634203277242648000672269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191512271036323530667563025 143634203277242648000672269)
                ·
                  refine ⟨53862826228965993000252101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 143634203277242648000672269 53862826228965993000252101)
                  ·
                    refine ⟨10099279917931123687547269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53862826228965993000252101 10099279917931123687547269)
                    ·
                      refine ⟨1893614984612085691415113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10099279917931123687547269 1893614984612085691415113)
                      ·
                        rfl

theorem cell23_3687802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 3, 4, 4].length) (baseStart_3687802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3687802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3687802 prefixEnd_3687802 := by exact prefixLift 3687802
  have htrace : WordTrace (prefixWord ++ tailWord_3687802) baseStart_3687802 baseEnd_3687802 := by
    simpa [prefixWord, tailWord_3687802, baseEnd_3687802] using wordTrace_append hprefix tailTrace_3687802
  have hstable : (prefixWord ++ tailWord_3687802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687802).length < 2 ^ (prefixWord ++ tailWord_3687802).sum := by decide
  have hdescent : baseEnd_3687802 < baseStart_3687802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687849 : List Nat := [1, 2, 1, 1, 1, 1, 3, 1, 3, 7, 2]
def baseStart_3687849 : Nat := 118140960795 + 3687849 * 2 ^ 59
def prefixEnd_3687849 : Nat := 4983230072969 + 3 ^ 40 * 3687849 * 2
def baseEnd_3687849 : Nat := 1893639118202847007527397

theorem tailTrace_3687849 : CollatzResearch.WordTrace tailWord_3687849 prefixEnd_3687849 1893639118202847007527397 := by
  unfold tailWord_3687849
  simp only [CollatzResearch.WordTrace]
  refine ⟨134506903216560382310626601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89671268811040254873751067 134506903216560382310626601)
  ·
    refine ⟨100880177412420286732969951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134506903216560382310626601 100880177412420286732969951)
    ·
      refine ⟨151320266118630430099454927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100880177412420286732969951 151320266118630430099454927)
      ·
        refine ⟨226980399177945645149182391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151320266118630430099454927 226980399177945645149182391)
        ·
          refine ⟨340470598766918467723773587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226980399177945645149182391 340470598766918467723773587)
          ·
            refine ⟨510705898150377701585660381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340470598766918467723773587 510705898150377701585660381)
            ·
              refine ⟨191514711806391638094622643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 510705898150377701585660381 191514711806391638094622643)
              ·
                refine ⟨287272067709587457141933965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191514711806391638094622643 287272067709587457141933965)
                ·
                  refine ⟨107727025391095296428225237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 287272067709587457141933965 107727025391095296428225237)
                  ·
                    refine ⟨2524852157603796010036529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 107727025391095296428225237 2524852157603796010036529)
                    ·
                      refine ⟨1893639118202847007527397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2524852157603796010036529 1893639118202847007527397)
                      ·
                        rfl

theorem cell23_3687849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 7, 2].length) (baseStart_3687849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3687849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3687849 prefixEnd_3687849 := by exact prefixLift 3687849
  have htrace : WordTrace (prefixWord ++ tailWord_3687849) baseStart_3687849 baseEnd_3687849 := by
    simpa [prefixWord, tailWord_3687849, baseEnd_3687849] using wordTrace_append hprefix tailTrace_3687849
  have hstable : (prefixWord ++ tailWord_3687849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687849).length < 2 ^ (prefixWord ++ tailWord_3687849).sum := by decide
  have hdescent : baseEnd_3687849 < baseStart_3687849 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687869 : List Nat := [1, 4, 1, 2, 2, 1, 3, 1, 1, 2, 5]
def baseStart_3687869 : Nat := 118140960795 + 3687869 * 2 ^ 59
def prefixEnd_3687869 : Nat := 4983230072969 + 3 ^ 40 * 3687869 * 2
def baseEnd_3687869 : Nat := 1893649387815936929277305

theorem tailTrace_3687869 : CollatzResearch.WordTrace tailWord_3687869 prefixEnd_3687869 1893649387815936929277305 := by
  unfold tailWord_3687869
  simp only [CollatzResearch.WordTrace]
  refine ⟨134507632676487925726354661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89671755117658617150903107 134507632676487925726354661)
  ·
    refine ⟨25220181126841486073691499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134507632676487925726354661 25220181126841486073691499)
    ·
      refine ⟨37830271690262229110537249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25220181126841486073691499 37830271690262229110537249)
      ·
        refine ⟨28372703767696671832902937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37830271690262229110537249 28372703767696671832902937)
        ·
          refine ⟨21279527825772503874677203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28372703767696671832902937 21279527825772503874677203)
          ·
            refine ⟨31919291738658755812015805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21279527825772503874677203 31919291738658755812015805)
            ·
              refine ⟨11969734401997033429505927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31919291738658755812015805 11969734401997033429505927)
              ·
                refine ⟨17954601602995550144258891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11969734401997033429505927 17954601602995550144258891)
                ·
                  refine ⟨26931902404493325216388337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17954601602995550144258891 26931902404493325216388337)
                  ·
                    refine ⟨20198926803369993912291253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26931902404493325216388337 20198926803369993912291253)
                    ·
                      refine ⟨1893649387815936929277305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20198926803369993912291253 1893649387815936929277305)
                      ·
                        rfl

theorem cell23_3687869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_3687869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3687869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3687869 prefixEnd_3687869 := by exact prefixLift 3687869
  have htrace : WordTrace (prefixWord ++ tailWord_3687869) baseStart_3687869 baseEnd_3687869 := by
    simpa [prefixWord, tailWord_3687869, baseEnd_3687869] using wordTrace_append hprefix tailTrace_3687869
  have hstable : (prefixWord ++ tailWord_3687869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687869).length < 2 ^ (prefixWord ++ tailWord_3687869).sum := by decide
  have hdescent : baseEnd_3687869 < baseStart_3687869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687879 : List Nat := [1, 1, 4, 1, 1, 3, 1, 2, 4, 1, 4]
def baseStart_3687879 : Nat := 118140960795 + 3687879 * 2 ^ 59
def prefixEnd_3687879 : Nat := 4983230072969 + 3 ^ 40 * 3687879 * 2
def baseEnd_3687879 : Nat := 1893654522622481890152259

theorem tailTrace_3687879 : CollatzResearch.WordTrace tailWord_3687879 prefixEnd_3687879 1893654522622481890152259 := by
  unfold tailWord_3687879
  simp only [CollatzResearch.WordTrace]
  refine ⟨134507997406451697434218691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89671998270967798289479127 134507997406451697434218691)
  ·
    refine ⟨201761996109677546151328037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134507997406451697434218691 201761996109677546151328037)
    ·
      refine ⟨37830374270564539903374007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 201761996109677546151328037 37830374270564539903374007)
      ·
        refine ⟨56745561405846809855061011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37830374270564539903374007 56745561405846809855061011)
        ·
          refine ⟨85118342108770214782591517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56745561405846809855061011 85118342108770214782591517)
          ·
            refine ⟨31919378290788830543471819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85118342108770214782591517 31919378290788830543471819)
            ·
              refine ⟨47879067436183245815207729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31919378290788830543471819 47879067436183245815207729)
              ·
                refine ⟨35909300577137434361405797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47879067436183245815207729 35909300577137434361405797)
                ·
                  refine ⟨6732993858213268942763587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35909300577137434361405797 6732993858213268942763587)
                  ·
                    refine ⟨10099490787319903414145381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6732993858213268942763587 10099490787319903414145381)
                    ·
                      refine ⟨1893654522622481890152259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10099490787319903414145381 1893654522622481890152259)
                      ·
                        rfl

theorem cell23_3687879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 4, 1, 4].length) (baseStart_3687879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3687879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3687879 prefixEnd_3687879 := by exact prefixLift 3687879
  have htrace : WordTrace (prefixWord ++ tailWord_3687879) baseStart_3687879 baseEnd_3687879 := by
    simpa [prefixWord, tailWord_3687879, baseEnd_3687879] using wordTrace_append hprefix tailTrace_3687879
  have hstable : (prefixWord ++ tailWord_3687879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687879).length < 2 ^ (prefixWord ++ tailWord_3687879).sum := by decide
  have hdescent : baseEnd_3687879 < baseStart_3687879 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687919 : List Nat := [1, 1, 2, 1, 4, 1, 3, 4, 6]
def baseStart_3687919 : Nat := 118140960795 + 3687919 * 2 ^ 59
def prefixEnd_3687919 : Nat := 4983230072969 + 3 ^ 40 * 3687919 * 2
def baseEnd_3687919 : Nat := 210408340205406859294675

theorem tailTrace_3687919 : CollatzResearch.WordTrace tailWord_3687919 prefixEnd_3687919 210408340205406859294675 := by
  unfold tailWord_3687919
  simp only [CollatzResearch.WordTrace]
  refine ⟨134509456326306784265674811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89672970884204522843783207 134509456326306784265674811)
  ·
    refine ⟨201764184489460176398512217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134509456326306784265674811 201764184489460176398512217)
    ·
      refine ⟨151323138367095132298884163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201764184489460176398512217 151323138367095132298884163)
      ·
        refine ⟨226984707550642698448326245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151323138367095132298884163 226984707550642698448326245)
        ·
          refine ⟨42559632665745505959061171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 226984707550642698448326245 42559632665745505959061171)
          ·
            refine ⟨63839448998618258938591757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42559632665745505959061171 63839448998618258938591757)
            ·
              refine ⟨23939793374481847101971909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63839448998618258938591757 23939793374481847101971909)
              ·
                refine ⟨4488711257715346331619733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23939793374481847101971909 4488711257715346331619733)
                ·
                  refine ⟨210408340205406859294675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4488711257715346331619733 210408340205406859294675)
                  ·
                    rfl

theorem cell23_3687919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 4, 6].length) (baseStart_3687919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3687919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3687919 prefixEnd_3687919 := by exact prefixLift 3687919
  have htrace : WordTrace (prefixWord ++ tailWord_3687919) baseStart_3687919 baseEnd_3687919 := by
    simpa [prefixWord, tailWord_3687919, baseEnd_3687919] using wordTrace_append hprefix tailTrace_3687919
  have hstable : (prefixWord ++ tailWord_3687919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687919).length < 2 ^ (prefixWord ++ tailWord_3687919).sum := by decide
  have hdescent : baseEnd_3687919 < baseStart_3687919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687929 : List Nat := [1, 2, 1, 3, 1, 2, 1, 2, 2, 5, 3]
def baseStart_3687929 : Nat := 118140960795 + 3687929 * 2 ^ 59
def prefixEnd_3687929 : Nat := 4983230072969 + 3 ^ 40 * 3687929 * 2
def baseEnd_3687929 : Nat := 1893680196655206694527029

theorem tailTrace_3687929 : CollatzResearch.WordTrace tailWord_3687929 prefixEnd_3687929 1893680196655206694527029 := by
  unfold tailWord_3687929
  simp only [CollatzResearch.WordTrace]
  refine ⟨134509821056270555973538841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89673214037513703982359227 134509821056270555973538841)
  ·
    refine ⟨100882365792202916980154131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134509821056270555973538841 100882365792202916980154131)
    ·
      refine ⟨151323548688304375470231197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100882365792202916980154131 151323548688304375470231197)
      ·
        refine ⟨56746330758114140801336699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151323548688304375470231197 56746330758114140801336699)
        ·
          refine ⟨85119496137171211202005049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56746330758114140801336699 85119496137171211202005049)
          ·
            refine ⟨63839622102878408401503787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85119496137171211202005049 63839622102878408401503787)
            ·
              refine ⟨95759433154317612602255681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63839622102878408401503787 95759433154317612602255681)
              ·
                refine ⟨71819574865738209451691761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95759433154317612602255681 71819574865738209451691761)
                ·
                  refine ⟨53864681149303657088768821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71819574865738209451691761 53864681149303657088768821)
                  ·
                    refine ⟨5049813857747217852072077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53864681149303657088768821 5049813857747217852072077)
                    ·
                      refine ⟨1893680196655206694527029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5049813857747217852072077 1893680196655206694527029)
                      ·
                        rfl

theorem cell23_3687929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 5, 3].length) (baseStart_3687929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3687929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3687929 prefixEnd_3687929 := by exact prefixLift 3687929
  have htrace : WordTrace (prefixWord ++ tailWord_3687929) baseStart_3687929 baseEnd_3687929 := by
    simpa [prefixWord, tailWord_3687929, baseEnd_3687929] using wordTrace_append hprefix tailTrace_3687929
  have hstable : (prefixWord ++ tailWord_3687929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687929).length < 2 ^ (prefixWord ++ tailWord_3687929).sum := by decide
  have hdescent : baseEnd_3687929 < baseStart_3687929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687950 : List Nat := [4, 1, 1, 2, 4, 2, 1, 1, 2, 2, 3]
def baseStart_3687950 : Nat := 118140960795 + 3687950 * 2 ^ 59
def prefixEnd_3687950 : Nat := 4983230072969 + 3 ^ 40 * 3687950 * 2
def baseEnd_3687950 : Nat := 1893690979748951112364433

theorem tailTrace_3687950 : CollatzResearch.WordTrace tailWord_3687950 prefixEnd_3687950 1893690979748951112364433 := by
  unfold tailWord_3687950
  simp only [CollatzResearch.WordTrace]
  refine ⟨16813823373649309570006663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89673724659462984373368869 16813823373649309570006663)
  ·
    refine ⟨25220735060473964355009995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16813823373649309570006663 25220735060473964355009995)
    ·
      refine ⟨37831102590710946532514993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25220735060473964355009995 37831102590710946532514993)
      ·
        refine ⟨28373326943033209899386245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37831102590710946532514993 28373326943033209899386245)
        ·
          refine ⟨5319998801818726856134921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28373326943033209899386245 5319998801818726856134921)
          ·
            refine ⟨3989999101364045142101191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5319998801818726856134921 3989999101364045142101191)
            ·
              refine ⟨5984998652046067713151787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3989999101364045142101191 5984998652046067713151787)
              ·
                refine ⟨8977497978069101569727681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5984998652046067713151787 8977497978069101569727681)
                ·
                  refine ⟨6733123483551826177295761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8977497978069101569727681 6733123483551826177295761)
                  ·
                    refine ⟨5049842612663869632971821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6733123483551826177295761 5049842612663869632971821)
                    ·
                      refine ⟨1893690979748951112364433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5049842612663869632971821 1893690979748951112364433)
                      ·
                        rfl

theorem cell23_3687950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 1, 2, 2, 3].length) (baseStart_3687950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3687950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3687950 prefixEnd_3687950 := by exact prefixLift 3687950
  have htrace : WordTrace (prefixWord ++ tailWord_3687950) baseStart_3687950 baseEnd_3687950 := by
    simpa [prefixWord, tailWord_3687950, baseEnd_3687950] using wordTrace_append hprefix tailTrace_3687950
  have hstable : (prefixWord ++ tailWord_3687950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687950).length < 2 ^ (prefixWord ++ tailWord_3687950).sum := by decide
  have hdescent : baseEnd_3687950 < baseStart_3687950 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3688023 : List Nat := [1, 1, 3, 2, 2, 3, 2, 3, 1, 2, 3]
def baseStart_3688023 : Nat := 118140960795 + 3688023 * 2 ^ 59
def prefixEnd_3688023 : Nat := 4983230072969 + 3 ^ 40 * 3688023 * 2
def baseEnd_3688023 : Nat := 1893728463836729326751597

theorem tailTrace_3688023 : CollatzResearch.WordTrace tailWord_3688023 prefixEnd_3688023 1893728463836729326751597 := by
  unfold tailWord_3688023
  simp only [CollatzResearch.WordTrace]
  refine ⟨134513249517930010027460723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89675499678620006684973815 134513249517930010027460723)
  ·
    refine ⟨201769874276895015041191085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134513249517930010027460723 201769874276895015041191085)
    ·
      refine ⟨75663702853835630640446657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201769874276895015041191085 75663702853835630640446657)
      ·
        refine ⟨56747777140376722980334993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75663702853835630640446657 56747777140376722980334993)
        ·
          refine ⟨42560832855282542235251245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56747777140376722980334993 42560832855282542235251245)
          ·
            refine ⟨15960312320730953338219217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42560832855282542235251245 15960312320730953338219217)
            ·
              refine ⟨11970234240548215003664413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15960312320730953338219217 11970234240548215003664413)
              ·
                refine ⟨4488837840205580626374155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11970234240548215003664413 4488837840205580626374155)
                ·
                  refine ⟨6733256760308370939561233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4488837840205580626374155 6733256760308370939561233)
                  ·
                    refine ⟨5049942570231278204670925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6733256760308370939561233 5049942570231278204670925)
                    ·
                      refine ⟨1893728463836729326751597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5049942570231278204670925 1893728463836729326751597)
                      ·
                        rfl

theorem cell23_3688023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 3, 1, 2, 3].length) (baseStart_3688023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3688023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3688023 prefixEnd_3688023 := by exact prefixLift 3688023
  have htrace : WordTrace (prefixWord ++ tailWord_3688023) baseStart_3688023 baseEnd_3688023 := by
    simpa [prefixWord, tailWord_3688023, baseEnd_3688023] using wordTrace_append hprefix tailTrace_3688023
  have hstable : (prefixWord ++ tailWord_3688023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3688023).length < 2 ^ (prefixWord ++ tailWord_3688023).sum := by decide
  have hdescent : baseEnd_3688023 < baseStart_3688023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3688023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3688037 : List Nat := [1, 3, 1, 3, 3, 3, 1, 1, 3, 2, 2]
def baseStart_3688037 : Nat := 118140960795 + 3688037 * 2 ^ 59
def prefixEnd_3688037 : Nat := 4983230072969 + 3 ^ 40 * 3688037 * 2
def baseEnd_3688037 : Nat := 1893735652565892271976533

theorem tailTrace_3688037 : CollatzResearch.WordTrace tailWord_3688037 prefixEnd_3688037 1893735652565892271976533 := by
  unfold tailWord_3688037
  simp only [CollatzResearch.WordTrace]
  refine ⟨134513760139879290418470365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89675840093252860278980243 134513760139879290418470365)
  ·
    refine ⟨50442660052454733906926387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134513760139879290418470365 50442660052454733906926387)
    ·
      refine ⟨75663990078682100860389581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50442660052454733906926387 75663990078682100860389581)
      ·
        refine ⟨28373996279505787822646093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75663990078682100860389581 28373996279505787822646093)
        ·
          refine ⟨10640248604814670433492285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28373996279505787822646093 10640248604814670433492285)
          ·
            refine ⟨3990093226805501412559607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10640248604814670433492285 3990093226805501412559607)
            ·
              refine ⟨5985139840208252118839411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3990093226805501412559607 5985139840208252118839411)
              ·
                refine ⟨8977709760312378178259117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5985139840208252118839411 8977709760312378178259117)
                ·
                  refine ⟨3366641160117141816847169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8977709760312378178259117 3366641160117141816847169)
                  ·
                    refine ⟨2524980870087856362635377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3366641160117141816847169 2524980870087856362635377)
                    ·
                      refine ⟨1893735652565892271976533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2524980870087856362635377 1893735652565892271976533)
                      ·
                        rfl

theorem cell23_3688037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 1, 3, 2, 2].length) (baseStart_3688037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3688037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3688037 prefixEnd_3688037 := by exact prefixLift 3688037
  have htrace : WordTrace (prefixWord ++ tailWord_3688037) baseStart_3688037 baseEnd_3688037 := by
    simpa [prefixWord, tailWord_3688037, baseEnd_3688037] using wordTrace_append hprefix tailTrace_3688037
  have hstable : (prefixWord ++ tailWord_3688037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3688037).length < 2 ^ (prefixWord ++ tailWord_3688037).sum := by decide
  have hdescent : baseEnd_3688037 < baseStart_3688037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3688037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3688093 : List Nat := [1, 4, 2, 1, 1, 1, 1, 1, 5, 4, 2]
def baseStart_3688093 : Nat := 118140960795 + 3688093 * 2 ^ 59
def prefixEnd_3688093 : Nat := 4983230072969 + 3 ^ 40 * 3688093 * 2
def baseEnd_3688093 : Nat := 1893764407482544052876275

theorem tailTrace_3688093 : CollatzResearch.WordTrace tailWord_3688093 prefixEnd_3688093 1893764407482544052876275 := by
  unfold tailWord_3688093
  simp only [CollatzResearch.WordTrace]
  refine ⟨134515802627676411982508933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89677201751784274655005955 134515802627676411982508933)
  ·
    refine ⟨25221712992689327246720425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134515802627676411982508933 25221712992689327246720425)
    ·
      refine ⟨18916284744516995435040319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25221712992689327246720425 18916284744516995435040319)
      ·
        refine ⟨28374427116775493152560479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18916284744516995435040319 28374427116775493152560479)
        ·
          refine ⟨42561640675163239728840719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28374427116775493152560479 42561640675163239728840719)
          ·
            refine ⟨63842461012744859593261079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42561640675163239728840719 63842461012744859593261079)
            ·
              refine ⟨95763691519117289389891619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63842461012744859593261079 95763691519117289389891619)
              ·
                refine ⟨143645537278675934084837429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95763691519117289389891619 143645537278675934084837429)
                ·
                  refine ⟨13466769119875868820453509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 143645537278675934084837429 13466769119875868820453509)
                  ·
                    refine ⟨2525019209976725403835033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13466769119875868820453509 2525019209976725403835033)
                    ·
                      refine ⟨1893764407482544052876275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2525019209976725403835033 1893764407482544052876275)
                      ·
                        rfl

theorem cell23_3688093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 5, 4, 2].length) (baseStart_3688093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3688093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3688093 prefixEnd_3688093 := by exact prefixLift 3688093
  have htrace : WordTrace (prefixWord ++ tailWord_3688093) baseStart_3688093 baseEnd_3688093 := by
    simpa [prefixWord, tailWord_3688093, baseEnd_3688093] using wordTrace_append hprefix tailTrace_3688093
  have hstable : (prefixWord ++ tailWord_3688093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3688093).length < 2 ^ (prefixWord ++ tailWord_3688093).sum := by decide
  have hdescent : baseEnd_3688093 < baseStart_3688093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3688093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3688104 : List Nat := [2, 1, 7, 1, 1, 1, 2, 1, 1, 3, 3]
def baseStart_3688104 : Nat := 118140960795 + 3688104 * 2 ^ 59
def prefixEnd_3688104 : Nat := 4983230072969 + 3 ^ 40 * 3688104 * 2
def baseEnd_3688104 : Nat := 1893770055769743509838725

theorem tailTrace_3688104 : CollatzResearch.WordTrace tailWord_3688104 prefixEnd_3688104 1893770055769743509838725 := by
  unfold tailWord_3688104
  simp only [CollatzResearch.WordTrace]
  refine ⟨67258101915318280430579683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89677469220424373907439577 67258101915318280430579683)
  ·
    refine ⟨100887152872977420645869525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67258101915318280430579683 100887152872977420645869525)
    ·
      refine ⟨2364542645460408296387567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 100887152872977420645869525 2364542645460408296387567)
      ·
        refine ⟨3546813968190612444581351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2364542645460408296387567 3546813968190612444581351)
        ·
          refine ⟨5320220952285918666872027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3546813968190612444581351 5320220952285918666872027)
          ·
            refine ⟨7980331428428878000308041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5320220952285918666872027 7980331428428878000308041)
            ·
              refine ⟨5985248571321658500231031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7980331428428878000308041 5985248571321658500231031)
              ·
                refine ⟨8977872856982487750346547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5985248571321658500231031 8977872856982487750346547)
                ·
                  refine ⟨13466809285473731625519821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8977872856982487750346547 13466809285473731625519821)
                  ·
                    refine ⟨5050053482052649359569933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13466809285473731625519821 5050053482052649359569933)
                    ·
                      refine ⟨1893770055769743509838725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5050053482052649359569933 1893770055769743509838725)
                      ·
                        rfl

theorem cell23_3688104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_3688104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3688104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3688104 prefixEnd_3688104 := by exact prefixLift 3688104
  have htrace : WordTrace (prefixWord ++ tailWord_3688104) baseStart_3688104 baseEnd_3688104 := by
    simpa [prefixWord, tailWord_3688104, baseEnd_3688104] using wordTrace_append hprefix tailTrace_3688104
  have hstable : (prefixWord ++ tailWord_3688104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3688104).length < 2 ^ (prefixWord ++ tailWord_3688104).sum := by decide
  have hdescent : baseEnd_3688104 < baseStart_3688104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3688104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3688183 : List Nat := [1, 1, 3, 1, 1, 1, 4, 2, 1, 6, 2]
def baseStart_3688183 : Nat := 118140960795 + 3688183 * 2 ^ 59
def prefixEnd_3688183 : Nat := 4983230072969 + 3 ^ 40 * 3688183 * 2
def baseEnd_3688183 : Nat := 1893810620741448700750861

theorem tailTrace_3688183 : CollatzResearch.WordTrace tailWord_3688183 prefixEnd_3688183 1893810620741448700750861 := by
  unfold tailWord_3688183
  simp only [CollatzResearch.WordTrace]
  refine ⟨134519085197350357353285203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89679390131566904902190135 134519085197350357353285203)
  ·
    refine ⟨201778627796025536029927805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134519085197350357353285203 201778627796025536029927805)
    ·
      refine ⟨75666985423509576011222927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201778627796025536029927805 75666985423509576011222927)
      ·
        refine ⟨113500478135264364016834391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75666985423509576011222927 113500478135264364016834391)
        ·
          refine ⟨170250717202896546025251587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113500478135264364016834391 170250717202896546025251587)
          ·
            refine ⟨255376075804344819037877381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170250717202896546025251587 255376075804344819037877381)
            ·
              refine ⟨47883014213314653569602009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 255376075804344819037877381 47883014213314653569602009)
              ·
                refine ⟨35912260659985990177201507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47883014213314653569602009 35912260659985990177201507)
                ·
                  refine ⟨53868390989978985265802261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35912260659985990177201507 53868390989978985265802261)
                  ·
                    refine ⟨2525080827655264934334481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 53868390989978985265802261 2525080827655264934334481)
                    ·
                      refine ⟨1893810620741448700750861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2525080827655264934334481 1893810620741448700750861)
                      ·
                        rfl

theorem cell23_3688183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 6, 2].length) (baseStart_3688183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3688183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3688183 prefixEnd_3688183 := by exact prefixLift 3688183
  have htrace : WordTrace (prefixWord ++ tailWord_3688183) baseStart_3688183 baseEnd_3688183 := by
    simpa [prefixWord, tailWord_3688183, baseEnd_3688183] using wordTrace_append hprefix tailTrace_3688183
  have hstable : (prefixWord ++ tailWord_3688183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3688183).length < 2 ^ (prefixWord ++ tailWord_3688183).sum := by decide
  have hdescent : baseEnd_3688183 < baseStart_3688183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3688183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3688186 : List Nat := [3, 1, 1, 1, 1, 3, 1, 2, 2, 3, 5]
def baseStart_3688186 : Nat := 118140960795 + 3688186 * 2 ^ 59
def prefixEnd_3688186 : Nat := 4983230072969 + 3 ^ 40 * 3688186 * 2
def baseEnd_3688186 : Nat := 1893812161183412189013347

theorem tailTrace_3688186 : CollatzResearch.WordTrace tailWord_3688186 prefixEnd_3688186 1893812161183412189013347 := by
  unfold tailWord_3688186
  simp only [CollatzResearch.WordTrace]
  refine ⟨33629798654084872216411103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89679463077559659243762941 33629798654084872216411103)
  ·
    refine ⟨50444697981127308324616655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33629798654084872216411103 50444697981127308324616655)
    ·
      refine ⟨75667046971690962486924983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50444697981127308324616655 75667046971690962486924983)
      ·
        refine ⟨113500570457536443730387475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75667046971690962486924983 113500570457536443730387475)
        ·
          refine ⟨170250855686304665595581213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113500570457536443730387475 170250855686304665595581213)
          ·
            refine ⟨63844070882364249598342955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170250855686304665595581213 63844070882364249598342955)
            ·
              refine ⟨95766106323546374397514433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63844070882364249598342955 95766106323546374397514433)
              ·
                refine ⟨71824579742659780798135825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95766106323546374397514433 71824579742659780798135825)
                ·
                  refine ⟨53868434806994835598601869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71824579742659780798135825 53868434806994835598601869)
                  ·
                    refine ⟨20200663052623063349475701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53868434806994835598601869 20200663052623063349475701)
                    ·
                      refine ⟨1893812161183412189013347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20200663052623063349475701 1893812161183412189013347)
                      ·
                        rfl

theorem cell23_3688186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 2, 3, 5].length) (baseStart_3688186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3688186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3688186 prefixEnd_3688186 := by exact prefixLift 3688186
  have htrace : WordTrace (prefixWord ++ tailWord_3688186) baseStart_3688186 baseEnd_3688186 := by
    simpa [prefixWord, tailWord_3688186, baseEnd_3688186] using wordTrace_append hprefix tailTrace_3688186
  have hstable : (prefixWord ++ tailWord_3688186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3688186).length < 2 ^ (prefixWord ++ tailWord_3688186).sum := by decide
  have hdescent : baseEnd_3688186 < baseStart_3688186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3688186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3688193 : List Nat := [1, 2, 4, 1, 1, 1, 2, 2, 5, 4]
def baseStart_3688193 : Nat := 118140960795 + 3688193 * 2 ^ 59
def prefixEnd_3688193 : Nat := 4983230072969 + 3 ^ 40 * 3688193 * 2
def baseEnd_3688193 : Nat := 631271918515997887208605

theorem tailTrace_3688193 : CollatzResearch.WordTrace tailWord_3688193 prefixEnd_3688193 631271918515997887208605 := by
  unfold tailWord_3688193
  simp only [CollatzResearch.WordTrace]
  refine ⟨134519449927314129061149233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89679633284876086040766155 134519449927314129061149233)
  ·
    refine ⟨100889587445485596795861925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134519449927314129061149233 100889587445485596795861925)
    ·
      refine ⟨18916797646028549399224111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100889587445485596795861925 18916797646028549399224111)
      ·
        refine ⟨28375196469042824098836167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18916797646028549399224111 28375196469042824098836167)
        ·
          refine ⟨42562794703564236148254251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28375196469042824098836167 42562794703564236148254251)
          ·
            refine ⟨63844192055346354222381377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42562794703564236148254251 63844192055346354222381377)
            ·
              refine ⟨47883144041509765666786033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63844192055346354222381377 47883144041509765666786033)
              ·
                refine ⟨35912358031132324250089525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47883144041509765666786033 35912358031132324250089525)
                ·
                  refine ⟨3366783565418655398445893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35912358031132324250089525 3366783565418655398445893)
                  ·
                    refine ⟨631271918515997887208605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3366783565418655398445893 631271918515997887208605)
                    ·
                      rfl

theorem cell23_3688193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 5, 4].length) (baseStart_3688193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3688193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3688193 prefixEnd_3688193 := by exact prefixLift 3688193
  have htrace : WordTrace (prefixWord ++ tailWord_3688193) baseStart_3688193 baseEnd_3688193 := by
    simpa [prefixWord, tailWord_3688193, baseEnd_3688193] using wordTrace_append hprefix tailTrace_3688193
  have hstable : (prefixWord ++ tailWord_3688193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3688193).length < 2 ^ (prefixWord ++ tailWord_3688193).sum := by decide
  have hdescent : baseEnd_3688193 < baseStart_3688193 := by decide
  rcases family_descends (prefixWord ++ tailWord_3688193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3688203 : List Nat := [1, 1, 1, 1, 5, 1, 3, 1, 4, 2, 3]
def baseStart_3688203 : Nat := 118140960795 + 3688203 * 2 ^ 59
def prefixEnd_3688203 : Nat := 4983230072969 + 3 ^ 40 * 3688203 * 2
def baseEnd_3688203 : Nat := 1893820890354538622500769

theorem tailTrace_3688203 : CollatzResearch.WordTrace tailWord_3688203 prefixEnd_3688203 1893820890354538622500769 := by
  unfold tailWord_3688203
  simp only [CollatzResearch.WordTrace]
  refine ⟨134519814657277900769013263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89679876438185267179342175 134519814657277900769013263)
  ·
    refine ⟨201779721985916851153519895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134519814657277900769013263 201779721985916851153519895)
    ·
      refine ⟨302669582978875276730279843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201779721985916851153519895 302669582978875276730279843)
      ·
        refine ⟨454004374468312915095419765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302669582978875276730279843 454004374468312915095419765)
        ·
          refine ⟨42562910106404335790195603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 454004374468312915095419765 42562910106404335790195603)
          ·
            refine ⟨63844365159606503685293405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42562910106404335790195603 63844365159606503685293405)
            ·
              refine ⟨23941636934852438881985027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63844365159606503685293405 23941636934852438881985027)
              ·
                refine ⟨35912455402278658322977541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23941636934852438881985027 35912455402278658322977541)
                ·
                  refine ⟨6733585387927248435558289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35912455402278658322977541 6733585387927248435558289)
                  ·
                    refine ⟨5050189040945436326668717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6733585387927248435558289 5050189040945436326668717)
                    ·
                      refine ⟨1893820890354538622500769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5050189040945436326668717 1893820890354538622500769)
                      ·
                        rfl

theorem cell23_3688203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 4, 2, 3].length) (baseStart_3688203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3688203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3688203 prefixEnd_3688203 := by exact prefixLift 3688203
  have htrace : WordTrace (prefixWord ++ tailWord_3688203) baseStart_3688203 baseEnd_3688203 := by
    simpa [prefixWord, tailWord_3688203, baseEnd_3688203] using wordTrace_append hprefix tailTrace_3688203
  have hstable : (prefixWord ++ tailWord_3688203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3688203).length < 2 ^ (prefixWord ++ tailWord_3688203).sum := by decide
  have hdescent : baseEnd_3688203 < baseStart_3688203 := by decide
  rcases family_descends (prefixWord ++ tailWord_3688203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3688212 : List Nat := [2, 4, 4, 1, 2, 1, 2, 1, 2, 2, 2]
def baseStart_3688212 : Nat := 118140960795 + 3688212 * 2 ^ 59
def prefixEnd_3688212 : Nat := 4983230072969 + 3 ^ 40 * 3688212 * 2
def baseEnd_3688212 : Nat := 1893825511680429087288229

theorem tailTrace_3688212 : CollatzResearch.WordTrace tailWord_3688212 prefixEnd_3688212 1893825511680429087288229 := by
  unfold tailWord_3688212
  simp only [CollatzResearch.WordTrace]
  refine ⟨67260071457122647653045445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89680095276163530204060593 67260071457122647653045445)
  ·
    refine ⟨12611263398210496434946021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67260071457122647653045445 12611263398210496434946021)
    ·
      refine ⟨2364611887164468081552379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12611263398210496434946021 2364611887164468081552379)
      ·
        refine ⟨3546917830746702122328569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2364611887164468081552379 3546917830746702122328569)
        ·
          refine ⟨2660188373060026591746427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3546917830746702122328569 2660188373060026591746427)
          ·
            refine ⟨3990282559590039887619641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2660188373060026591746427 3990282559590039887619641)
            ·
              refine ⟨2992711919692529915714731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3990282559590039887619641 2992711919692529915714731)
              ·
                refine ⟨4489067879538794873572097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2992711919692529915714731 4489067879538794873572097)
                ·
                  refine ⟨3366800909654096155179073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4489067879538794873572097 3366800909654096155179073)
                  ·
                    refine ⟨2525100682240572116384305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3366800909654096155179073 2525100682240572116384305)
                    ·
                      refine ⟨1893825511680429087288229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2525100682240572116384305 1893825511680429087288229)
                      ·
                        rfl

theorem cell23_3688212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_3688212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3688212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3688212 prefixEnd_3688212 := by exact prefixLift 3688212
  have htrace : WordTrace (prefixWord ++ tailWord_3688212) baseStart_3688212 baseEnd_3688212 := by
    simpa [prefixWord, tailWord_3688212, baseEnd_3688212] using wordTrace_append hprefix tailTrace_3688212
  have hstable : (prefixWord ++ tailWord_3688212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3688212).length < 2 ^ (prefixWord ++ tailWord_3688212).sum := by decide
  have hdescent : baseEnd_3688212 < baseStart_3688212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3688212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3688223 : List Nat := [1, 1, 2, 4, 2, 1, 3, 3, 6]
def baseStart_3688223 : Nat := 118140960795 + 3688223 * 2 ^ 59
def prefixEnd_3688223 : Nat := 4983230072969 + 3 ^ 40 * 3688223 * 2
def baseEnd_3688223 : Nat := 210425684440847616027853

theorem tailTrace_3688223 : CollatzResearch.WordTrace tailWord_3688223 prefixEnd_3688223 210425684440847616027853 := by
  unfold tailWord_3688223
  simp only [CollatzResearch.WordTrace]
  refine ⟨134520544117205444184741323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89680362744803629456494215 134520544117205444184741323)
  ·
    refine ⟨201780816175808166277111985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134520544117205444184741323 201780816175808166277111985)
    ·
      refine ⟨151335612131856124707833989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201780816175808166277111985 151335612131856124707833989)
      ·
        refine ⟨28375427274723023382718873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 151335612131856124707833989 28375427274723023382718873)
        ·
          refine ⟨21281570456042267537039155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28375427274723023382718873 21281570456042267537039155)
          ·
            refine ⟨31922355684063401305558733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21281570456042267537039155 31922355684063401305558733)
            ·
              refine ⟨11970883381523775489584525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31922355684063401305558733 11970883381523775489584525)
              ·
                refine ⟨4489081268071415808594197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11970883381523775489584525 4489081268071415808594197)
                ·
                  refine ⟨210425684440847616027853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4489081268071415808594197 210425684440847616027853)
                  ·
                    rfl

theorem cell23_3688223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 3, 6].length) (baseStart_3688223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3688223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3688223 prefixEnd_3688223 := by exact prefixLift 3688223
  have htrace : WordTrace (prefixWord ++ tailWord_3688223) baseStart_3688223 baseEnd_3688223 := by
    simpa [prefixWord, tailWord_3688223, baseEnd_3688223] using wordTrace_append hprefix tailTrace_3688223
  have hstable : (prefixWord ++ tailWord_3688223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3688223).length < 2 ^ (prefixWord ++ tailWord_3688223).sum := by decide
  have hdescent : baseEnd_3688223 < baseStart_3688223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3688223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3688284 : List Nat := [2, 2, 4, 2, 2, 1, 1, 2, 3, 1, 3]
def baseStart_3688284 : Nat := 118140960795 + 3688284 * 2 ^ 59
def prefixEnd_3688284 : Nat := 4983230072969 + 3 ^ 40 * 3688284 * 2
def baseEnd_3688284 : Nat := 1893862482287552805587897

theorem tailTrace_3688284 : CollatzResearch.WordTrace tailWord_3688284 prefixEnd_3688284 1893862482287552805587897 := by
  unfold tailWord_3688284
  simp only [CollatzResearch.WordTrace]
  refine ⟨67261384484992225801355953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89681845979989634401807937 67261384484992225801355953)
  ·
    refine ⟨50446038363744169351016965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67261384484992225801355953 50446038363744169351016965)
    ·
      refine ⟨9458632193202031753315681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50446038363744169351016965 9458632193202031753315681)
      ·
        refine ⟨7093974144901523814986761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9458632193202031753315681 7093974144901523814986761)
        ·
          refine ⟨5320480608676142861240071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7093974144901523814986761 5320480608676142861240071)
          ·
            refine ⟨7980720913014214291860107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5320480608676142861240071 7980720913014214291860107)
            ·
              refine ⟨11971081369521321437790161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7980720913014214291860107 11971081369521321437790161)
              ·
                refine ⟨8978311027140991078342621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11971081369521321437790161 8978311027140991078342621)
                ·
                  refine ⟨3366866635177871654378483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8978311027140991078342621 3366866635177871654378483)
                  ·
                    refine ⟨5050299952766807481567725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3366866635177871654378483 5050299952766807481567725)
                    ·
                      refine ⟨1893862482287552805587897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5050299952766807481567725 1893862482287552805587897)
                      ·
                        rfl

theorem cell23_3688284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_3688284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3688284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3688284 prefixEnd_3688284 := by exact prefixLift 3688284
  have htrace : WordTrace (prefixWord ++ tailWord_3688284) baseStart_3688284 baseEnd_3688284 := by
    simpa [prefixWord, tailWord_3688284, baseEnd_3688284] using wordTrace_append hprefix tailTrace_3688284
  have hstable : (prefixWord ++ tailWord_3688284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3688284).length < 2 ^ (prefixWord ++ tailWord_3688284).sum := by decide
  have hdescent : baseEnd_3688284 < baseStart_3688284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3688284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3688334 : List Nat := [4, 1, 1, 5, 1, 2, 1, 1, 1, 6]
def baseStart_3688334 : Nat := 118140960795 + 3688334 * 2 ^ 59
def prefixEnd_3688334 : Nat := 4983230072969 + 3 ^ 40 * 3688334 * 2
def baseEnd_3688334 : Nat := 631296052106759203320889

theorem tailTrace_3688334 : CollatzResearch.WordTrace tailWord_3688334 prefixEnd_3688334 631296052106759203320889 := by
  unfold tailWord_3688334
  simp only [CollatzResearch.WordTrace]
  refine ⟨16815574077475413767754007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89683061746535540094688037 16815574077475413767754007)
  ·
    refine ⟨25223361116213120651631011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16815574077475413767754007 25223361116213120651631011)
    ·
      refine ⟨37835041674319680977446517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25223361116213120651631011 37835041674319680977446517)
      ·
        refine ⟨3547035156967470091635611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37835041674319680977446517 3547035156967470091635611)
        ·
          refine ⟨5320552735451205137453417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3547035156967470091635611 5320552735451205137453417)
          ·
            refine ⟨3990414551588403853090063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5320552735451205137453417 3990414551588403853090063)
            ·
              refine ⟨5985621827382605779635095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3990414551588403853090063 5985621827382605779635095)
              ·
                refine ⟨8978432741073908669452643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5985621827382605779635095 8978432741073908669452643)
                ·
                  refine ⟨13467649111610863004178965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8978432741073908669452643 13467649111610863004178965)
                  ·
                    refine ⟨631296052106759203320889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13467649111610863004178965 631296052106759203320889)
                    ·
                      rfl

theorem cell23_3688334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 1, 1, 6].length) (baseStart_3688334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3688334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3688334 prefixEnd_3688334 := by exact prefixLift 3688334
  have htrace : WordTrace (prefixWord ++ tailWord_3688334) baseStart_3688334 baseEnd_3688334 := by
    simpa [prefixWord, tailWord_3688334, baseEnd_3688334] using wordTrace_append hprefix tailTrace_3688334
  have hstable : (prefixWord ++ tailWord_3688334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3688334).length < 2 ^ (prefixWord ++ tailWord_3688334).sum := by decide
  have hdescent : baseEnd_3688334 < baseStart_3688334 := by decide
  rcases family_descends (prefixWord ++ tailWord_3688334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3688367 : List Nat := [1, 1, 2, 1, 2, 2, 3, 5, 1, 3, 2]
def baseStart_3688367 : Nat := 118140960795 + 3688367 * 2 ^ 59
def prefixEnd_3688367 : Nat := 4983230072969 + 3 ^ 40 * 3688367 * 2
def baseEnd_3688367 : Nat := 1893905101181875980850015

theorem tailTrace_3688367 : CollatzResearch.WordTrace tailWord_3688367 prefixEnd_3688367 1893905101181875980850015 := by
  unfold tailWord_3688367
  simp only [CollatzResearch.WordTrace]
  refine ⟨134525796228683756777983355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89683864152455837851988903 134525796228683756777983355)
  ·
    refine ⟨201788694343025635166975033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134525796228683756777983355 201788694343025635166975033)
    ·
      refine ⟨151341520757269226375231275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201788694343025635166975033 151341520757269226375231275)
      ·
        refine ⟨227012281135903839562846913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151341520757269226375231275 227012281135903839562846913)
        ·
          refine ⟨170259210851927879672135185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227012281135903839562846913 170259210851927879672135185)
          ·
            refine ⟨127694408138945909754101389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170259210851927879672135185 127694408138945909754101389)
            ·
              refine ⟨47885403052104716157788021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127694408138945909754101389 47885403052104716157788021)
              ·
                refine ⟨4489256536134817139792627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47885403052104716157788021 4489256536134817139792627)
                ·
                  refine ⟨6733884804202225709688941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4489256536134817139792627 6733884804202225709688941)
                  ·
                    refine ⟨2525206801575834641133353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6733884804202225709688941 2525206801575834641133353)
                    ·
                      refine ⟨1893905101181875980850015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2525206801575834641133353 1893905101181875980850015)
                      ·
                        rfl

theorem cell23_3688367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 5, 1, 3, 2].length) (baseStart_3688367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3688367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3688367 prefixEnd_3688367 := by exact prefixLift 3688367
  have htrace : WordTrace (prefixWord ++ tailWord_3688367) baseStart_3688367 baseEnd_3688367 := by
    simpa [prefixWord, tailWord_3688367, baseEnd_3688367] using wordTrace_append hprefix tailTrace_3688367
  have hstable : (prefixWord ++ tailWord_3688367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3688367).length < 2 ^ (prefixWord ++ tailWord_3688367).sum := by decide
  have hdescent : baseEnd_3688367 < baseStart_3688367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3688367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3688383 : List Nat := [1, 1, 2, 2, 2, 1, 3, 2, 1, 3, 5]
def baseStart_3688383 : Nat := 118140960795 + 3688383 * 2 ^ 59
def prefixEnd_3688383 : Nat := 4983230072969 + 3 ^ 40 * 3688383 * 2
def baseEnd_3688383 : Nat := 1893913316872347918249941

theorem tailTrace_3688383 : CollatzResearch.WordTrace tailWord_3688383 prefixEnd_3688383 1893913316872347918249941 := by
  unfold tailWord_3688383
  simp only [CollatzResearch.WordTrace]
  refine ⟨134526379796625791510565803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89684253197750527673710535 134526379796625791510565803)
  ·
    refine ⟨201789569694938687265848705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134526379796625791510565803 201789569694938687265848705)
    ·
      refine ⟨151342177271204015449386529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201789569694938687265848705 151342177271204015449386529)
      ·
        refine ⟨113506632953403011587039897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151342177271204015449386529 113506632953403011587039897)
        ·
          refine ⟨85129974715052258690279923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113506632953403011587039897 85129974715052258690279923)
          ·
            refine ⟨127694962072578388035419885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85129974715052258690279923 127694962072578388035419885)
            ·
              refine ⟨47885610777216895513282457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127694962072578388035419885 47885610777216895513282457)
              ·
                refine ⟨35914208082912671634961843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47885610777216895513282457 35914208082912671634961843)
                ·
                  refine ⟨53871312124369007452442765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35914208082912671634961843 53871312124369007452442765)
                  ·
                    refine ⟨20201742046638377794666037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53871312124369007452442765 20201742046638377794666037)
                    ·
                      refine ⟨1893913316872347918249941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20201742046638377794666037 1893913316872347918249941)
                      ·
                        rfl

theorem cell23_3688383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 3, 5].length) (baseStart_3688383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3688383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3688383 prefixEnd_3688383 := by exact prefixLift 3688383
  have htrace : WordTrace (prefixWord ++ tailWord_3688383) baseStart_3688383 baseEnd_3688383 := by
    simpa [prefixWord, tailWord_3688383, baseEnd_3688383] using wordTrace_append hprefix tailTrace_3688383
  have hstable : (prefixWord ++ tailWord_3688383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3688383).length < 2 ^ (prefixWord ++ tailWord_3688383).sum := by decide
  have hdescent : baseEnd_3688383 < baseStart_3688383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3688383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3688497 : List Nat := [1, 2, 2, 3, 1, 3, 1, 3, 3, 4]
def baseStart_3688497 : Nat := 118140960795 + 3688497 * 2 ^ 59
def prefixEnd_3688497 : Nat := 4983230072969 + 3 ^ 40 * 3688497 * 2
def baseEnd_3688497 : Nat := 631323951222320157408139

theorem tailTrace_3688497 : CollatzResearch.WordTrace tailWord_3688497 prefixEnd_3688497 631323951222320157408139 := by
  unfold tailWord_3688497
  simp only [CollatzResearch.WordTrace]
  refine ⟨134530537718212788980215745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89687025145475192653477163 134530537718212788980215745)
  ·
    refine ⟨100897903288659591735161809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134530537718212788980215745 100897903288659591735161809)
    ·
      refine ⟨75673427466494693801371357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100897903288659591735161809 75673427466494693801371357)
      ·
        refine ⟨28377535299935510175514259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75673427466494693801371357 28377535299935510175514259)
        ·
          refine ⟨42566302949903265263271389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28377535299935510175514259 42566302949903265263271389)
          ·
            refine ⟨15962363606213724473726771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42566302949903265263271389 15962363606213724473726771)
            ·
              refine ⟨23943545409320586710590157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15962363606213724473726771 23943545409320586710590157)
              ·
                refine ⟨8978829528495220016471309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23943545409320586710590157 8978829528495220016471309)
                ·
                  refine ⟨3367061073185707506176741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8978829528495220016471309 3367061073185707506176741)
                  ·
                    refine ⟨631323951222320157408139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3367061073185707506176741 631323951222320157408139)
                    ·
                      rfl

theorem cell23_3688497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 3, 3, 4].length) (baseStart_3688497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3688497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3688497 prefixEnd_3688497 := by exact prefixLift 3688497
  have htrace : WordTrace (prefixWord ++ tailWord_3688497) baseStart_3688497 baseEnd_3688497 := by
    simpa [prefixWord, tailWord_3688497, baseEnd_3688497] using wordTrace_append hprefix tailTrace_3688497
  have hstable : (prefixWord ++ tailWord_3688497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3688497).length < 2 ^ (prefixWord ++ tailWord_3688497).sum := by decide
  have hdescent : baseEnd_3688497 < baseStart_3688497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3688497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3688541 : List Nat := [1, 4, 4, 1, 1, 2, 1, 2, 2, 2, 3]
def baseStart_3688541 : Nat := 118140960795 + 3688541 * 2 ^ 59
def prefixEnd_3688541 : Nat := 4983230072969 + 3 ^ 40 * 3688541 * 2
def baseEnd_3688541 : Nat := 1893994446815758300074215

theorem tailTrace_3688541 : CollatzResearch.WordTrace tailWord_3688541 prefixEnd_3688541 1893994446815758300074215 := by
  unfold tailWord_3688541
  simp only [CollatzResearch.WordTrace]
  refine ⟨134532142530053384494817477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89688095020035589663211651 134532142530053384494817477)
  ·
    refine ⟨25224776724385009592778277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134532142530053384494817477 25224776724385009592778277)
    ·
      refine ⟨4729645635822189298645927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25224776724385009592778277 4729645635822189298645927)
      ·
        refine ⟨7094468453733283947968891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4729645635822189298645927 7094468453733283947968891)
        ·
          refine ⟨10641702680599925921953337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7094468453733283947968891 10641702680599925921953337)
          ·
            refine ⟨7981277010449944441465003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10641702680599925921953337 7981277010449944441465003)
            ·
              refine ⟨11971915515674916662197505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7981277010449944441465003 11971915515674916662197505)
              ·
                refine ⟨8978936636756187496648129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11971915515674916662197505 8978936636756187496648129)
                ·
                  refine ⟨6734202477567140622486097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8978936636756187496648129 6734202477567140622486097)
                  ·
                    refine ⟨5050651858175355466864573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6734202477567140622486097 5050651858175355466864573)
                    ·
                      refine ⟨1893994446815758300074215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5050651858175355466864573 1893994446815758300074215)
                      ·
                        rfl

theorem cell23_3688541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_3688541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3688541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3688541 prefixEnd_3688541 := by exact prefixLift 3688541
  have htrace : WordTrace (prefixWord ++ tailWord_3688541) baseStart_3688541 baseEnd_3688541 := by
    simpa [prefixWord, tailWord_3688541, baseEnd_3688541] using wordTrace_append hprefix tailTrace_3688541
  have hstable : (prefixWord ++ tailWord_3688541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3688541).length < 2 ^ (prefixWord ++ tailWord_3688541).sum := by decide
  have hdescent : baseEnd_3688541 < baseStart_3688541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3688541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3688557 : List Nat := [1, 5, 1, 1, 2, 1, 2, 2, 3, 5]
def baseStart_3688557 : Nat := 118140960795 + 3688557 * 2 ^ 59
def prefixEnd_3688557 : Nat := 4983230072969 + 3 ^ 40 * 3688557 * 2
def baseEnd_3688557 : Nat := 631334220835410079158047

theorem tailTrace_3688557 : CollatzResearch.WordTrace tailWord_3688557 prefixEnd_3688557 631334220835410079158047 := by
  unfold tailWord_3688557
  simp only [CollatzResearch.WordTrace]
  refine ⟨134532726097995419227399925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89688484065330279484933283 134532726097995419227399925)
  ·
    refine ⟨12612443071687070552568743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 134532726097995419227399925 12612443071687070552568743)
    ·
      refine ⟨18918664607530605828853115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12612443071687070552568743 18918664607530605828853115)
      ·
        refine ⟨28377996911295908743279673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18918664607530605828853115 28377996911295908743279673)
        ·
          refine ⟨21283497683471931557459755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28377996911295908743279673 21283497683471931557459755)
          ·
            refine ⟨31925246525207897336189633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21283497683471931557459755 31925246525207897336189633)
            ·
              refine ⟨23943934893905923002142225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31925246525207897336189633 23943934893905923002142225)
              ·
                refine ⟨17957951170429442251606669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23943934893905923002142225 17957951170429442251606669)
                ·
                  refine ⟨6734231688911040844352501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17957951170429442251606669 6734231688911040844352501)
                  ·
                    refine ⟨631334220835410079158047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6734231688911040844352501 631334220835410079158047)
                    ·
                      rfl

theorem cell23_3688557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 2, 3, 5].length) (baseStart_3688557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3688557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3688557 prefixEnd_3688557 := by exact prefixLift 3688557
  have htrace : WordTrace (prefixWord ++ tailWord_3688557) baseStart_3688557 baseEnd_3688557 := by
    simpa [prefixWord, tailWord_3688557, baseEnd_3688557] using wordTrace_append hprefix tailTrace_3688557
  have hstable : (prefixWord ++ tailWord_3688557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3688557).length < 2 ^ (prefixWord ++ tailWord_3688557).sum := by decide
  have hdescent : baseEnd_3688557 < baseStart_3688557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3688557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3688570 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 7, 6]
def baseStart_3688570 : Nat := 118140960795 + 3688570 * 2 ^ 59
def prefixEnd_3688570 : Nat := 4983230072969 + 3 ^ 40 * 3688570 * 2
def baseEnd_3688570 : Nat := 631336445918246228870527

theorem tailTrace_3688570 : CollatzResearch.WordTrace tailWord_3688570 prefixEnd_3688570 631336445918246228870527 := by
  unfold tailWord_3688570
  simp only [CollatzResearch.WordTrace]
  refine ⟨33633300061737080611905791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89688800164632214965082109 33633300061737080611905791)
  ·
    refine ⟨50449950092605620917858687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33633300061737080611905791 50449950092605620917858687)
    ·
      refine ⟨75674925138908431376788031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50449950092605620917858687 75674925138908431376788031)
      ·
        refine ⟨113512387708362647065182047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75674925138908431376788031 113512387708362647065182047)
        ·
          refine ⟨170268581562543970597773071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113512387708362647065182047 170268581562543970597773071)
          ·
            refine ⟨255402872343815955896659607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170268581562543970597773071 255402872343815955896659607)
            ·
              refine ⟨383104308515723933844989411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255402872343815955896659607 383104308515723933844989411)
              ·
                refine ⟨574656462773585900767484117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 383104308515723933844989411 574656462773585900767484117)
                ·
                  refine ⟨13468510846255919549237909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 574656462773585900767484117 13468510846255919549237909)
                  ·
                    refine ⟨631336445918246228870527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13468510846255919549237909 631336445918246228870527)
                    ·
                      rfl

theorem cell23_3688570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 7, 6].length) (baseStart_3688570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3688570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3688570 prefixEnd_3688570 := by exact prefixLift 3688570
  have htrace : WordTrace (prefixWord ++ tailWord_3688570) baseStart_3688570 baseEnd_3688570 := by
    simpa [prefixWord, tailWord_3688570, baseEnd_3688570] using wordTrace_append hprefix tailTrace_3688570
  have hstable : (prefixWord ++ tailWord_3688570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3688570).length < 2 ^ (prefixWord ++ tailWord_3688570).sum := by decide
  have hdescent : baseEnd_3688570 < baseStart_3688570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3688570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3688581 : List Nat := [1, 3, 1, 1, 5, 2, 2, 1, 2, 3, 2]
def baseStart_3688581 : Nat := 118140960795 + 3688581 * 2 ^ 59
def prefixEnd_3688581 : Nat := 4983230072969 + 3 ^ 40 * 3688581 * 2
def baseEnd_3688581 : Nat := 1894014986041938143574031

theorem tailTrace_3688581 : CollatzResearch.WordTrace tailWord_3688581 prefixEnd_3688581 1894014986041938143574031 := by
  unfold tailWord_3688581
  simp only [CollatzResearch.WordTrace]
  refine ⟨134533601449908471326273597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89689067633272314217515731 134533601449908471326273597)
  ·
    refine ⟨50450100543715676747352599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134533601449908471326273597 50450100543715676747352599)
    ·
      refine ⟨75675150815573515121028899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50450100543715676747352599 75675150815573515121028899)
      ·
        refine ⟨113512726223360272681543349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75675150815573515121028899 113512726223360272681543349)
        ·
          refine ⟨10641818083440025563894689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 113512726223360272681543349 10641818083440025563894689)
          ·
            refine ⟨7981363562580019172921017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10641818083440025563894689 7981363562580019172921017)
            ·
              refine ⟨5986022671935014379690763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7981363562580019172921017 5986022671935014379690763)
              ·
                refine ⟨8979034007902521569536145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5986022671935014379690763 8979034007902521569536145)
                ·
                  refine ⟨6734275505926891177152109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8979034007902521569536145 6734275505926891177152109)
                  ·
                    refine ⟨2525353314722584191432041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6734275505926891177152109 2525353314722584191432041)
                    ·
                      refine ⟨1894014986041938143574031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2525353314722584191432041 1894014986041938143574031)
                      ·
                        rfl

theorem cell23_3688581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 1, 2, 3, 2].length) (baseStart_3688581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3688581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3688581 prefixEnd_3688581 := by exact prefixLift 3688581
  have htrace : WordTrace (prefixWord ++ tailWord_3688581) baseStart_3688581 baseEnd_3688581 := by
    simpa [prefixWord, tailWord_3688581, baseEnd_3688581] using wordTrace_append hprefix tailTrace_3688581
  have hstable : (prefixWord ++ tailWord_3688581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3688581).length < 2 ^ (prefixWord ++ tailWord_3688581).sum := by decide
  have hdescent : baseEnd_3688581 < baseStart_3688581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3688581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3688600 : List Nat := [2, 1, 2, 4, 14]
def baseStart_3688600 : Nat := 118140960795 + 3688600 * 2 ^ 59
def prefixEnd_3688600 : Nat := 4983230072969 + 3 ^ 40 * 3688600 * 2
def baseEnd_3688600 : Nat := 2598113500925066624467

theorem tailTrace_3688600 : CollatzResearch.WordTrace tailWord_3688600 prefixEnd_3688600 2598113500925066624467 := by
  unfold tailWord_3688600
  simp only [CollatzResearch.WordTrace]
  refine ⟨67267147218419818785607627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89689529624559758380810169 67267147218419818785607627)
  ·
    refine ⟨100900720827629728178411441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67267147218419818785607627 100900720827629728178411441)
    ·
      refine ⟨75675540620722296133808581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100900720827629728178411441 75675540620722296133808581)
      ·
        refine ⟨14189163866385430525089109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75675540620722296133808581 14189163866385430525089109)
        ·
          refine ⟨2598113500925066624467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 14189163866385430525089109 2598113500925066624467)
          ·
            rfl

theorem cell23_3688600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 14].length) (baseStart_3688600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3688600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3688600 prefixEnd_3688600 := by exact prefixLift 3688600
  have htrace : WordTrace (prefixWord ++ tailWord_3688600) baseStart_3688600 baseEnd_3688600 := by
    simpa [prefixWord, tailWord_3688600, baseEnd_3688600] using wordTrace_append hprefix tailTrace_3688600
  have hstable : (prefixWord ++ tailWord_3688600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3688600).length < 2 ^ (prefixWord ++ tailWord_3688600).sum := by decide
  have hdescent : baseEnd_3688600 < baseStart_3688600 := by decide
  rcases family_descends (prefixWord ++ tailWord_3688600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3688605 : List Nat := [1, 4, 2, 1, 1, 5, 2, 2, 1, 1, 3]
def baseStart_3688605 : Nat := 118140960795 + 3688605 * 2 ^ 59
def prefixEnd_3688605 : Nat := 4983230072969 + 3 ^ 40 * 3688605 * 2
def baseEnd_3688605 : Nat := 1894027309577646049673921

theorem tailTrace_3688605 : CollatzResearch.WordTrace tailWord_3688605 prefixEnd_3688605 1894027309577646049673921 := by
  unfold tailWord_3688605
  simp only [CollatzResearch.WordTrace]
  refine ⟨134534476801821523425147269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89689651201214348950098179 134534476801821523425147269)
  ·
    refine ⟨25225214400341535642215113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134534476801821523425147269 25225214400341535642215113)
    ·
      refine ⟨18918910800256151731661335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25225214400341535642215113 18918910800256151731661335)
      ·
        refine ⟨28378366200384227597492003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18918910800256151731661335 28378366200384227597492003)
        ·
          refine ⟨42567549300576341396238005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28378366200384227597492003 42567549300576341396238005)
          ·
            refine ⟨3990707746929032005897313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42567549300576341396238005 3990707746929032005897313)
            ·
              refine ⟨2993030810196774004422985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3990707746929032005897313 2993030810196774004422985)
              ·
                refine ⟨2244773107647580503317239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2993030810196774004422985 2244773107647580503317239)
                ·
                  refine ⟨3367159661471370754975859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2244773107647580503317239 3367159661471370754975859)
                  ·
                    refine ⟨5050739492207056132463789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3367159661471370754975859 5050739492207056132463789)
                    ·
                      refine ⟨1894027309577646049673921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5050739492207056132463789 1894027309577646049673921)
                      ·
                        rfl

theorem cell23_3688605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 2, 2, 1, 1, 3].length) (baseStart_3688605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3688605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3688605 prefixEnd_3688605 := by exact prefixLift 3688605
  have htrace : WordTrace (prefixWord ++ tailWord_3688605) baseStart_3688605 baseEnd_3688605 := by
    simpa [prefixWord, tailWord_3688605, baseEnd_3688605] using wordTrace_append hprefix tailTrace_3688605
  have hstable : (prefixWord ++ tailWord_3688605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3688605).length < 2 ^ (prefixWord ++ tailWord_3688605).sum := by decide
  have hdescent : baseEnd_3688605 < baseStart_3688605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3688605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3688621 : List Nat := [1, 5, 2, 1, 2, 1, 2, 3, 2, 4]
def baseStart_3688621 : Nat := 118140960795 + 3688621 * 2 ^ 59
def prefixEnd_3688621 : Nat := 4983230072969 + 3 ^ 40 * 3688621 * 2
def baseEnd_3688621 : Nat := 631345175089372662357949

theorem tailTrace_3688621 : CollatzResearch.WordTrace tailWord_3688621 prefixEnd_3688621 631345175089372662357949 := by
  unfold tailWord_3688621
  simp only [CollatzResearch.WordTrace]
  refine ⟨134535060369763558157729717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89690040246509038771819811 134535060369763558157729717)
  ·
    refine ⟨12612661909665333577287161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 134535060369763558157729717 12612661909665333577287161)
    ·
      refine ⟨9459496432249000182965371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12612661909665333577287161 9459496432249000182965371)
      ·
        refine ⟨14189244648373500274448057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9459496432249000182965371 14189244648373500274448057)
        ·
          refine ⟨10641933486280125205836043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14189244648373500274448057 10641933486280125205836043)
          ·
            refine ⟨15962900229420187808754065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10641933486280125205836043 15962900229420187808754065)
            ·
              refine ⟨11972175172065140856565549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15962900229420187808754065 11972175172065140856565549)
              ·
                refine ⟨4489565689524427821212081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11972175172065140856565549 4489565689524427821212081)
                ·
                  refine ⟨3367174267143320865909061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4489565689524427821212081 3367174267143320865909061)
                  ·
                    refine ⟨631345175089372662357949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3367174267143320865909061 631345175089372662357949)
                    ·
                      rfl

theorem cell23_3688621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_3688621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3688621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3688621 prefixEnd_3688621 := by exact prefixLift 3688621
  have htrace : WordTrace (prefixWord ++ tailWord_3688621) baseStart_3688621 baseEnd_3688621 := by
    simpa [prefixWord, tailWord_3688621, baseEnd_3688621] using wordTrace_append hprefix tailTrace_3688621
  have hstable : (prefixWord ++ tailWord_3688621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3688621).length < 2 ^ (prefixWord ++ tailWord_3688621).sum := by decide
  have hdescent : baseEnd_3688621 < baseStart_3688621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3688621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3688662 : List Nat := [5, 2, 1, 2, 1, 1, 2, 4, 1, 2, 2]
def baseStart_3688662 : Nat := 118140960795 + 3688662 * 2 ^ 59
def prefixEnd_3688662 : Nat := 4983230072969 + 3 ^ 40 * 3688662 * 2
def baseEnd_3688662 : Nat := 1894056577974952326661159

theorem tailTrace_3688662 : CollatzResearch.WordTrace tailWord_3688662 prefixEnd_3688662 1894056577974952326661159 := by
  unfold tailWord_3688662
  simp only [CollatzResearch.WordTrace]
  refine ⟨8408534735163438884998265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89691037175076681439981493 8408534735163438884998265)
  ·
    refine ⟨6306401051372579163748699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8408534735163438884998265 6306401051372579163748699)
    ·
      refine ⟨9459601577058868745623049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6306401051372579163748699 9459601577058868745623049)
      ·
        refine ⟨7094701182794151559217287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9459601577058868745623049 7094701182794151559217287)
        ·
          refine ⟨10642051774191227338825931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7094701182794151559217287 10642051774191227338825931)
          ·
            refine ⟨15963077661286841008238897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10642051774191227338825931 15963077661286841008238897)
            ·
              refine ⟨11972308245965130756179173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15963077661286841008238897 11972308245965130756179173)
              ·
                refine ⟨2244807796118462016783595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11972308245965130756179173 2244807796118462016783595)
                ·
                  refine ⟨3367211694177693025175393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2244807796118462016783595 3367211694177693025175393)
                  ·
                    refine ⟨2525408770633269768881545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3367211694177693025175393 2525408770633269768881545)
                    ·
                      refine ⟨1894056577974952326661159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2525408770633269768881545 1894056577974952326661159)
                      ·
                        rfl

theorem cell23_3688662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_3688662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3688662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3688662 prefixEnd_3688662 := by exact prefixLift 3688662
  have htrace : WordTrace (prefixWord ++ tailWord_3688662) baseStart_3688662 baseEnd_3688662 := by
    simpa [prefixWord, tailWord_3688662, baseEnd_3688662] using wordTrace_append hprefix tailTrace_3688662
  have hstable : (prefixWord ++ tailWord_3688662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3688662).length < 2 ^ (prefixWord ++ tailWord_3688662).sum := by decide
  have hdescent : baseEnd_3688662 < baseStart_3688662 := by decide
  rcases family_descends (prefixWord ++ tailWord_3688662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3688697 : List Nat := [1, 2, 1, 3, 1, 1, 2, 2, 4, 2, 4]
def baseStart_3688697 : Nat := 118140960795 + 3688697 * 2 ^ 59
def prefixEnd_3688697 : Nat := 4983230072969 + 3 ^ 40 * 3688697 * 2
def baseEnd_3688697 : Nat := 1894074549797859689723497

theorem tailTrace_3688697 : CollatzResearch.WordTrace tailWord_3688697 prefixEnd_3688697 1894074549797859689723497 := by
  unfold tailWord_3688697
  simp only [CollatzResearch.WordTrace]
  refine ⟨134537832317488223137496345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89691888211658815424997563 134537832317488223137496345)
  ·
    refine ⟨100903374238116167353122259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134537832317488223137496345 100903374238116167353122259)
    ·
      refine ⟨151355061357174251029683389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100903374238116167353122259 151355061357174251029683389)
      ·
        refine ⟨56758148008940344136131271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151355061357174251029683389 56758148008940344136131271)
        ·
          refine ⟨85137222013410516204196907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56758148008940344136131271 85137222013410516204196907)
          ·
            refine ⟨127705833020115774306295361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85137222013410516204196907 127705833020115774306295361)
            ·
              refine ⟨95779374765086830729721521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127705833020115774306295361 95779374765086830729721521)
              ·
                refine ⟨71834531073815123047291141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95779374765086830729721521 71834531073815123047291141)
                ·
                  refine ⟨13468974576340335571367089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71834531073815123047291141 13468974576340335571367089)
                  ·
                    refine ⟨10101730932255251678525317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13468974576340335571367089 10101730932255251678525317)
                    ·
                      refine ⟨1894074549797859689723497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10101730932255251678525317 1894074549797859689723497)
                      ·
                        rfl

theorem cell23_3688697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 4, 2, 4].length) (baseStart_3688697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3688697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3688697 prefixEnd_3688697 := by exact prefixLift 3688697
  have htrace : WordTrace (prefixWord ++ tailWord_3688697) baseStart_3688697 baseEnd_3688697 := by
    simpa [prefixWord, tailWord_3688697, baseEnd_3688697] using wordTrace_append hprefix tailTrace_3688697
  have hstable : (prefixWord ++ tailWord_3688697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3688697).length < 2 ^ (prefixWord ++ tailWord_3688697).sum := by decide
  have hdescent : baseEnd_3688697 < baseStart_3688697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3688697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3688718 : List Nat := [4, 1, 1, 2, 1, 2, 2, 4, 2, 2, 2]
def baseStart_3688718 : Nat := 118140960795 + 3688718 * 2 ^ 59
def prefixEnd_3688718 : Nat := 4983230072969 + 3 ^ 40 * 3688718 * 2
def baseEnd_3688718 : Nat := 1894085332891604107560901

theorem tailTrace_3688718 : CollatzResearch.WordTrace tailWord_3688718 prefixEnd_3688718 1894085332891604107560901 := by
  unfold tailWord_3688718
  simp only [CollatzResearch.WordTrace]
  refine ⟨16817324781301517965501351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89692398833608095816007205 16817324781301517965501351)
  ·
    refine ⟨25225987171952276948252027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16817324781301517965501351 25225987171952276948252027)
    ·
      refine ⟨37838980757928415422378041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25225987171952276948252027 37838980757928415422378041)
      ·
        refine ⟨28379235568446311566783531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37838980757928415422378041 28379235568446311566783531)
        ·
          refine ⟨42568853352669467350175297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28379235568446311566783531 42568853352669467350175297)
          ·
            refine ⟨31926640014502100512631473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42568853352669467350175297 31926640014502100512631473)
            ·
              refine ⟨23944980010876575384473605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31926640014502100512631473 23944980010876575384473605)
              ·
                refine ⟨4489683752039357884588801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23944980010876575384473605 4489683752039357884588801)
                ·
                  refine ⟨3367262814029518413441601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4489683752039357884588801 3367262814029518413441601)
                  ·
                    refine ⟨2525447110522138810081201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3367262814029518413441601 2525447110522138810081201)
                    ·
                      refine ⟨1894085332891604107560901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2525447110522138810081201 1894085332891604107560901)
                      ·
                        rfl

theorem cell23_3688718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 4, 2, 2, 2].length) (baseStart_3688718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3688718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3688718 prefixEnd_3688718 := by exact prefixLift 3688718
  have htrace : WordTrace (prefixWord ++ tailWord_3688718) baseStart_3688718 baseEnd_3688718 := by
    simpa [prefixWord, tailWord_3688718, baseEnd_3688718] using wordTrace_append hprefix tailTrace_3688718
  have hstable : (prefixWord ++ tailWord_3688718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3688718).length < 2 ^ (prefixWord ++ tailWord_3688718).sum := by decide
  have hdescent : baseEnd_3688718 < baseStart_3688718 := by decide
  rcases family_descends (prefixWord ++ tailWord_3688718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3688735 : List Nat := [1, 1, 2, 4, 3, 1, 4, 1, 2, 2, 2]
def baseStart_3688735 : Nat := 118140960795 + 3688735 * 2 ^ 59
def prefixEnd_3688735 : Nat := 4983230072969 + 3 ^ 40 * 3688735 * 2
def baseEnd_3688735 : Nat := 1894094062062730541048323

theorem tailTrace_3688735 : CollatzResearch.WordTrace tailWord_3688735 prefixEnd_3688735 1894094062062730541048323 := by
  unfold tailWord_3688735
  simp only [CollatzResearch.WordTrace]
  refine ⟨134539218291350555627379659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89692812194233703751586439 134539218291350555627379659)
  ·
    refine ⟨201808827437025833441069489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134539218291350555627379659 201808827437025833441069489)
    ·
      refine ⟨151356620577769375080802117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201808827437025833441069489 151356620577769375080802117)
      ·
        refine ⟨28379366358331757827650397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 151356620577769375080802117 28379366358331757827650397)
        ·
          refine ⟨10642262384374409185368899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28379366358331757827650397 10642262384374409185368899)
          ·
            refine ⟨15963393576561613778053349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10642262384374409185368899 15963393576561613778053349)
            ·
              refine ⟨2993136295605302583385003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15963393576561613778053349 2993136295605302583385003)
              ·
                refine ⟨4489704443407953875077505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2993136295605302583385003 4489704443407953875077505)
                ·
                  refine ⟨3367278332555965406308129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4489704443407953875077505 3367278332555965406308129)
                  ·
                    refine ⟨2525458749416974054731097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3367278332555965406308129 2525458749416974054731097)
                    ·
                      refine ⟨1894094062062730541048323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2525458749416974054731097 1894094062062730541048323)
                      ·
                        rfl

theorem cell23_3688735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 4, 1, 2, 2, 2].length) (baseStart_3688735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3688735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3688735 prefixEnd_3688735 := by exact prefixLift 3688735
  have htrace : WordTrace (prefixWord ++ tailWord_3688735) baseStart_3688735 baseEnd_3688735 := by
    simpa [prefixWord, tailWord_3688735, baseEnd_3688735] using wordTrace_append hprefix tailTrace_3688735
  have hstable : (prefixWord ++ tailWord_3688735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3688735).length < 2 ^ (prefixWord ++ tailWord_3688735).sum := by decide
  have hdescent : baseEnd_3688735 < baseStart_3688735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3688735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3688737 : List Nat := [1, 2, 3, 2, 1, 1, 2, 1, 3, 7]
def baseStart_3688737 : Nat := 118140960795 + 3688737 * 2 ^ 59
def prefixEnd_3688737 : Nat := 4983230072969 + 3 ^ 40 * 3688737 * 2
def baseEnd_3688737 : Nat := 631365029674679844407771

theorem tailTrace_3688737 : CollatzResearch.WordTrace tailWord_3688737 prefixEnd_3688737 631365029674679844407771 := by
  unfold tailWord_3688737
  simp only [CollatzResearch.WordTrace]
  refine ⟨134539291237343309968952465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89692860824895539979301643 134539291237343309968952465)
  ·
    refine ⟨100904468428007482476714349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134539291237343309968952465 100904468428007482476714349)
    ·
      refine ⟨37839175660502805928767881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100904468428007482476714349 37839175660502805928767881)
      ·
        refine ⟨28379381745377104446575911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37839175660502805928767881 28379381745377104446575911)
        ·
          refine ⟨42569072618065656669863867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28379381745377104446575911 42569072618065656669863867)
          ·
            refine ⟨63853608927098485004795801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42569072618065656669863867 63853608927098485004795801)
            ·
              refine ⟨47890206695323863753596851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63853608927098485004795801 47890206695323863753596851)
              ·
                refine ⟨71835310042985795630395277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47890206695323863753596851 71835310042985795630395277)
                ·
                  refine ⟨26938241266119673361398229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71835310042985795630395277 26938241266119673361398229)
                  ·
                    refine ⟨631365029674679844407771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26938241266119673361398229 631365029674679844407771)
                    ·
                      rfl

theorem cell23_3688737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 3, 7].length) (baseStart_3688737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3688737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3688737 prefixEnd_3688737 := by exact prefixLift 3688737
  have htrace : WordTrace (prefixWord ++ tailWord_3688737) baseStart_3688737 baseEnd_3688737 := by
    simpa [prefixWord, tailWord_3688737, baseEnd_3688737] using wordTrace_append hprefix tailTrace_3688737
  have hstable : (prefixWord ++ tailWord_3688737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3688737).length < 2 ^ (prefixWord ++ tailWord_3688737).sum := by decide
  have hdescent : baseEnd_3688737 < baseStart_3688737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3688737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3688777 : List Nat := [1, 2, 1, 1, 2, 3, 1, 1, 1, 5, 5]
def baseStart_3688777 : Nat := 118140960795 + 3688777 * 2 ^ 59
def prefixEnd_3688777 : Nat := 4983230072969 + 3 ^ 40 * 3688777 * 2
def baseEnd_3688777 : Nat := 1894115628250219376723129

theorem tailTrace_3688777 : CollatzResearch.WordTrace tailWord_3688777 prefixEnd_3688777 1894115628250219376723129 := by
  unfold tailWord_3688777
  simp only [CollatzResearch.WordTrace]
  refine ⟨134540750157198396800408585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89693833438132264533605723 134540750157198396800408585)
  ·
    refine ⟨100905562617898797600306439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134540750157198396800408585 100905562617898797600306439)
    ·
      refine ⟨151358343926848196400459659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100905562617898797600306439 151358343926848196400459659)
      ·
        refine ⟨227037515890272294600689489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151358343926848196400459659 227037515890272294600689489)
        ·
          refine ⟨170278136917704220950517117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227037515890272294600689489 170278136917704220950517117)
          ·
            refine ⟨63854301344139082856443919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170278136917704220950517117 63854301344139082856443919)
            ·
              refine ⟨95781452016208624284665879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63854301344139082856443919 95781452016208624284665879)
              ·
                refine ⟨143672178024312936426998819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95781452016208624284665879 143672178024312936426998819)
                ·
                  refine ⟨215508267036469404640498229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143672178024312936426998819 215508267036469404640498229)
                  ·
                    refine ⟨20203900034669006685046709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 215508267036469404640498229 20203900034669006685046709)
                    ·
                      refine ⟨1894115628250219376723129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20203900034669006685046709 1894115628250219376723129)
                      ·
                        rfl

theorem cell23_3688777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 5, 5].length) (baseStart_3688777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3688777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3688777 prefixEnd_3688777 := by exact prefixLift 3688777
  have htrace : WordTrace (prefixWord ++ tailWord_3688777) baseStart_3688777 baseEnd_3688777 := by
    simpa [prefixWord, tailWord_3688777, baseEnd_3688777] using wordTrace_append hprefix tailTrace_3688777
  have hstable : (prefixWord ++ tailWord_3688777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3688777).length < 2 ^ (prefixWord ++ tailWord_3688777).sum := by decide
  have hdescent : baseEnd_3688777 < baseStart_3688777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3688777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3688787 : List Nat := [1, 1, 1, 2, 1, 1, 4, 1, 4, 1, 6]
def baseStart_3688787 : Nat := 118140960795 + 3688787 * 2 ^ 59
def prefixEnd_3688787 : Nat := 4983230072969 + 3 ^ 40 * 3688787 * 2
def baseEnd_3688787 : Nat := 1894120763056764337598083

theorem tailTrace_3688787 : CollatzResearch.WordTrace tailWord_3688787 prefixEnd_3688787 1894120763056764337598083 := by
  unfold tailWord_3688787
  simp only [CollatzResearch.WordTrace]
  refine ⟨134541114887162168508272615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89694076591441445672181743 134541114887162168508272615)
  ·
    refine ⟨201811672330743252762408923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134541114887162168508272615 201811672330743252762408923)
    ·
      refine ⟨302717508496114879143613385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201811672330743252762408923 302717508496114879143613385)
      ·
        refine ⟨227038131372086159357710039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302717508496114879143613385 227038131372086159357710039)
        ·
          refine ⟨340557197058129239036565059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227038131372086159357710039 340557197058129239036565059)
          ·
            refine ⟨510835795587193858554847589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340557197058129239036565059 510835795587193858554847589)
            ·
              refine ⟨95781711672598848479033923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 510835795587193858554847589 95781711672598848479033923)
              ·
                refine ⟨143672567508898272718550885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95781711672598848479033923 143672567508898272718550885)
                ·
                  refine ⟨26938606407918426134728291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 143672567508898272718550885 26938606407918426134728291)
                  ·
                    refine ⟨40407909611877639202092437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26938606407918426134728291 40407909611877639202092437)
                    ·
                      refine ⟨1894120763056764337598083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40407909611877639202092437 1894120763056764337598083)
                      ·
                        rfl

theorem cell23_3688787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4, 1, 6].length) (baseStart_3688787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3688787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3688787 prefixEnd_3688787 := by exact prefixLift 3688787
  have htrace : WordTrace (prefixWord ++ tailWord_3688787) baseStart_3688787 baseEnd_3688787 := by
    simpa [prefixWord, tailWord_3688787, baseEnd_3688787] using wordTrace_append hprefix tailTrace_3688787
  have hstable : (prefixWord ++ tailWord_3688787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3688787).length < 2 ^ (prefixWord ++ tailWord_3688787).sum := by decide
  have hdescent : baseEnd_3688787 < baseStart_3688787 := by decide
  rcases family_descends (prefixWord ++ tailWord_3688787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3688791 : List Nat := [1, 1, 3, 2, 3, 1, 3, 1, 2, 4, 2]
def baseStart_3688791 : Nat := 118140960795 + 3688791 * 2 ^ 59
def prefixEnd_3688791 : Nat := 4983230072969 + 3 ^ 40 * 3688791 * 2
def baseEnd_3688791 : Nat := 1894122816979382321948065

theorem tailTrace_3688791 : CollatzResearch.WordTrace tailWord_3688791 prefixEnd_3688791 1894122816979382321948065 := by
  unfold tailWord_3688791
  simp only [CollatzResearch.WordTrace]
  refine ⟨134541260779147677191418227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89694173852765118127612151 134541260779147677191418227)
  ·
    refine ⟨201811891168721515787127341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134541260779147677191418227 201811891168721515787127341)
    ·
      refine ⟨75679459188270568420172753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201811891168721515787127341 75679459188270568420172753)
      ·
        refine ⟨56759594391202926315129565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75679459188270568420172753 56759594391202926315129565)
        ·
          refine ⟨21284847896701097368173587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56759594391202926315129565 21284847896701097368173587)
          ·
            refine ⟨31927271845051646052260381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21284847896701097368173587 31927271845051646052260381)
            ·
              refine ⟨11972726941894367269597643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31927271845051646052260381 11972726941894367269597643)
              ·
                refine ⟨17959090412841550904396465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11972726941894367269597643 17959090412841550904396465)
                ·
                  refine ⟨13469317809631163178297349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17959090412841550904396465 13469317809631163178297349)
                  ·
                    refine ⟨2525497089305843095930753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13469317809631163178297349 2525497089305843095930753)
                    ·
                      refine ⟨1894122816979382321948065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2525497089305843095930753 1894122816979382321948065)
                      ·
                        rfl

theorem cell23_3688791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 1, 2, 4, 2].length) (baseStart_3688791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3688791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3688791 prefixEnd_3688791 := by exact prefixLift 3688791
  have htrace : WordTrace (prefixWord ++ tailWord_3688791) baseStart_3688791 baseEnd_3688791 := by
    simpa [prefixWord, tailWord_3688791, baseEnd_3688791] using wordTrace_append hprefix tailTrace_3688791
  have hstable : (prefixWord ++ tailWord_3688791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3688791).length < 2 ^ (prefixWord ++ tailWord_3688791).sum := by decide
  have hdescent : baseEnd_3688791 < baseStart_3688791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3688791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3688794 : List Nat := [3, 1, 1, 2, 1, 2, 1, 4, 1, 4, 3]
def baseStart_3688794 : Nat := 118140960795 + 3688794 * 2 ^ 59
def prefixEnd_3688794 : Nat := 4983230072969 + 3 ^ 40 * 3688794 * 2
def baseEnd_3688794 : Nat := 1894124357421345810210551

theorem tailTrace_3688794 : CollatzResearch.WordTrace tailWord_3688794 prefixEnd_3688794 1894124357421345810210551 := by
  unfold tailWord_3688794
  simp only [CollatzResearch.WordTrace]
  refine ⟨33635342549534202175944359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89694246798757872469184957 33635342549534202175944359)
  ·
    refine ⟨50453013824301303263916539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33635342549534202175944359 50453013824301303263916539)
    ·
      refine ⟨75679520736451954895874809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50453013824301303263916539 75679520736451954895874809)
      ·
        refine ⟨56759640552338966171906107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75679520736451954895874809 56759640552338966171906107)
        ·
          refine ⟨85139460828508449257859161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56759640552338966171906107 85139460828508449257859161)
          ·
            refine ⟨63854595621381336943394371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85139460828508449257859161 63854595621381336943394371)
            ·
              refine ⟨95781893432072005415091557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63854595621381336943394371 95781893432072005415091557)
              ·
                refine ⟨17959105018513501015329667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95781893432072005415091557 17959105018513501015329667)
                ·
                  refine ⟨26938657527770251522994501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17959105018513501015329667 26938657527770251522994501)
                  ·
                    refine ⟨5050998286456922160561469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26938657527770251522994501 5050998286456922160561469)
                    ·
                      refine ⟨1894124357421345810210551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5050998286456922160561469 1894124357421345810210551)
                      ·
                        rfl

theorem cell23_3688794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4, 1, 4, 3].length) (baseStart_3688794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3688794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3688794 prefixEnd_3688794 := by exact prefixLift 3688794
  have htrace : WordTrace (prefixWord ++ tailWord_3688794) baseStart_3688794 baseEnd_3688794 := by
    simpa [prefixWord, tailWord_3688794, baseEnd_3688794] using wordTrace_append hprefix tailTrace_3688794
  have hstable : (prefixWord ++ tailWord_3688794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3688794).length < 2 ^ (prefixWord ++ tailWord_3688794).sum := by decide
  have hdescent : baseEnd_3688794 < baseStart_3688794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3688794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3688808 : List Nat := [2, 1, 4, 2, 2, 3, 1, 1, 2, 1, 4]
def baseStart_3688808 : Nat := 118140960795 + 3688808 * 2 ^ 59
def prefixEnd_3688808 : Nat := 4983230072969 + 3 ^ 40 * 3688808 * 2
def baseEnd_3688808 : Nat := 1894131546150508755435487

theorem tailTrace_3688808 : CollatzResearch.WordTrace tailWord_3688808 prefixEnd_3688808 1894131546150508755435487 := by
  unfold tailWord_3688808
  simp only [CollatzResearch.WordTrace]
  refine ⟨67270940410043044547393539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89694587213390726063191385 67270940410043044547393539)
  ·
    refine ⟨100906410615064566821090309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67270940410043044547393539 100906410615064566821090309)
    ·
      refine ⟨18919951990324606278954433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100906410615064566821090309 18919951990324606278954433)
      ·
        refine ⟨14189963992743454709215825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18919951990324606278954433 14189963992743454709215825)
        ·
          refine ⟨10642472994557591031911869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14189963992743454709215825 10642472994557591031911869)
          ·
            refine ⟨3990927372959096636966951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10642472994557591031911869 3990927372959096636966951)
            ·
              refine ⟨5986391059438644955450427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3990927372959096636966951 5986391059438644955450427)
              ·
                refine ⟨8979586589157967433175641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5986391059438644955450427 8979586589157967433175641)
                ·
                  refine ⟨6734689941868475574881731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8979586589157967433175641 6734689941868475574881731)
                  ·
                    refine ⟨10102034912802713362322597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6734689941868475574881731 10102034912802713362322597)
                    ·
                      refine ⟨1894131546150508755435487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10102034912802713362322597 1894131546150508755435487)
                      ·
                        rfl

theorem cell23_3688808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_3688808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3688808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3688808 prefixEnd_3688808 := by exact prefixLift 3688808
  have htrace : WordTrace (prefixWord ++ tailWord_3688808) baseStart_3688808 baseEnd_3688808 := by
    simpa [prefixWord, tailWord_3688808, baseEnd_3688808] using wordTrace_append hprefix tailTrace_3688808
  have hstable : (prefixWord ++ tailWord_3688808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3688808).length < 2 ^ (prefixWord ++ tailWord_3688808).sum := by decide
  have hdescent : baseEnd_3688808 < baseStart_3688808 := by decide
  rcases family_descends (prefixWord ++ tailWord_3688808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3688818 : List Nat := [3, 2, 1, 2, 1, 3, 1, 5, 1, 4]
def baseStart_3688818 : Nat := 118140960795 + 3688818 * 2 ^ 59
def prefixEnd_3688818 : Nat := 4983230072969 + 3 ^ 40 * 3688818 * 2
def baseEnd_3688818 : Nat := 631378893652351238770147

theorem tailTrace_3688818 : CollatzResearch.WordTrace tailWord_3688818 prefixEnd_3688818 631378893652351238770147 := by
  unfold tailWord_3688818
  simp only [CollatzResearch.WordTrace]
  refine ⟨33635561387512465200662777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89694830366699907201767405 33635561387512465200662777)
  ·
    refine ⟨25226671040634348900497083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33635561387512465200662777 25226671040634348900497083)
    ·
      refine ⟨37840006560951523350745625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25226671040634348900497083 37840006560951523350745625)
      ·
        refine ⟨28380004920713642513059219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37840006560951523350745625 28380004920713642513059219)
        ·
          refine ⟨42570007381070463769588829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28380004920713642513059219 42570007381070463769588829)
          ·
            refine ⟨15963752767901423913595811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42570007381070463769588829 15963752767901423913595811)
            ·
              refine ⟨23945629151852135870393717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15963752767901423913595811 23945629151852135870393717)
              ·
                refine ⟨2244902732986137737849411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23945629151852135870393717 2244902732986137737849411)
                ·
                  refine ⟨3367354099479206606774117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2244902732986137737849411 3367354099479206606774117)
                  ·
                    refine ⟨631378893652351238770147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3367354099479206606774117 631378893652351238770147)
                    ·
                      rfl

theorem cell23_3688818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 5, 1, 4].length) (baseStart_3688818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3688818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3688818 prefixEnd_3688818 := by exact prefixLift 3688818
  have htrace : WordTrace (prefixWord ++ tailWord_3688818) baseStart_3688818 baseEnd_3688818 := by
    simpa [prefixWord, tailWord_3688818, baseEnd_3688818] using wordTrace_append hprefix tailTrace_3688818
  have hstable : (prefixWord ++ tailWord_3688818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3688818).length < 2 ^ (prefixWord ++ tailWord_3688818).sum := by decide
  have hdescent : baseEnd_3688818 < baseStart_3688818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3688818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3688858 : List Nat := [3, 1, 1, 4, 1, 2, 2, 2, 3, 1, 3]
def baseStart_3688858 : Nat := 118140960795 + 3688858 * 2 ^ 59
def prefixEnd_3688858 : Nat := 4983230072969 + 3 ^ 40 * 3688858 * 2
def baseEnd_3688858 : Nat := 1894157220183233559810257

theorem tailTrace_3688858 : CollatzResearch.WordTrace tailWord_3688858 prefixEnd_3688858 1894157220183233559810257 := by
  unfold tailWord_3688858
  simp only [CollatzResearch.WordTrace]
  refine ⟨33635926117476236908526807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89695802979936631756071485 33635926117476236908526807)
  ·
    refine ⟨50453889176214355362790211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33635926117476236908526807 50453889176214355362790211)
    ·
      refine ⟨75680833764321533044185317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50453889176214355362790211 75680833764321533044185317)
      ·
        refine ⟨14190156330810287445784747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75680833764321533044185317 14190156330810287445784747)
        ·
          refine ⟨21285234496215431168677121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14190156330810287445784747 21285234496215431168677121)
          ·
            refine ⟨15963925872161573376507841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21285234496215431168677121 15963925872161573376507841)
            ·
              refine ⟨11972944404121180032380881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15963925872161573376507841 11972944404121180032380881)
              ·
                refine ⟨8979708303090885024285661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11972944404121180032380881 8979708303090885024285661)
                ·
                  refine ⟨3367390613659081884107123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8979708303090885024285661 3367390613659081884107123)
                  ·
                    refine ⟨5051085920488622826160685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3367390613659081884107123 5051085920488622826160685)
                    ·
                      refine ⟨1894157220183233559810257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5051085920488622826160685 1894157220183233559810257)
                      ·
                        rfl

theorem cell23_3688858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_3688858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3688858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3688858 prefixEnd_3688858 := by exact prefixLift 3688858
  have htrace : WordTrace (prefixWord ++ tailWord_3688858) baseStart_3688858 baseEnd_3688858 := by
    simpa [prefixWord, tailWord_3688858, baseEnd_3688858] using wordTrace_append hprefix tailTrace_3688858
  have hstable : (prefixWord ++ tailWord_3688858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3688858).length < 2 ^ (prefixWord ++ tailWord_3688858).sum := by decide
  have hdescent : baseEnd_3688858 < baseStart_3688858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3688858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3688885 : List Nat := [1, 3, 3, 2, 3, 1, 1, 2, 2, 3, 2]
def baseStart_3688885 : Nat := 118140960795 + 3688885 * 2 ^ 59
def prefixEnd_3688885 : Nat := 4983230072969 + 3 ^ 40 * 3688885 * 2
def baseEnd_3688885 : Nat := 1894171084160904954172633

theorem tailTrace_3688885 : CollatzResearch.WordTrace tailWord_3688885 prefixEnd_3688885 1894171084160904954172633 := by
  unfold tailWord_3688885
  simp only [CollatzResearch.WordTrace]
  refine ⟨134544689240807131245340109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89696459493871420830226739 134544689240807131245340109)
  ·
    refine ⟨50454258465302674217002541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134544689240807131245340109 50454258465302674217002541)
    ·
      refine ⟨18920346924488502831375953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50454258465302674217002541 18920346924488502831375953)
      ·
        refine ⟨14190260193366377123531965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18920346924488502831375953 14190260193366377123531965)
        ·
          refine ⟨5321347572512391421324487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14190260193366377123531965 5321347572512391421324487)
          ·
            refine ⟨7982021358768587131986731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5321347572512391421324487 7982021358768587131986731)
            ·
              refine ⟨11973032038152880697980097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7982021358768587131986731 11973032038152880697980097)
              ·
                refine ⟨8979774028614660523485073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11973032038152880697980097 8979774028614660523485073)
                ·
                  refine ⟨6734830521460995392613805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8979774028614660523485073 6734830521460995392613805)
                  ·
                    refine ⟨2525561445547873272230177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6734830521460995392613805 2525561445547873272230177)
                    ·
                      refine ⟨1894171084160904954172633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2525561445547873272230177 1894171084160904954172633)
                      ·
                        rfl

theorem cell23_3688885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 2, 2, 3, 2].length) (baseStart_3688885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3688885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3688885 prefixEnd_3688885 := by exact prefixLift 3688885
  have htrace : WordTrace (prefixWord ++ tailWord_3688885) baseStart_3688885 baseEnd_3688885 := by
    simpa [prefixWord, tailWord_3688885, baseEnd_3688885] using wordTrace_append hprefix tailTrace_3688885
  have hstable : (prefixWord ++ tailWord_3688885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3688885).length < 2 ^ (prefixWord ++ tailWord_3688885).sum := by decide
  have hdescent : baseEnd_3688885 < baseStart_3688885 := by decide
  rcases family_descends (prefixWord ++ tailWord_3688885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3688904 : List Nat := [2, 1, 3, 1, 3, 2, 1, 10]
def baseStart_3688904 : Nat := 118140960795 + 3688904 * 2 ^ 59
def prefixEnd_3688904 : Nat := 4983230072969 + 3 ^ 40 * 3688904 * 2
def baseEnd_3688904 : Nat := 70154845936790384438335

theorem tailTrace_3688904 : CollatzResearch.WordTrace tailWord_3688904 prefixEnd_3688904 70154845936790384438335 := by
  unfold tailWord_3688904
  simp only [CollatzResearch.WordTrace]
  refine ⟨67272691113869148745140883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89696921485158864993521177 67272691113869148745140883)
  ·
    refine ⟨100909036670803723117711325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67272691113869148745140883 100909036670803723117711325)
    ·
      refine ⟨37840888751551396169141747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100909036670803723117711325 37840888751551396169141747)
      ·
        refine ⟨56761333127327094253712621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37840888751551396169141747 56761333127327094253712621)
        ·
          refine ⟨21285499922747660345142233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56761333127327094253712621 21285499922747660345142233)
          ·
            refine ⟨15964124942060745258856675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21285499922747660345142233 15964124942060745258856675)
            ·
              refine ⟨23946187413091117888285013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15964124942060745258856675 23946187413091117888285013)
              ·
                refine ⟨70154845936790384438335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 23946187413091117888285013 70154845936790384438335)
                ·
                  rfl

theorem cell23_3688904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 10].length) (baseStart_3688904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3688904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3688904 prefixEnd_3688904 := by exact prefixLift 3688904
  have htrace : WordTrace (prefixWord ++ tailWord_3688904) baseStart_3688904 baseEnd_3688904 := by
    simpa [prefixWord, tailWord_3688904, baseEnd_3688904] using wordTrace_append hprefix tailTrace_3688904
  have hstable : (prefixWord ++ tailWord_3688904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3688904).length < 2 ^ (prefixWord ++ tailWord_3688904).sum := by decide
  have hdescent : baseEnd_3688904 < baseStart_3688904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3688904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3688935 : List Nat := [1, 1, 5, 2, 1, 1, 5, 1, 1, 2, 3]
def baseStart_3688935 : Nat := 118140960795 + 3688935 * 2 ^ 59
def prefixEnd_3688935 : Nat := 4983230072969 + 3 ^ 40 * 3688935 * 2
def baseEnd_3688935 : Nat := 1894196758193629758547403

theorem tailTrace_3688935 : CollatzResearch.WordTrace tailWord_3688935 prefixEnd_3688935 1894196758193629758547403 := by
  unfold tailWord_3688935
  simp only [CollatzResearch.WordTrace]
  refine ⟨134546512890625989784660259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89697675260417326523106839 134546512890625989784660259)
  ·
    refine ⟨201819769335938984676990389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134546512890625989784660259 201819769335938984676990389)
    ·
      refine ⟨18920603375244279813467849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 201819769335938984676990389 18920603375244279813467849)
      ·
        refine ⟨14190452531433209860100887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18920603375244279813467849 14190452531433209860100887)
        ·
          refine ⟨21285678797149814790151331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14190452531433209860100887 21285678797149814790151331)
          ·
            refine ⟨31928518195724722185226997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21285678797149814790151331 31928518195724722185226997)
            ·
              refine ⟨2993298580849192704865031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31928518195724722185226997 2993298580849192704865031)
              ·
                refine ⟨4489947871273789057297547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2993298580849192704865031 4489947871273789057297547)
                ·
                  refine ⟨6734921806910683585946321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4489947871273789057297547 6734921806910683585946321)
                  ·
                    refine ⟨5051191355183012689459741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6734921806910683585946321 5051191355183012689459741)
                    ·
                      refine ⟨1894196758193629758547403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5051191355183012689459741 1894196758193629758547403)
                      ·
                        rfl

theorem cell23_3688935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 5, 1, 1, 2, 3].length) (baseStart_3688935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3688935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3688935 prefixEnd_3688935 := by exact prefixLift 3688935
  have htrace : WordTrace (prefixWord ++ tailWord_3688935) baseStart_3688935 baseEnd_3688935 := by
    simpa [prefixWord, tailWord_3688935, baseEnd_3688935] using wordTrace_append hprefix tailTrace_3688935
  have hstable : (prefixWord ++ tailWord_3688935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3688935).length < 2 ^ (prefixWord ++ tailWord_3688935).sum := by decide
  have hdescent : baseEnd_3688935 < baseStart_3688935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3688935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3688966 : List Nat := [6, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2]
def baseStart_3688966 : Nat := 118140960795 + 3688966 * 2 ^ 59
def prefixEnd_3688966 : Nat := 4983230072969 + 3 ^ 40 * 3688966 * 2
def baseEnd_3688966 : Nat := 1894212676093919137259761

theorem tailTrace_3688966 : CollatzResearch.WordTrace tailWord_3688966 prefixEnd_3688966 1894212676093919137259761 := by
  unfold tailWord_3688966
  simp only [CollatzResearch.WordTrace]
  refine ⟨4204613861047302564969961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 89698429035675788052692501 4204613861047302564969961)
  ·
    refine ⟨3153460395785476923727471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4204613861047302564969961 3153460395785476923727471)
    ·
      refine ⟨4730190593678215385591207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3153460395785476923727471 4730190593678215385591207)
      ·
        refine ⟨7095285890517323078386811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4730190593678215385591207 7095285890517323078386811)
        ·
          refine ⟨10642928835775984617580217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7095285890517323078386811 10642928835775984617580217)
          ·
            refine ⟨7982196626831988463185163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10642928835775984617580217 7982196626831988463185163)
            ·
              refine ⟨11973294940247982694777745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7982196626831988463185163 11973294940247982694777745)
              ·
                refine ⟨8979971205185987021083309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11973294940247982694777745 8979971205185987021083309)
                ·
                  refine ⟨3367489201944745132906241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8979971205185987021083309 3367489201944745132906241)
                  ·
                    refine ⟨2525616901458558849679681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3367489201944745132906241 2525616901458558849679681)
                    ·
                      refine ⟨1894212676093919137259761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2525616901458558849679681 1894212676093919137259761)
                      ·
                        rfl

theorem cell23_3688966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_3688966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3688966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3688966 prefixEnd_3688966 := by exact prefixLift 3688966
  have htrace : WordTrace (prefixWord ++ tailWord_3688966) baseStart_3688966 baseEnd_3688966 := by
    simpa [prefixWord, tailWord_3688966, baseEnd_3688966] using wordTrace_append hprefix tailTrace_3688966
  have hstable : (prefixWord ++ tailWord_3688966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3688966).length < 2 ^ (prefixWord ++ tailWord_3688966).sum := by decide
  have hdescent : baseEnd_3688966 < baseStart_3688966 := by decide
  rcases family_descends (prefixWord ++ tailWord_3688966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3688992 : List Nat := [2, 1, 1, 6, 2, 1, 1, 3, 1, 3, 2]
def baseStart_3688992 : Nat := 118140960795 + 3688992 * 2 ^ 59
def prefixEnd_3688992 : Nat := 4983230072969 + 3 ^ 40 * 3688992 * 2
def baseEnd_3688992 : Nat := 1894226026590936035534641

theorem tailTrace_3688992 : CollatzResearch.WordTrace tailWord_3688992 prefixEnd_3688992 1894226026590936035534641 := by
  unfold tailWord_3688992
  simp only [CollatzResearch.WordTrace]
  refine ⟨67274295925709744259742615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89699061234279659012990153 67274295925709744259742615)
  ·
    refine ⟨100911443888564616389613923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67274295925709744259742615 100911443888564616389613923)
    ·
      refine ⟨151367165832846924584420885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100911443888564616389613923 151367165832846924584420885)
      ·
        refine ⟨7095335898414699589894729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 151367165832846924584420885 7095335898414699589894729)
        ·
          refine ⟨5321501923811024692421047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7095335898414699589894729 5321501923811024692421047)
          ·
            refine ⟨7982252885716537038631571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5321501923811024692421047 7982252885716537038631571)
            ·
              refine ⟨11973379328574805557947357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7982252885716537038631571 11973379328574805557947357)
              ·
                refine ⟨4490017248215552084230259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11973379328574805557947357 4490017248215552084230259)
                ·
                  refine ⟨6735025872323328126345389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4490017248215552084230259 6735025872323328126345389)
                  ·
                    refine ⟨2525634702121248047379521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6735025872323328126345389 2525634702121248047379521)
                    ·
                      refine ⟨1894226026590936035534641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2525634702121248047379521 1894226026590936035534641)
                      ·
                        rfl

theorem cell23_3688992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_3688992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3688992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3688992 prefixEnd_3688992 := by exact prefixLift 3688992
  have htrace : WordTrace (prefixWord ++ tailWord_3688992) baseStart_3688992 baseEnd_3688992 := by
    simpa [prefixWord, tailWord_3688992, baseEnd_3688992] using wordTrace_append hprefix tailTrace_3688992
  have hstable : (prefixWord ++ tailWord_3688992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3688992).length < 2 ^ (prefixWord ++ tailWord_3688992).sum := by decide
  have hdescent : baseEnd_3688992 < baseStart_3688992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3688992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689011 : List Nat := [1, 1, 1, 2, 4, 2, 4, 1, 7]
def baseStart_3689011 : Nat := 118140960795 + 3689011 * 2 ^ 59
def prefixEnd_3689011 : Nat := 4983230072969 + 3 ^ 40 * 3689011 * 2
def baseEnd_3689011 : Nat := 210470642524819051244117

theorem tailTrace_3689011 : CollatzResearch.WordTrace tailWord_3689011 prefixEnd_3689011 210470642524819051244117 := by
  unfold tailWord_3689011
  simp only [CollatzResearch.WordTrace]
  refine ⟨134549284838350654764426887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89699523225567103176284591 134549284838350654764426887)
  ·
    refine ⟨201823927257525982146640331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134549284838350654764426887 201823927257525982146640331)
    ·
      refine ⟨302735890886288973219960497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201823927257525982146640331 302735890886288973219960497)
      ·
        refine ⟨227051918164716729914970373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302735890886288973219960497 227051918164716729914970373)
        ·
          refine ⟨42572234655884386859056945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 227051918164716729914970373 42572234655884386859056945)
          ·
            refine ⟨31929175991913290144292709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42572234655884386859056945 31929175991913290144292709)
            ·
              refine ⟨5986720498483741902054883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31929175991913290144292709 5986720498483741902054883)
              ·
                refine ⟨8980080747725612853082325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5986720498483741902054883 8980080747725612853082325)
                ·
                  refine ⟨210470642524819051244117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8980080747725612853082325 210470642524819051244117)
                  ·
                    rfl

theorem cell23_3689011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 1, 7].length) (baseStart_3689011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3689011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3689011 prefixEnd_3689011 := by exact prefixLift 3689011
  have htrace : WordTrace (prefixWord ++ tailWord_3689011) baseStart_3689011 baseEnd_3689011 := by
    simpa [prefixWord, tailWord_3689011, baseEnd_3689011] using wordTrace_append hprefix tailTrace_3689011
  have hstable : (prefixWord ++ tailWord_3689011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689011).length < 2 ^ (prefixWord ++ tailWord_3689011).sum := by decide
  have hdescent : baseEnd_3689011 < baseStart_3689011 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689041 : List Nat := [1, 2, 2, 1, 3, 3, 2, 1, 1, 7]
def baseStart_3689041 : Nat := 118140960795 + 3689041 * 2 ^ 59
def prefixEnd_3689041 : Nat := 4983230072969 + 3 ^ 40 * 3689041 * 2
def baseEnd_3689041 : Nat := 631417062381002114607305

theorem tailTrace_3689041 : CollatzResearch.WordTrace tailWord_3689041 prefixEnd_3689041 631417062381002114607305 := by
  unfold tailWord_3689041
  simp only [CollatzResearch.WordTrace]
  refine ⟨134550379028241969888018977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89700252685494646592012651 134550379028241969888018977)
  ·
    refine ⟨100912784271181477416014233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134550379028241969888018977 100912784271181477416014233)
    ·
      refine ⟨75684588203386108062010675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100912784271181477416014233 75684588203386108062010675)
      ·
        refine ⟨113526882305079162093016013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75684588203386108062010675 113526882305079162093016013)
        ·
          refine ⟨42572580864404685784881005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113526882305079162093016013 42572580864404685784881005)
          ·
            refine ⟨15964717824151757169330377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42572580864404685784881005 15964717824151757169330377)
            ·
              refine ⟨11973538368113817876997783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15964717824151757169330377 11973538368113817876997783)
              ·
                refine ⟨17960307552170726815496675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11973538368113817876997783 17960307552170726815496675)
                ·
                  refine ⟨26940461328256090223245013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17960307552170726815496675 26940461328256090223245013)
                  ·
                    refine ⟨631417062381002114607305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26940461328256090223245013 631417062381002114607305)
                    ·
                      rfl

theorem cell23_3689041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 1, 1, 7].length) (baseStart_3689041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3689041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3689041 prefixEnd_3689041 := by exact prefixLift 3689041
  have htrace : WordTrace (prefixWord ++ tailWord_3689041) baseStart_3689041 baseEnd_3689041 := by
    simpa [prefixWord, tailWord_3689041, baseEnd_3689041] using wordTrace_append hprefix tailTrace_3689041
  have hstable : (prefixWord ++ tailWord_3689041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689041).length < 2 ^ (prefixWord ++ tailWord_3689041).sum := by decide
  have hdescent : baseEnd_3689041 < baseStart_3689041 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689091 : List Nat := [1, 1, 1, 3, 3, 1, 2, 1, 2, 4, 4]
def baseStart_3689091 : Nat := 118140960795 + 3689091 * 2 ^ 59
def prefixEnd_3689091 : Nat := 4983230072969 + 3 ^ 40 * 3689091 * 2
def baseEnd_3689091 : Nat := 1894276861175731148196685

theorem tailTrace_3689091 : CollatzResearch.WordTrace tailWord_3689091 prefixEnd_3689091 1894276861175731148196685 := by
  unfold tailWord_3689091
  simp only [CollatzResearch.WordTrace]
  refine ⟨134552202678060828427339127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89701468452040552284892751 134552202678060828427339127)
  ·
    refine ⟨201828304017091242641008691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134552202678060828427339127 201828304017091242641008691)
    ·
      refine ⟨302742456025636863961513037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201828304017091242641008691 302742456025636863961513037)
      ·
        refine ⟨113528421009613823985567389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 302742456025636863961513037 113528421009613823985567389)
        ·
          refine ⟨42573157878605183994587771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113528421009613823985567389 42573157878605183994587771)
          ·
            refine ⟨63859736817907775991881657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42573157878605183994587771 63859736817907775991881657)
            ·
              refine ⟨47894802613430831993911243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63859736817907775991881657 47894802613430831993911243)
              ·
                refine ⟨71842203920146247990866865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47894802613430831993911243 71842203920146247990866865)
                ·
                  refine ⟨53881652940109685993150149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71842203920146247990866865 53881652940109685993150149)
                  ·
                    refine ⟨10102809926270566123715653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53881652940109685993150149 10102809926270566123715653)
                    ·
                      refine ⟨1894276861175731148196685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10102809926270566123715653 1894276861175731148196685)
                      ·
                        rfl

theorem cell23_3689091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 4, 4].length) (baseStart_3689091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3689091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3689091 prefixEnd_3689091 := by exact prefixLift 3689091
  have htrace : WordTrace (prefixWord ++ tailWord_3689091) baseStart_3689091 baseEnd_3689091 := by
    simpa [prefixWord, tailWord_3689091, baseEnd_3689091] using wordTrace_append hprefix tailTrace_3689091
  have hstable : (prefixWord ++ tailWord_3689091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689091).length < 2 ^ (prefixWord ++ tailWord_3689091).sum := by decide
  have hdescent : baseEnd_3689091 < baseStart_3689091 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689148 : List Nat := [2, 2, 2, 3, 1, 1, 1, 3, 3, 5]
def baseStart_3689148 : Nat := 118140960795 + 3689148 * 2 ^ 59
def prefixEnd_3689148 : Nat := 4983230072969 + 3 ^ 40 * 3689148 * 2
def baseEnd_3689148 : Nat := 631435376524345808394641

theorem tailTrace_3689148 : CollatzResearch.WordTrace tailWord_3689148 prefixEnd_3689148 631435376524345808394641 := by
  unfold tailWord_3689148
  simp only [CollatzResearch.WordTrace]
  refine ⟨67277140819427163581082049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89702854425902884774776065 67277140819427163581082049)
  ·
    refine ⟨50457855614570372685811537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67277140819427163581082049 50457855614570372685811537)
    ·
      refine ⟨37843391710927779514358653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50457855614570372685811537 37843391710927779514358653)
      ·
        refine ⟨14191271891597917317884495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37843391710927779514358653 14191271891597917317884495)
        ·
          refine ⟨21286907837396875976826743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14191271891597917317884495 21286907837396875976826743)
          ·
            refine ⟨31930361756095313965240115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21286907837396875976826743 31930361756095313965240115)
            ·
              refine ⟨47895542634142970947860173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31930361756095313965240115 47895542634142970947860173)
              ·
                refine ⟨17960828487803614105447565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47895542634142970947860173 17960828487803614105447565)
                ·
                  refine ⟨6735310682926355289542837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17960828487803614105447565 6735310682926355289542837)
                  ·
                    refine ⟨631435376524345808394641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6735310682926355289542837 631435376524345808394641)
                    ·
                      rfl

theorem cell23_3689148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 3, 3, 5].length) (baseStart_3689148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3689148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3689148 prefixEnd_3689148 := by exact prefixLift 3689148
  have htrace : WordTrace (prefixWord ++ tailWord_3689148) baseStart_3689148 baseEnd_3689148 := by
    simpa [prefixWord, tailWord_3689148, baseEnd_3689148] using wordTrace_append hprefix tailTrace_3689148
  have hstable : (prefixWord ++ tailWord_3689148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689148).length < 2 ^ (prefixWord ++ tailWord_3689148).sum := by decide
  have hdescent : baseEnd_3689148 < baseStart_3689148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689171 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 1, 7, 5]
def baseStart_3689171 : Nat := 118140960795 + 3689171 * 2 ^ 59
def prefixEnd_3689171 : Nat := 4983230072969 + 3 ^ 40 * 3689171 * 2
def baseEnd_3689171 : Nat := 1894317939628090835196317

theorem tailTrace_3689171 : CollatzResearch.WordTrace tailWord_3689171 prefixEnd_3689171 1894317939628090835196317 := by
  unfold tailWord_3689171
  simp only [CollatzResearch.WordTrace]
  refine ⟨134555120517771002090251367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89703413678514001393500911 134555120517771002090251367)
  ·
    refine ⟨201832680776656503135377051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134555120517771002090251367 201832680776656503135377051)
    ·
      refine ⟨302749021164984754703065577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201832680776656503135377051 302749021164984754703065577)
      ·
        refine ⟨227061765873738566027299183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302749021164984754703065577 227061765873738566027299183)
        ·
          refine ⟨340592648810607849040948775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227061765873738566027299183 340592648810607849040948775)
          ·
            refine ⟨510888973215911773561423163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340592648810607849040948775 510888973215911773561423163)
            ·
              refine ⟨766333459823867660342134745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 510888973215911773561423163 766333459823867660342134745)
              ·
                refine ⟨574750094867900745256601059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 766333459823867660342134745 574750094867900745256601059)
                ·
                  refine ⟨862125142301851117884901589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 574750094867900745256601059 862125142301851117884901589)
                  ·
                    refine ⟨20206058022699635575427381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 862125142301851117884901589 20206058022699635575427381)
                    ·
                      refine ⟨1894317939628090835196317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20206058022699635575427381 1894317939628090835196317)
                      ·
                        rfl

theorem cell23_3689171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 7, 5].length) (baseStart_3689171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3689171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3689171 prefixEnd_3689171 := by exact prefixLift 3689171
  have htrace : WordTrace (prefixWord ++ tailWord_3689171) baseStart_3689171 baseEnd_3689171 := by
    simpa [prefixWord, tailWord_3689171, baseEnd_3689171] using wordTrace_append hprefix tailTrace_3689171
  have hstable : (prefixWord ++ tailWord_3689171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689171).length < 2 ^ (prefixWord ++ tailWord_3689171).sum := by decide
  have hdescent : baseEnd_3689171 < baseStart_3689171 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689188 : List Nat := [2, 3, 1, 1, 1, 4, 1, 1, 3, 1, 5]
def baseStart_3689188 : Nat := 118140960795 + 3689188 * 2 ^ 59
def prefixEnd_3689188 : Nat := 4983230072969 + 3 ^ 40 * 3689188 * 2
def baseEnd_3689188 : Nat := 1894326668799217268683739

theorem tailTrace_3689188 : CollatzResearch.WordTrace tailWord_3689188 prefixEnd_3689188 1894326668799217268683739 := by
  unfold tailWord_3689188
  simp only [CollatzResearch.WordTrace]
  refine ⟨67277870279354706996810109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89703827039139609329080145 67277870279354706996810109)
  ·
    refine ⟨25229201354758015123803791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67277870279354706996810109 25229201354758015123803791)
    ·
      refine ⟨37843802032137022685705687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25229201354758015123803791 37843802032137022685705687)
      ·
        refine ⟨56765703048205534028558531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37843802032137022685705687 56765703048205534028558531)
        ·
          refine ⟨85148554572308301042837797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56765703048205534028558531 85148554572308301042837797)
          ·
            refine ⟨15965353982307806445532087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85148554572308301042837797 15965353982307806445532087)
            ·
              refine ⟨23948030973461709668298131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15965353982307806445532087 23948030973461709668298131)
              ·
                refine ⟨35922046460192564502447197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23948030973461709668298131 35922046460192564502447197)
                ·
                  refine ⟨13470767422572211688417699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35922046460192564502447197 13470767422572211688417699)
                  ·
                    refine ⟨20206151133858317532626549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13470767422572211688417699 20206151133858317532626549)
                    ·
                      refine ⟨1894326668799217268683739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20206151133858317532626549 1894326668799217268683739)
                      ·
                        rfl

theorem cell23_3689188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 3, 1, 5].length) (baseStart_3689188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3689188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3689188 prefixEnd_3689188 := by exact prefixLift 3689188
  have htrace : WordTrace (prefixWord ++ tailWord_3689188) baseStart_3689188 baseEnd_3689188 := by
    simpa [prefixWord, tailWord_3689188, baseEnd_3689188] using wordTrace_append hprefix tailTrace_3689188
  have hstable : (prefixWord ++ tailWord_3689188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689188).length < 2 ^ (prefixWord ++ tailWord_3689188).sum := by decide
  have hdescent : baseEnd_3689188 < baseStart_3689188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689202 : List Nat := [3, 2, 1, 3, 1, 3, 2, 2, 1, 1, 4]
def baseStart_3689202 : Nat := 118140960795 + 3689202 * 2 ^ 59
def prefixEnd_3689202 : Nat := 4983230072969 + 3 ^ 40 * 3689202 * 2
def baseEnd_3689202 : Nat := 1894333857528380213908675

theorem tailTrace_3689202 : CollatzResearch.WordTrace tailWord_3689202 prefixEnd_3689202 1894333857528380213908675 := by
  unfold tailWord_3689202
  simp only [CollatzResearch.WordTrace]
  refine ⟨33639062795164673596157465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89704167453772462923086573 33639062795164673596157465)
  ·
    refine ⟨25229297096373505197118099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33639062795164673596157465 25229297096373505197118099)
    ·
      refine ⟨37843945644560257795677149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25229297096373505197118099 37843945644560257795677149)
      ·
        refine ⟨14191479616710096673378931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37843945644560257795677149 14191479616710096673378931)
        ·
          refine ⟨21287219425065145010068397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14191479616710096673378931 21287219425065145010068397)
          ·
            refine ⟨7982707284399429378775649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21287219425065145010068397 7982707284399429378775649)
            ·
              refine ⟨5987030463299572034081737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7982707284399429378775649 5987030463299572034081737)
              ·
                refine ⟨4490272847474679025561303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5987030463299572034081737 4490272847474679025561303)
                ·
                  refine ⟨6735409271212018538341955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4490272847474679025561303 6735409271212018538341955)
                  ·
                    refine ⟨10103113906818027807512933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6735409271212018538341955 10103113906818027807512933)
                    ·
                      refine ⟨1894333857528380213908675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10103113906818027807512933 1894333857528380213908675)
                      ·
                        rfl

theorem cell23_3689202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_3689202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3689202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3689202 prefixEnd_3689202 := by exact prefixLift 3689202
  have htrace : WordTrace (prefixWord ++ tailWord_3689202) baseStart_3689202 baseEnd_3689202 := by
    simpa [prefixWord, tailWord_3689202, baseEnd_3689202] using wordTrace_append hprefix tailTrace_3689202
  have hstable : (prefixWord ++ tailWord_3689202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689202).length < 2 ^ (prefixWord ++ tailWord_3689202).sum := by decide
  have hdescent : baseEnd_3689202 < baseStart_3689202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689235 : List Nat := [1, 1, 1, 2, 1, 3, 3, 3, 4, 1, 3]
def baseStart_3689235 : Nat := 118140960795 + 3689235 * 2 ^ 59
def prefixEnd_3689235 : Nat := 4983230072969 + 3 ^ 40 * 3689235 * 2
def baseEnd_3689235 : Nat := 1894350802389978584796023

theorem tailTrace_3689235 : CollatzResearch.WordTrace tailWord_3689235 prefixEnd_3689235 1894350802389978584796023 := by
  unfold tailWord_3689235
  simp only [CollatzResearch.WordTrace]
  refine ⟨134557454789539141020581159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89704969859692760680387439 134557454789539141020581159)
  ·
    refine ⟨201836182184308711530871739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134557454789539141020581159 201836182184308711530871739)
    ·
      refine ⟨302754273276463067296307609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201836182184308711530871739 302754273276463067296307609)
      ·
        refine ⟨227065704957347300472230707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302754273276463067296307609 227065704957347300472230707)
        ·
          refine ⟨340598557436020950708346061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227065704957347300472230707 340598557436020950708346061)
          ·
            refine ⟨127724459038507856515629773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 340598557436020950708346061 127724459038507856515629773)
            ·
              refine ⟨47896672139440446193361165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127724459038507856515629773 47896672139440446193361165)
              ·
                refine ⟨17961252052290167322510437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47896672139440446193361165 17961252052290167322510437)
                ·
                  refine ⟨3367734759804406372970707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17961252052290167322510437 3367734759804406372970707)
                  ·
                    refine ⟨5051602139706609559456061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3367734759804406372970707 5051602139706609559456061)
                    ·
                      refine ⟨1894350802389978584796023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5051602139706609559456061 1894350802389978584796023)
                      ·
                        rfl

theorem cell23_3689235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3, 4, 1, 3].length) (baseStart_3689235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3689235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3689235 prefixEnd_3689235 := by exact prefixLift 3689235
  have htrace : WordTrace (prefixWord ++ tailWord_3689235) baseStart_3689235 baseEnd_3689235 := by
    simpa [prefixWord, tailWord_3689235, baseEnd_3689235] using wordTrace_append hprefix tailTrace_3689235
  have hstable : (prefixWord ++ tailWord_3689235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689235).length < 2 ^ (prefixWord ++ tailWord_3689235).sum := by decide
  have hdescent : baseEnd_3689235 < baseStart_3689235 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689305 : List Nat := [1, 2, 1, 2, 2, 5, 1, 1, 2, 2, 4]
def baseStart_3689305 : Nat := 118140960795 + 3689305 * 2 ^ 59
def prefixEnd_3689305 : Nat := 4983230072969 + 3 ^ 40 * 3689305 * 2
def baseEnd_3689305 : Nat := 1894386746035793310920701

theorem tailTrace_3689305 : CollatzResearch.WordTrace tailWord_3689305 prefixEnd_3689305 1894386746035793310920701 := by
  unfold tailWord_3689305
  simp only [CollatzResearch.WordTrace]
  refine ⟨134560007899285542975629369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89706671932857028650419579 134560007899285542975629369)
  ·
    refine ⟨100920005924464157231722027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134560007899285542975629369 100920005924464157231722027)
    ·
      refine ⟨151380008886696235847583041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100920005924464157231722027 151380008886696235847583041)
      ·
        refine ⟨113535006665022176885687281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151380008886696235847583041 113535006665022176885687281)
        ·
          refine ⟨85151254998766632664265461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113535006665022176885687281 85151254998766632664265461)
          ·
            refine ⟨7982930156134371812274887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 85151254998766632664265461 7982930156134371812274887)
            ·
              refine ⟨11974395234201557718412331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7982930156134371812274887 11974395234201557718412331)
              ·
                refine ⟨17961592851302336577618497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11974395234201557718412331 17961592851302336577618497)
                ·
                  refine ⟨13471194638476752433213873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17961592851302336577618497 13471194638476752433213873)
                  ·
                    refine ⟨10103395978857564324910405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13471194638476752433213873 10103395978857564324910405)
                    ·
                      refine ⟨1894386746035793310920701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10103395978857564324910405 1894386746035793310920701)
                      ·
                        rfl

theorem cell23_3689305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 1, 2, 2, 4].length) (baseStart_3689305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3689305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3689305 prefixEnd_3689305 := by exact prefixLift 3689305
  have htrace : WordTrace (prefixWord ++ tailWord_3689305) baseStart_3689305 baseEnd_3689305 := by
    simpa [prefixWord, tailWord_3689305, baseEnd_3689305] using wordTrace_append hprefix tailTrace_3689305
  have hstable : (prefixWord ++ tailWord_3689305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689305).length < 2 ^ (prefixWord ++ tailWord_3689305).sum := by decide
  have hdescent : baseEnd_3689305 < baseStart_3689305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689315 : List Nat := [1, 1, 1, 5, 3, 2, 1, 2, 7]
def baseStart_3689315 : Nat := 118140960795 + 3689315 * 2 ^ 59
def prefixEnd_3689315 : Nat := 4983230072969 + 3 ^ 40 * 3689315 * 2
def baseEnd_3689315 : Nat := 210487986760259807977295

theorem tailTrace_3689315 : CollatzResearch.WordTrace tailWord_3689315 prefixEnd_3689315 210487986760259807977295 := by
  unfold tailWord_3689315
  simp only [CollatzResearch.WordTrace]
  refine ⟨134560372629249314683493399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89706915086166209788995599 134560372629249314683493399)
  ·
    refine ⟨201840558943873972025240099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134560372629249314683493399 201840558943873972025240099)
    ·
      refine ⟨302760838415810958037860149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201840558943873972025240099 302760838415810958037860149)
      ·
        refine ⟨28383828601482277316049389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 302760838415810958037860149 28383828601482277316049389)
        ·
          refine ⟨10643935725555853993518521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28383828601482277316049389 10643935725555853993518521)
          ·
            refine ⟨7982951794166890495138891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10643935725555853993518521 7982951794166890495138891)
            ·
              refine ⟨11974427691250335742708337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7982951794166890495138891 11974427691250335742708337)
              ·
                refine ⟨8980820768437751807031253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11974427691250335742708337 8980820768437751807031253)
                ·
                  refine ⟨210487986760259807977295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8980820768437751807031253 210487986760259807977295)
                  ·
                    rfl

theorem cell23_3689315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 2, 7].length) (baseStart_3689315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3689315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3689315 prefixEnd_3689315 := by exact prefixLift 3689315
  have htrace : WordTrace (prefixWord ++ tailWord_3689315) baseStart_3689315 baseEnd_3689315 := by
    simpa [prefixWord, tailWord_3689315, baseEnd_3689315] using wordTrace_append hprefix tailTrace_3689315
  have hstable : (prefixWord ++ tailWord_3689315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689315).length < 2 ^ (prefixWord ++ tailWord_3689315).sum := by decide
  have hdescent : baseEnd_3689315 < baseStart_3689315 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689325 : List Nat := [1, 5, 1, 1, 1, 1, 1, 1, 3, 5, 3]
def baseStart_3689325 : Nat := 118140960795 + 3689325 * 2 ^ 59
def prefixEnd_3689325 : Nat := 4983230072969 + 3 ^ 40 * 3689325 * 2
def baseEnd_3689325 : Nat := 1894397015648883232670609

theorem tailTrace_3689325 : CollatzResearch.WordTrace tailWord_3689325 prefixEnd_3689325 1894397015648883232670609 := by
  unfold tailWord_3689325
  simp only [CollatzResearch.WordTrace]
  refine ⟨134560737359213086391357429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89707158239475390927571619 134560737359213086391357429)
  ·
    refine ⟨12615069127426226849189759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 134560737359213086391357429 12615069127426226849189759)
    ·
      refine ⟨18922603691139340273784639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12615069127426226849189759 18922603691139340273784639)
      ·
        refine ⟨28383905536709010410676959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18922603691139340273784639 28383905536709010410676959)
        ·
          refine ⟨42575858305063515616015439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28383905536709010410676959 42575858305063515616015439)
          ·
            refine ⟨63863787457595273424023159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42575858305063515616015439 63863787457595273424023159)
            ·
              refine ⟨95795681186392910136034739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63863787457595273424023159 95795681186392910136034739)
              ·
                refine ⟨143693521779589365204052109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95795681186392910136034739 143693521779589365204052109)
                ·
                  refine ⟨53885070667346011951519541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 143693521779589365204052109 53885070667346011951519541)
                  ·
                    refine ⟨5051725375063688620454957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53885070667346011951519541 5051725375063688620454957)
                    ·
                      refine ⟨1894397015648883232670609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5051725375063688620454957 1894397015648883232670609)
                      ·
                        rfl

theorem cell23_3689325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 5, 3].length) (baseStart_3689325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3689325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3689325 prefixEnd_3689325 := by exact prefixLift 3689325
  have htrace : WordTrace (prefixWord ++ tailWord_3689325) baseStart_3689325 baseEnd_3689325 := by
    simpa [prefixWord, tailWord_3689325, baseEnd_3689325] using wordTrace_append hprefix tailTrace_3689325
  have hstable : (prefixWord ++ tailWord_3689325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689325).length < 2 ^ (prefixWord ++ tailWord_3689325).sum := by decide
  have hdescent : baseEnd_3689325 < baseStart_3689325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689365 : List Nat := [1, 3, 2, 1, 1, 4, 1, 2, 1, 3, 4]
def baseStart_3689365 : Nat := 118140960795 + 3689365 * 2 ^ 59
def prefixEnd_3689365 : Nat := 4983230072969 + 3 ^ 40 * 3689365 * 2
def baseEnd_3689365 : Nat := 1894417554875063076170425

theorem tailTrace_3689365 : CollatzResearch.WordTrace tailWord_3689365 prefixEnd_3689365 1894417554875063076170425 := by
  unfold tailWord_3689365
  simp only [CollatzResearch.WordTrace]
  refine ⟨134562196279068173222813549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89708130852712115481875699 134562196279068173222813549)
  ·
    refine ⟨50460823604650564958555081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134562196279068173222813549 50460823604650564958555081)
    ·
      refine ⟨37845617703487923718916311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50460823604650564958555081 37845617703487923718916311)
      ·
        refine ⟨56768426555231885578374467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37845617703487923718916311 56768426555231885578374467)
        ·
          refine ⟨85152639832847828367561701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56768426555231885578374467 85152639832847828367561701)
          ·
            refine ⟨15966119968658967818917819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85152639832847828367561701 15966119968658967818917819)
            ·
              refine ⟨23949179952988451728376729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15966119968658967818917819 23949179952988451728376729)
              ·
                refine ⟨17961884964741338796282547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23949179952988451728376729 17961884964741338796282547)
                ·
                  refine ⟨26942827447112008194423821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17961884964741338796282547 26942827447112008194423821)
                  ·
                    refine ⟨10103560292667003072908933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26942827447112008194423821 10103560292667003072908933)
                    ·
                      refine ⟨1894417554875063076170425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10103560292667003072908933 1894417554875063076170425)
                      ·
                        rfl

theorem cell23_3689365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 2, 1, 3, 4].length) (baseStart_3689365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3689365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3689365 prefixEnd_3689365 := by exact prefixLift 3689365
  have htrace : WordTrace (prefixWord ++ tailWord_3689365) baseStart_3689365 baseEnd_3689365 := by
    simpa [prefixWord, tailWord_3689365, baseEnd_3689365] using wordTrace_append hprefix tailTrace_3689365
  have hstable : (prefixWord ++ tailWord_3689365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689365).length < 2 ^ (prefixWord ++ tailWord_3689365).sum := by decide
  have hdescent : baseEnd_3689365 < baseStart_3689365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689385 : List Nat := [1, 2, 1, 1, 1, 1, 5, 3, 1, 4, 3]
def baseStart_3689385 : Nat := 118140960795 + 3689385 * 2 ^ 59
def prefixEnd_3689385 : Nat := 4983230072969 + 3 ^ 40 * 3689385 * 2
def baseEnd_3689385 : Nat := 1894427824488152997920333

theorem tailTrace_3689385 : CollatzResearch.WordTrace tailWord_3689385 prefixEnd_3689385 1894427824488152997920333 := by
  unfold tailWord_3689385
  simp only [CollatzResearch.WordTrace]
  refine ⟨134562925738995716638541609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89708617159330477759027739 134562925738995716638541609)
  ·
    refine ⟨100922194304246787478906207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134562925738995716638541609 100922194304246787478906207)
    ·
      refine ⟨151383291456370181218359311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100922194304246787478906207 151383291456370181218359311)
      ·
        refine ⟨227074937184555271827538967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151383291456370181218359311 227074937184555271827538967)
        ·
          refine ⟨340612405776832907741308451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227074937184555271827538967 340612405776832907741308451)
          ·
            refine ⟨510918608665249361611962677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340612405776832907741308451 510918608665249361611962677)
            ·
              refine ⟨47898619562367127651121501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 510918608665249361611962677 47898619562367127651121501)
              ·
                refine ⟨17961982335887672869170563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47898619562367127651121501 17961982335887672869170563)
                ·
                  refine ⟨26942973503831509303755845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17961982335887672869170563 26942973503831509303755845)
                  ·
                    refine ⟨5051807531968407994454221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26942973503831509303755845 5051807531968407994454221)
                    ·
                      refine ⟨1894427824488152997920333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5051807531968407994454221 1894427824488152997920333)
                      ·
                        rfl

theorem cell23_3689385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3, 1, 4, 3].length) (baseStart_3689385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3689385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3689385 prefixEnd_3689385 := by exact prefixLift 3689385
  have htrace : WordTrace (prefixWord ++ tailWord_3689385) baseStart_3689385 baseEnd_3689385 := by
    simpa [prefixWord, tailWord_3689385, baseEnd_3689385] using wordTrace_append hprefix tailTrace_3689385
  have hstable : (prefixWord ++ tailWord_3689385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689385).length < 2 ^ (prefixWord ++ tailWord_3689385).sum := by decide
  have hdescent : baseEnd_3689385 < baseStart_3689385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689402 : List Nat := [3, 1, 1, 1, 2, 1, 5, 2, 2, 2, 3]
def baseStart_3689402 : Nat := 118140960795 + 3689402 * 2 ^ 59
def prefixEnd_3689402 : Nat := 4983230072969 + 3 ^ 40 * 3689402 * 2
def baseEnd_3689402 : Nat := 1894436553659279431407755

theorem tailTrace_3689402 : CollatzResearch.WordTrace tailWord_3689402 prefixEnd_3689402 1894436553659279431407755 := by
  unfold tailWord_3689402
  simp only [CollatzResearch.WordTrace]
  refine ⟨33640886444983532135477615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89709030519956085694606973 33640886444983532135477615)
  ·
    refine ⟨50461329667475298203216423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33640886444983532135477615 50461329667475298203216423)
    ·
      refine ⟨75691994501212947304824635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50461329667475298203216423 75691994501212947304824635)
      ·
        refine ⟨113537991751819420957236953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75691994501212947304824635 113537991751819420957236953)
        ·
          refine ⟨85153493813864565717927715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113537991751819420957236953 85153493813864565717927715)
          ·
            refine ⟨127730240720796848576891573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85153493813864565717927715 127730240720796848576891573)
            ·
              refine ⟨11974710067574704554083585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 127730240720796848576891573 11974710067574704554083585)
              ·
                refine ⟨8981032550681028415562689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11974710067574704554083585 8981032550681028415562689)
                ·
                  refine ⟨6735774413010771311672017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8981032550681028415562689 6735774413010771311672017)
                  ·
                    refine ⟨5051830809758078483754013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6735774413010771311672017 5051830809758078483754013)
                    ·
                      refine ⟨1894436553659279431407755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5051830809758078483754013 1894436553659279431407755)
                      ·
                        rfl

theorem cell23_3689402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 2, 2, 2, 3].length) (baseStart_3689402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3689402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3689402 prefixEnd_3689402 := by exact prefixLift 3689402
  have htrace : WordTrace (prefixWord ++ tailWord_3689402) baseStart_3689402 baseEnd_3689402 := by
    simpa [prefixWord, tailWord_3689402, baseEnd_3689402] using wordTrace_append hprefix tailTrace_3689402
  have hstable : (prefixWord ++ tailWord_3689402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689402).length < 2 ^ (prefixWord ++ tailWord_3689402).sum := by decide
  have hdescent : baseEnd_3689402 < baseStart_3689402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689422 : List Nat := [4, 1, 1, 1, 2, 4, 1, 3, 6]
def baseStart_3689422 : Nat := 118140960795 + 3689422 * 2 ^ 59
def prefixEnd_3689422 : Nat := 4983230072969 + 3 ^ 40 * 3689422 * 2
def baseEnd_3689422 : Nat := 210494091474707705906407

theorem tailTrace_3689422 : CollatzResearch.WordTrace tailWord_3689422 prefixEnd_3689422 210494091474707705906407 := by
  unfold tailWord_3689422
  simp only [CollatzResearch.WordTrace]
  refine ⟨16820534404982708994704815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89709516826574447971759013 16820534404982708994704815)
  ·
    refine ⟨25230801607474063492057223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16820534404982708994704815 25230801607474063492057223)
    ·
      refine ⟨37846202411211095238085835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25230801607474063492057223 37846202411211095238085835)
      ·
        refine ⟨56769303616816642857128753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37846202411211095238085835 56769303616816642857128753)
        ·
          refine ⟨42576977712612482142846565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56769303616816642857128753 42576977712612482142846565)
          ·
            refine ⟨7983183321114840401783731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42576977712612482142846565 7983183321114840401783731)
            ·
              refine ⟨11974774981672260602675597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7983183321114840401783731 11974774981672260602675597)
              ·
                refine ⟨4490540618127097726003349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11974774981672260602675597 4490540618127097726003349)
                ·
                  refine ⟨210494091474707705906407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4490540618127097726003349 210494091474707705906407)
                  ·
                    rfl

theorem cell23_3689422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 3, 6].length) (baseStart_3689422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3689422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3689422 prefixEnd_3689422 := by exact prefixLift 3689422
  have htrace : WordTrace (prefixWord ++ tailWord_3689422) baseStart_3689422 baseEnd_3689422 := by
    simpa [prefixWord, tailWord_3689422, baseEnd_3689422] using wordTrace_append hprefix tailTrace_3689422
  have hstable : (prefixWord ++ tailWord_3689422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689422).length < 2 ^ (prefixWord ++ tailWord_3689422).sum := by decide
  have hdescent : baseEnd_3689422 < baseStart_3689422 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689465 : List Nat := [1, 2, 1, 3, 1, 3, 1, 2, 3, 6]
def baseStart_3689465 : Nat := 118140960795 + 3689465 * 2 ^ 59
def prefixEnd_3689465 : Nat := 4983230072969 + 3 ^ 40 * 3689465 * 2
def baseEnd_3689465 : Nat := 631489634313504228306655

theorem tailTrace_3689465 : CollatzResearch.WordTrace tailWord_3689465 prefixEnd_3689465 631489634313504228306655 := by
  unfold tailWord_3689465
  simp only [CollatzResearch.WordTrace]
  refine ⟨134565843578705890301453849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89710562385803926867635899 134565843578705890301453849)
  ·
    refine ⟨100924382684029417726090387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134565843578705890301453849 100924382684029417726090387)
    ·
      refine ⟨151386574026044126589135581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100924382684029417726090387 151386574026044126589135581)
      ·
        refine ⟨56769965259766547470925843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151386574026044126589135581 56769965259766547470925843)
        ·
          refine ⟨85154947889649821206388765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56769965259766547470925843 85154947889649821206388765)
          ·
            refine ⟨31933105458618682952395787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85154947889649821206388765 31933105458618682952395787)
            ·
              refine ⟨47899658187928024428593681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31933105458618682952395787 47899658187928024428593681)
              ·
                refine ⟨35924743640946018321445261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47899658187928024428593681 35924743640946018321445261)
                ·
                  refine ⟨13471778865354756870541973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35924743640946018321445261 13471778865354756870541973)
                  ·
                    refine ⟨631489634313504228306655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13471778865354756870541973 631489634313504228306655)
                    ·
                      rfl

theorem cell23_3689465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 3, 6].length) (baseStart_3689465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3689465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3689465 prefixEnd_3689465 := by exact prefixLift 3689465
  have htrace : WordTrace (prefixWord ++ tailWord_3689465) baseStart_3689465 baseEnd_3689465 := by
    simpa [prefixWord, tailWord_3689465, baseEnd_3689465] using wordTrace_append hprefix tailTrace_3689465
  have hstable : (prefixWord ++ tailWord_3689465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689465).length < 2 ^ (prefixWord ++ tailWord_3689465).sum := by decide
  have hdescent : baseEnd_3689465 < baseStart_3689465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689482 : List Nat := [3, 1, 2, 2, 3, 1, 1, 3, 1, 6]
def baseStart_3689482 : Nat := 118140960795 + 3689482 * 2 ^ 59
def prefixEnd_3689482 : Nat := 4983230072969 + 3 ^ 40 * 3689482 * 2
def baseEnd_3689482 : Nat := 631492544037213039469129

theorem tailTrace_3689482 : CollatzResearch.WordTrace tailWord_3689482 prefixEnd_3689482 631492544037213039469129 := by
  unfold tailWord_3689482
  simp only [CollatzResearch.WordTrace]
  refine ⟨33641615904911075551205675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89710975746429534803215133 33641615904911075551205675)
  ·
    refine ⟨50462423857366613326808513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33641615904911075551205675 50462423857366613326808513)
    ·
      refine ⟨37846817893024959995106385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50462423857366613326808513 37846817893024959995106385)
      ·
        refine ⟨28385113419768719996329789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37846817893024959995106385 28385113419768719996329789)
        ·
          refine ⟨10644417532413269998623671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28385113419768719996329789 10644417532413269998623671)
          ·
            refine ⟨15966626298619904997935507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10644417532413269998623671 15966626298619904997935507)
            ·
              refine ⟨23949939447929857496903261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15966626298619904997935507 23949939447929857496903261)
              ·
                refine ⟨8981227292973696561338723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23949939447929857496903261 8981227292973696561338723)
                ·
                  refine ⟨13471840939460544842008085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8981227292973696561338723 13471840939460544842008085)
                  ·
                    refine ⟨631492544037213039469129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13471840939460544842008085 631492544037213039469129)
                    ·
                      rfl

theorem cell23_3689482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 3, 1, 6].length) (baseStart_3689482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3689482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3689482 prefixEnd_3689482 := by exact prefixLift 3689482
  have htrace : WordTrace (prefixWord ++ tailWord_3689482) baseStart_3689482 baseEnd_3689482 := by
    simpa [prefixWord, tailWord_3689482, baseEnd_3689482] using wordTrace_append hprefix tailTrace_3689482
  have hstable : (prefixWord ++ tailWord_3689482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689482).length < 2 ^ (prefixWord ++ tailWord_3689482).sum := by decide
  have hdescent : baseEnd_3689482 < baseStart_3689482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689506 : List Nat := [3, 3, 1, 1, 1, 3, 4, 1, 1, 1, 4]
def baseStart_3689506 : Nat := 118140960795 + 3689506 * 2 ^ 59
def prefixEnd_3689506 : Nat := 4983230072969 + 3 ^ 40 * 3689506 * 2
def baseEnd_3689506 : Nat := 1894489955647347024507277

theorem tailTrace_3689506 : CollatzResearch.WordTrace tailWord_3689506 prefixEnd_3689506 1894489955647347024507277 := by
  unfold tailWord_3689506
  simp only [CollatzResearch.WordTrace]
  refine ⟨33641834742889338575924093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89711559314371569535797581 33641834742889338575924093)
  ·
    refine ⟨12615688028583501965971535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33641834742889338575924093 12615688028583501965971535)
    ·
      refine ⟨18923532042875252948957303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12615688028583501965971535 18923532042875252948957303)
      ·
        refine ⟨28385298064312879423435955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18923532042875252948957303 28385298064312879423435955)
        ·
          refine ⟨42577947096469319135153933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28385298064312879423435955 42577947096469319135153933)
          ·
            refine ⟨15966730161175994675682725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42577947096469319135153933 15966730161175994675682725)
            ·
              refine ⟨2993761905220499001690511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15966730161175994675682725 2993761905220499001690511)
              ·
                refine ⟨4490642857830748502535767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2993761905220499001690511 4490642857830748502535767)
                ·
                  refine ⟨6735964286746122753803651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4490642857830748502535767 6735964286746122753803651)
                  ·
                    refine ⟨10103946430119184130705477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6735964286746122753803651 10103946430119184130705477)
                    ·
                      refine ⟨1894489955647347024507277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10103946430119184130705477 1894489955647347024507277)
                      ·
                        rfl

theorem cell23_3689506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 4, 1, 1, 1, 4].length) (baseStart_3689506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3689506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3689506 prefixEnd_3689506 := by exact prefixLift 3689506
  have htrace : WordTrace (prefixWord ++ tailWord_3689506) baseStart_3689506 baseEnd_3689506 := by
    simpa [prefixWord, tailWord_3689506, baseEnd_3689506] using wordTrace_append hprefix tailTrace_3689506
  have hstable : (prefixWord ++ tailWord_3689506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689506).length < 2 ^ (prefixWord ++ tailWord_3689506).sum := by decide
  have hdescent : baseEnd_3689506 < baseStart_3689506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689509 : List Nat := [1, 3, 1, 2, 2, 2, 3, 3, 1, 2, 3]
def baseStart_3689509 : Nat := 118140960795 + 3689509 * 2 ^ 59
def prefixEnd_3689509 : Nat := 4983230072969 + 3 ^ 40 * 3689509 * 2
def baseEnd_3689509 : Nat := 1894491496089310512769763

theorem tailTrace_3689509 : CollatzResearch.WordTrace tailWord_3689509 prefixEnd_3689509 1894491496089310512769763 := by
  unfold tailWord_3689509
  simp only [CollatzResearch.WordTrace]
  refine ⟨134567448390546485816055581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89711632260364323877370387 134567448390546485816055581)
  ·
    refine ⟨50462793146454932181020843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134567448390546485816055581 50462793146454932181020843)
    ·
      refine ⟨75694189719682398271531265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50462793146454932181020843 75694189719682398271531265)
      ·
        refine ⟨56770642289761798703648449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75694189719682398271531265 56770642289761798703648449)
        ·
          refine ⟨42577981717321349027736337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56770642289761798703648449 42577981717321349027736337)
          ·
            refine ⟨31933486287991011770802253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42577981717321349027736337 31933486287991011770802253)
            ·
              refine ⟨11975057357996629414050845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31933486287991011770802253 11975057357996629414050845)
              ·
                refine ⟨4490646509248736030269067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11975057357996629414050845 4490646509248736030269067)
                ·
                  refine ⟨6735969763873104045403601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4490646509248736030269067 6735969763873104045403601)
                  ·
                    refine ⟨5051977322904828034052701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6735969763873104045403601 5051977322904828034052701)
                    ·
                      refine ⟨1894491496089310512769763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5051977322904828034052701 1894491496089310512769763)
                      ·
                        rfl

theorem cell23_3689509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 3, 1, 2, 3].length) (baseStart_3689509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3689509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3689509 prefixEnd_3689509 := by exact prefixLift 3689509
  have htrace : WordTrace (prefixWord ++ tailWord_3689509) baseStart_3689509 baseEnd_3689509 := by
    simpa [prefixWord, tailWord_3689509, baseEnd_3689509] using wordTrace_append hprefix tailTrace_3689509
  have hstable : (prefixWord ++ tailWord_3689509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689509).length < 2 ^ (prefixWord ++ tailWord_3689509).sum := by decide
  have hdescent : baseEnd_3689509 < baseStart_3689509 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689545 : List Nat := [1, 2, 1, 1, 2, 2, 2, 1, 1, 2, 8]
def baseStart_3689545 : Nat := 118140960795 + 3689545 * 2 ^ 59
def prefixEnd_3689545 : Nat := 4983230072969 + 3 ^ 40 * 3689545 * 2
def baseEnd_3689545 : Nat := 1894509981392872371919597

theorem tailTrace_3689545 : CollatzResearch.WordTrace tailWord_3689545 prefixEnd_3689545 1894509981392872371919597 := by
  unfold tailWord_3689545
  simp only [CollatzResearch.WordTrace]
  refine ⟨134568761418416063964366089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89712507612277375976244059 134568761418416063964366089)
  ·
    refine ⟨100926571063812047973274567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134568761418416063964366089 100926571063812047973274567)
    ·
      refine ⟨151389856595718071959911851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100926571063812047973274567 151389856595718071959911851)
      ·
        refine ⟨227084784893577107939867777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151389856595718071959911851 227084784893577107939867777)
        ·
          refine ⟨170313588670182830954900833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227084784893577107939867777 170313588670182830954900833)
          ·
            refine ⟨127735191502637123216175625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170313588670182830954900833 127735191502637123216175625)
            ·
              refine ⟨95801393626977842412131719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127735191502637123216175625 95801393626977842412131719)
              ·
                refine ⟨143702090440466763618197579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95801393626977842412131719 143702090440466763618197579)
                ·
                  refine ⟨215553135660700145427296369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143702090440466763618197579 215553135660700145427296369)
                  ·
                    refine ⟨161664851745525109070472277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 215553135660700145427296369 161664851745525109070472277)
                    ·
                      refine ⟨1894509981392872371919597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 161664851745525109070472277 1894509981392872371919597)
                      ·
                        rfl

theorem cell23_3689545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 2, 8].length) (baseStart_3689545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3689545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3689545 prefixEnd_3689545 := by exact prefixLift 3689545
  have htrace : WordTrace (prefixWord ++ tailWord_3689545) baseStart_3689545 baseEnd_3689545 := by
    simpa [prefixWord, tailWord_3689545, baseEnd_3689545] using wordTrace_append hprefix tailTrace_3689545
  have hstable : (prefixWord ++ tailWord_3689545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689545).length < 2 ^ (prefixWord ++ tailWord_3689545).sum := by decide
  have hdescent : baseEnd_3689545 < baseStart_3689545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689555 : List Nat := [1, 1, 1, 2, 1, 1, 2, 3, 3, 8]
def baseStart_3689555 : Nat := 118140960795 + 3689555 * 2 ^ 59
def prefixEnd_3689555 : Nat := 4983230072969 + 3 ^ 40 * 3689555 * 2
def baseEnd_3689555 : Nat := 631505038733139110931517

theorem tailTrace_3689555 : CollatzResearch.WordTrace tailWord_3689555 prefixEnd_3689555 631505038733139110931517 := by
  unfold tailWord_3689555
  simp only [CollatzResearch.WordTrace]
  refine ⟨134569126148379835672230119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89712750765586557114820079 134569126148379835672230119)
  ·
    refine ⟨201853689222569753508345179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134569126148379835672230119 201853689222569753508345179)
    ·
      refine ⟨302780533833854630262517769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201853689222569753508345179 302780533833854630262517769)
      ·
        refine ⟨227085400375390972696888327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302780533833854630262517769 227085400375390972696888327)
        ·
          refine ⟨340628100563086459045332491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227085400375390972696888327 340628100563086459045332491)
          ·
            refine ⟨510942150844629688567998737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340628100563086459045332491 510942150844629688567998737)
            ·
              refine ⟨383206613133472266425999053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 510942150844629688567998737 383206613133472266425999053)
              ·
                refine ⟨143702479925052099909749645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 383206613133472266425999053 143702479925052099909749645)
                ·
                  refine ⟨53888429971894537466156117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 143702479925052099909749645 53888429971894537466156117)
                  ·
                    refine ⟨631505038733139110931517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 53888429971894537466156117 631505038733139110931517)
                    ·
                      rfl

theorem cell23_3689555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 8].length) (baseStart_3689555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3689555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3689555 prefixEnd_3689555 := by exact prefixLift 3689555
  have htrace : WordTrace (prefixWord ++ tailWord_3689555) baseStart_3689555 baseEnd_3689555 := by
    simpa [prefixWord, tailWord_3689555, baseEnd_3689555] using wordTrace_append hprefix tailTrace_3689555
  have hstable : (prefixWord ++ tailWord_3689555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689555).length < 2 ^ (prefixWord ++ tailWord_3689555).sum := by decide
  have hdescent : baseEnd_3689555 < baseStart_3689555 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689592 : List Nat := [2, 1, 2, 1, 1, 1, 4, 3, 2, 2, 4]
def baseStart_3689592 : Nat := 118140960795 + 3689592 * 2 ^ 59
def prefixEnd_3689592 : Nat := 4983230072969 + 3 ^ 40 * 3689592 * 2
def baseEnd_3689592 : Nat := 1894534114983633688031881

theorem tailTrace_3689592 : CollatzResearch.WordTrace tailWord_3689592 prefixEnd_3689592 1894534114983633688031881 := by
  unfold tailWord_3689592
  simp only [CollatzResearch.WordTrace]
  refine ⟨67285237824622895495663515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89713650432830527327551353 67285237824622895495663515)
  ·
    refine ⟨100927856736934343243495273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67285237824622895495663515 100927856736934343243495273)
    ·
      refine ⟨75695892552700757432621455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100927856736934343243495273 75695892552700757432621455)
      ·
        refine ⟨113543838829051136148932183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75695892552700757432621455 113543838829051136148932183)
        ·
          refine ⟨170315758243576704223398275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113543838829051136148932183 170315758243576704223398275)
          ·
            refine ⟨255473637365365056335097413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170315758243576704223398275 255473637365365056335097413)
            ·
              refine ⟨47901307006005948062830765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 255473637365365056335097413 47901307006005948062830765)
              ·
                refine ⟨17962990127252230523561537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47901307006005948062830765 17962990127252230523561537)
                ·
                  refine ⟨13472242595439172892671153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17962990127252230523561537 13472242595439172892671153)
                  ·
                    refine ⟨10104181946579379669503365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13472242595439172892671153 10104181946579379669503365)
                    ·
                      refine ⟨1894534114983633688031881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10104181946579379669503365 1894534114983633688031881)
                      ·
                        rfl

theorem cell23_3689592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3, 2, 2, 4].length) (baseStart_3689592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3689592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3689592 prefixEnd_3689592 := by exact prefixLift 3689592
  have htrace : WordTrace (prefixWord ++ tailWord_3689592) baseStart_3689592 baseEnd_3689592 := by
    simpa [prefixWord, tailWord_3689592, baseEnd_3689592] using wordTrace_append hprefix tailTrace_3689592
  have hstable : (prefixWord ++ tailWord_3689592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689592).length < 2 ^ (prefixWord ++ tailWord_3689592).sum := by decide
  have hdescent : baseEnd_3689592 < baseStart_3689592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689629 : List Nat := [1, 4, 2, 1, 1, 2, 2, 2, 2, 3, 3]
def baseStart_3689629 : Nat := 118140960795 + 3689629 * 2 ^ 59
def prefixEnd_3689629 : Nat := 4983230072969 + 3 ^ 40 * 3689629 * 2
def baseEnd_3689629 : Nat := 1894553113767850043269211

theorem tailTrace_3689629 : CollatzResearch.WordTrace tailWord_3689629 prefixEnd_3689629 1894553113767850043269211 := by
  unfold tailWord_3689629
  simp only [CollatzResearch.WordTrace]
  refine ⟨134571825150111746310423941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89714550100074497540282627 134571825150111746310423941)
  ·
    refine ⟨25232217215645952433204489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134571825150111746310423941 25232217215645952433204489)
    ·
      refine ⟨18924162911734464324903367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25232217215645952433204489 18924162911734464324903367)
      ·
        refine ⟨28386244367601696487355051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18924162911734464324903367 28386244367601696487355051)
        ·
          refine ⟨42579366551402544731032577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28386244367601696487355051 42579366551402544731032577)
          ·
            refine ⟨31934524913551908548274433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42579366551402544731032577 31934524913551908548274433)
            ·
              refine ⟨23950893685163931411205825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31934524913551908548274433 23950893685163931411205825)
              ·
                refine ⟨17963170263872948558404369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23950893685163931411205825 17963170263872948558404369)
                ·
                  refine ⟨13472377697904711418803277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17963170263872948558404369 13472377697904711418803277)
                  ·
                    refine ⟨5052141636714266782051229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13472377697904711418803277 5052141636714266782051229)
                    ·
                      refine ⟨1894553113767850043269211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5052141636714266782051229 1894553113767850043269211)
                      ·
                        rfl

theorem cell23_3689629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 2, 2, 3, 3].length) (baseStart_3689629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3689629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3689629 prefixEnd_3689629 := by exact prefixLift 3689629
  have htrace : WordTrace (prefixWord ++ tailWord_3689629) baseStart_3689629 baseEnd_3689629 := by
    simpa [prefixWord, tailWord_3689629, baseEnd_3689629] using wordTrace_append hprefix tailTrace_3689629
  have hstable : (prefixWord ++ tailWord_3689629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689629).length < 2 ^ (prefixWord ++ tailWord_3689629).sum := by decide
  have hdescent : baseEnd_3689629 < baseStart_3689629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689630 : List Nat := [4, 3, 1, 1, 2, 1, 1, 4, 2, 2, 2]
def baseStart_3689630 : Nat := 118140960795 + 3689630 * 2 ^ 59
def prefixEnd_3689630 : Nat := 4983230072969 + 3 ^ 40 * 3689630 * 2
def baseEnd_3689630 : Nat := 1894553627248504539356707

theorem tailTrace_3689630 : CollatzResearch.WordTrace tailWord_3689630 prefixEnd_3689630 1894553627248504539356707 := by
  unfold tailWord_3689630
  simp only [CollatzResearch.WordTrace]
  refine ⟨16821482702888515435151293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89714574415405415654140229 16821482702888515435151293)
  ·
    refine ⟨6308056013583193288181735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16821482702888515435151293 6308056013583193288181735)
    ·
      refine ⟨9462084020374789932272603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6308056013583193288181735 9462084020374789932272603)
      ·
        refine ⟨14193126030562184898408905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9462084020374789932272603 14193126030562184898408905)
        ·
          refine ⟨10644844522921638673806679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14193126030562184898408905 10644844522921638673806679)
          ·
            refine ⟨15967266784382458010710019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10644844522921638673806679 15967266784382458010710019)
            ·
              refine ⟨23950900176573687016065029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15967266784382458010710019 23950900176573687016065029)
              ·
                refine ⟨4490793783107566315512193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23950900176573687016065029 4490793783107566315512193)
                ·
                  refine ⟨3368095337330674736634145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4490793783107566315512193 3368095337330674736634145)
                  ·
                    refine ⟨2526071502998006052475609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3368095337330674736634145 2526071502998006052475609)
                    ·
                      refine ⟨1894553627248504539356707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2526071502998006052475609 1894553627248504539356707)
                      ·
                        rfl

theorem cell23_3689630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 4, 2, 2, 2].length) (baseStart_3689630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3689630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3689630 prefixEnd_3689630 := by exact prefixLift 3689630
  have htrace : WordTrace (prefixWord ++ tailWord_3689630) baseStart_3689630 baseEnd_3689630 := by
    simpa [prefixWord, tailWord_3689630, baseEnd_3689630] using wordTrace_append hprefix tailTrace_3689630
  have hstable : (prefixWord ++ tailWord_3689630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689630).length < 2 ^ (prefixWord ++ tailWord_3689630).sum := by decide
  have hdescent : baseEnd_3689630 < baseStart_3689630 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689636 : List Nat := [2, 3, 1, 2, 3, 2, 1, 4, 5]
def baseStart_3689636 : Nat := 118140960795 + 3689636 * 2 ^ 59
def prefixEnd_3689636 : Nat := 4983230072969 + 3 ^ 40 * 3689636 * 2
def baseEnd_3689636 : Nat := 210506300903603501764631

theorem tailTrace_3689636 : CollatzResearch.WordTrace tailWord_3689636 prefixEnd_3689636 210506300903603501764631 := by
  unfold tailWord_3689636
  simp only [CollatzResearch.WordTrace]
  refine ⟨67286040230543193252964381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89714720307390924337285841 67286040230543193252964381)
  ·
    refine ⟨25232265086453697469861643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67286040230543193252964381 25232265086453697469861643)
    ·
      refine ⟨37848397629680546204792465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25232265086453697469861643 37848397629680546204792465)
      ·
        refine ⟨28386298222260409653594349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37848397629680546204792465 28386298222260409653594349)
        ·
          refine ⟨10644861833347653620097881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28386298222260409653594349 10644861833347653620097881)
          ·
            refine ⟨7983646375010740215073411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10644861833347653620097881 7983646375010740215073411)
            ·
              refine ⟨11975469562516110322610117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7983646375010740215073411 11975469562516110322610117)
              ·
                refine ⟨2245400542971770685489397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11975469562516110322610117 2245400542971770685489397)
                ·
                  refine ⟨210506300903603501764631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2245400542971770685489397 210506300903603501764631)
                  ·
                    rfl

theorem cell23_3689636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 4, 5].length) (baseStart_3689636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3689636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3689636 prefixEnd_3689636 := by exact prefixLift 3689636
  have htrace : WordTrace (prefixWord ++ tailWord_3689636) baseStart_3689636 baseEnd_3689636 := by
    simpa [prefixWord, tailWord_3689636, baseEnd_3689636] using wordTrace_append hprefix tailTrace_3689636
  have hstable : (prefixWord ++ tailWord_3689636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689636).length < 2 ^ (prefixWord ++ tailWord_3689636).sum := by decide
  have hdescent : baseEnd_3689636 < baseStart_3689636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689669 : List Nat := [1, 3, 1, 1, 1, 1, 3, 1, 3, 6, 2]
def baseStart_3689669 : Nat := 118140960795 + 3689669 * 2 ^ 59
def prefixEnd_3689669 : Nat := 4983230072969 + 3 ^ 40 * 3689669 * 2
def baseEnd_3689669 : Nat := 1894573652994029886769027

theorem tailTrace_3689669 : CollatzResearch.WordTrace tailWord_3689669 prefixEnd_3689669 1894573652994029886769027 := by
  unfold tailWord_3689669
  simp only [CollatzResearch.WordTrace]
  refine ⟨134573284069966833141880061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89715522713311222094586707 134573284069966833141880061)
  ·
    refine ⟨50464981526237562428205023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134573284069966833141880061 50464981526237562428205023)
    ·
      refine ⟨75697472289356343642307535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50464981526237562428205023 75697472289356343642307535)
      ·
        refine ⟨113546208434034515463461303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75697472289356343642307535 113546208434034515463461303)
        ·
          refine ⟨170319312651051773195191955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113546208434034515463461303 170319312651051773195191955)
          ·
            refine ⟨255478968976577659792787933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170319312651051773195191955 255478968976577659792787933)
            ·
              refine ⟨95804613366216622422295475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 255478968976577659792787933 95804613366216622422295475)
              ·
                refine ⟨143706920049324933633443213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95804613366216622422295475 143706920049324933633443213)
                ·
                  refine ⟨53890095018496850112541205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 143706920049324933633443213 53890095018496850112541205)
                  ·
                    refine ⟨2526098203992039849025369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 53890095018496850112541205 2526098203992039849025369)
                    ·
                      refine ⟨1894573652994029886769027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2526098203992039849025369 1894573652994029886769027)
                      ·
                        rfl

theorem cell23_3689669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 6, 2].length) (baseStart_3689669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3689669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3689669 prefixEnd_3689669 := by exact prefixLift 3689669
  have htrace : WordTrace (prefixWord ++ tailWord_3689669) baseStart_3689669 baseEnd_3689669 := by
    simpa [prefixWord, tailWord_3689669, baseEnd_3689669] using wordTrace_append hprefix tailTrace_3689669
  have hstable : (prefixWord ++ tailWord_3689669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689669).length < 2 ^ (prefixWord ++ tailWord_3689669).sum := by decide
  have hdescent : baseEnd_3689669 < baseStart_3689669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689689 : List Nat := [1, 2, 1, 2, 3, 1, 1, 3, 4, 2, 3]
def baseStart_3689689 : Nat := 118140960795 + 3689689 * 2 ^ 59
def prefixEnd_3689689 : Nat := 4983230072969 + 3 ^ 40 * 3689689 * 2
def baseEnd_3689689 : Nat := 1894583922607119808518935

theorem tailTrace_3689689 : CollatzResearch.WordTrace tailWord_3689689 prefixEnd_3689689 1894583922607119808518935 := by
  unfold tailWord_3689689
  simp only [CollatzResearch.WordTrace]
  refine ⟨134574013529894376557608121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89716009019929584371738747 134574013529894376557608121)
  ·
    refine ⟨100930510147420782418206091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134574013529894376557608121 100930510147420782418206091)
    ·
      refine ⟨151395765221131173627309137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100930510147420782418206091 151395765221131173627309137)
      ·
        refine ⟨113546823915848380220481853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151395765221131173627309137 113546823915848380220481853)
        ·
          refine ⟨42580058968443142582680695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113546823915848380220481853 42580058968443142582680695)
          ·
            refine ⟨63870088452664713874021043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42580058968443142582680695 63870088452664713874021043)
            ·
              refine ⟨95805132678997070811031565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63870088452664713874021043 95805132678997070811031565)
              ·
                refine ⟨35926924754623901554136837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95805132678997070811031565 35926924754623901554136837)
                ·
                  refine ⟨6736298391491981541400657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35926924754623901554136837 6736298391491981541400657)
                  ·
                    refine ⟨5052223793618986156050493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6736298391491981541400657 5052223793618986156050493)
                    ·
                      refine ⟨1894583922607119808518935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5052223793618986156050493 1894583922607119808518935)
                      ·
                        rfl

theorem cell23_3689689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 4, 2, 3].length) (baseStart_3689689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3689689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3689689 prefixEnd_3689689 := by exact prefixLift 3689689
  have htrace : WordTrace (prefixWord ++ tailWord_3689689) baseStart_3689689 baseEnd_3689689 := by
    simpa [prefixWord, tailWord_3689689, baseEnd_3689689] using wordTrace_append hprefix tailTrace_3689689
  have hstable : (prefixWord ++ tailWord_3689689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689689).length < 2 ^ (prefixWord ++ tailWord_3689689).sum := by decide
  have hdescent : baseEnd_3689689 < baseStart_3689689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689696 : List Nat := [2, 1, 1, 3, 1, 5, 2, 1, 3, 4]
def baseStart_3689696 : Nat := 118140960795 + 3689696 * 2 ^ 59
def prefixEnd_3689696 : Nat := 4983230072969 + 3 ^ 40 * 3689696 * 2
def baseEnd_3689696 : Nat := 631529172323900427043801

theorem tailTrace_3689696 : CollatzResearch.WordTrace tailWord_3689696 prefixEnd_3689696 631529172323900427043801 := by
  unfold tailWord_3689696
  simp only [CollatzResearch.WordTrace]
  refine ⟨67287134420434508376556471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89716179227246011168741961 67287134420434508376556471)
  ·
    refine ⟨100930701630651762564834707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67287134420434508376556471 100930701630651762564834707)
    ·
      refine ⟨151396052445977643847252061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100930701630651762564834707 151396052445977643847252061)
      ·
        refine ⟨56773519667241616442719523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151396052445977643847252061 56773519667241616442719523)
        ·
          refine ⟨85160279500862424664079285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56773519667241616442719523 85160279500862424664079285)
          ·
            refine ⟨7983776203205852312257433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 85160279500862424664079285 7983776203205852312257433)
            ·
              refine ⟨5987832152404389234193075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7983776203205852312257433 5987832152404389234193075)
              ·
                refine ⟨8981748228606583851289613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5987832152404389234193075 8981748228606583851289613)
                ·
                  refine ⟨3368155585727468944233605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8981748228606583851289613 3368155585727468944233605)
                  ·
                    refine ⟨631529172323900427043801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3368155585727468944233605 631529172323900427043801)
                    ·
                      rfl

theorem cell23_3689696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 1, 3, 4].length) (baseStart_3689696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3689696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3689696 prefixEnd_3689696 := by exact prefixLift 3689696
  have htrace : WordTrace (prefixWord ++ tailWord_3689696) baseStart_3689696 baseEnd_3689696 := by
    simpa [prefixWord, tailWord_3689696, baseEnd_3689696] using wordTrace_append hprefix tailTrace_3689696
  have hstable : (prefixWord ++ tailWord_3689696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689696).length < 2 ^ (prefixWord ++ tailWord_3689696).sum := by decide
  have hdescent : baseEnd_3689696 < baseStart_3689696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689760 : List Nat := [2, 1, 1, 5, 4, 1, 2, 1, 6]
def baseStart_3689760 : Nat := 118140960795 + 3689760 * 2 ^ 59
def prefixEnd_3689760 : Nat := 4983230072969 + 3 ^ 40 * 3689760 * 2
def baseEnd_3689760 : Nat := 210513375525954336747901

theorem tailTrace_3689760 : CollatzResearch.WordTrace tailWord_3689760 prefixEnd_3689760 210513375525954336747901 := by
  unfold tailWord_3689760
  simp only [CollatzResearch.WordTrace]
  refine ⟨67288301556318577841721367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89717735408424770455628489 67288301556318577841721367)
  ·
    refine ⟨100932452334477866762582051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67288301556318577841721367 100932452334477866762582051)
    ·
      refine ⟨151398678501716800143873077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100932452334477866762582051 151398678501716800143873077)
      ·
        refine ⟨14193626109535950013488101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 151398678501716800143873077 14193626109535950013488101)
        ·
          refine ⟨2661304895537990627529019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14193626109535950013488101 2661304895537990627529019)
          ·
            refine ⟨3991957343306985941293529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2661304895537990627529019 3991957343306985941293529)
            ·
              refine ⟨2993968007480239455970147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3991957343306985941293529 2993968007480239455970147)
              ·
                refine ⟨4490952011220359183955221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2993968007480239455970147 4490952011220359183955221)
                ·
                  refine ⟨210513375525954336747901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4490952011220359183955221 210513375525954336747901)
                  ·
                    rfl

theorem cell23_3689760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 2, 1, 6].length) (baseStart_3689760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3689760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3689760 prefixEnd_3689760 := by exact prefixLift 3689760
  have htrace : WordTrace (prefixWord ++ tailWord_3689760) baseStart_3689760 baseEnd_3689760 := by
    simpa [prefixWord, tailWord_3689760, baseEnd_3689760] using wordTrace_append hprefix tailTrace_3689760
  have hstable : (prefixWord ++ tailWord_3689760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689760).length < 2 ^ (prefixWord ++ tailWord_3689760).sum := by decide
  have hdescent : baseEnd_3689760 < baseStart_3689760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689773 : List Nat := [1, 5, 3, 1, 1, 2, 1, 1, 3, 5]
def baseStart_3689773 : Nat := 118140960795 + 3689773 * 2 ^ 59
def prefixEnd_3689773 : Nat := 4983230072969 + 3 ^ 40 * 3689773 * 2
def baseEnd_3689773 : Nat := 631542351660699159956183

theorem tailTrace_3689773 : CollatzResearch.WordTrace tailWord_3689773 prefixEnd_3689773 631542351660699159956183 := by
  unfold tailWord_3689773
  simp only [CollatzResearch.WordTrace]
  refine ⟨134577077261590058903665973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89718051507726705935777315 134577077261590058903665973)
  ·
    refine ⟨12616600993274068022218685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 134577077261590058903665973 12616600993274068022218685)
    ·
      refine ⟨4731225372477775508332007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12616600993274068022218685 4731225372477775508332007)
      ·
        refine ⟨7096838058716663262498011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4731225372477775508332007 7096838058716663262498011)
        ·
          refine ⟨10645257088074994893747017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7096838058716663262498011 10645257088074994893747017)
          ·
            refine ⟨7983942816056246170310263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10645257088074994893747017 7983942816056246170310263)
            ·
              refine ⟨11975914224084369255465395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7983942816056246170310263 11975914224084369255465395)
              ·
                refine ⟨17963871336126553883198093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11975914224084369255465395 17963871336126553883198093)
                ·
                  refine ⟨6736451751047457706199285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17963871336126553883198093 6736451751047457706199285)
                  ·
                    refine ⟨631542351660699159956183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6736451751047457706199285 631542351660699159956183)
                    ·
                      rfl

theorem cell23_3689773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_3689773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3689773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3689773 prefixEnd_3689773 := by exact prefixLift 3689773
  have htrace : WordTrace (prefixWord ++ tailWord_3689773) baseStart_3689773 baseEnd_3689773 := by
    simpa [prefixWord, tailWord_3689773, baseEnd_3689773] using wordTrace_append hprefix tailTrace_3689773
  have hstable : (prefixWord ++ tailWord_3689773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689773).length < 2 ^ (prefixWord ++ tailWord_3689773).sum := by decide
  have hdescent : baseEnd_3689773 < baseStart_3689773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689780 : List Nat := [2, 5, 1, 1, 1, 1, 4, 1, 2, 3, 2]
def baseStart_3689780 : Nat := 118140960795 + 3689780 * 2 ^ 59
def prefixEnd_3689780 : Nat := 4983230072969 + 3 ^ 40 * 3689780 * 2
def baseEnd_3689780 : Nat := 1894630649346678952481017

theorem tailTrace_3689780 : CollatzResearch.WordTrace tailWord_3689780 prefixEnd_3689780 1894630649346678952481017 := by
  unfold tailWord_3689780
  simp only [CollatzResearch.WordTrace]
  refine ⟨67288666286282349549585397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89718221715043132732780529 67288666286282349549585397)
  ·
    refine ⟨6308312464338970270273631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67288666286282349549585397 6308312464338970270273631)
    ·
      refine ⟨9462468696508455405410447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6308312464338970270273631 9462468696508455405410447)
      ·
        refine ⟨14193703044762683108115671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9462468696508455405410447 14193703044762683108115671)
        ·
          refine ⟨21290554567144024662173507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14193703044762683108115671 21290554567144024662173507)
          ·
            refine ⟨31935831850716036993260261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21290554567144024662173507 31935831850716036993260261)
            ·
              refine ⟨5987968472009256936236299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31935831850716036993260261 5987968472009256936236299)
              ·
                refine ⟨8981952708013885404354449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5987968472009256936236299 8981952708013885404354449)
                ·
                  refine ⟨6736464531010414053265837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8981952708013885404354449 6736464531010414053265837)
                  ·
                    refine ⟨2526174199128905269974689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6736464531010414053265837 2526174199128905269974689)
                    ·
                      refine ⟨1894630649346678952481017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2526174199128905269974689 1894630649346678952481017)
                      ·
                        rfl

theorem cell23_3689780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 1, 2, 3, 2].length) (baseStart_3689780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3689780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3689780 prefixEnd_3689780 := by exact prefixLift 3689780
  have htrace : WordTrace (prefixWord ++ tailWord_3689780) baseStart_3689780 baseEnd_3689780 := by
    simpa [prefixWord, tailWord_3689780, baseEnd_3689780] using wordTrace_append hprefix tailTrace_3689780
  have hstable : (prefixWord ++ tailWord_3689780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689780).length < 2 ^ (prefixWord ++ tailWord_3689780).sum := by decide
  have hdescent : baseEnd_3689780 < baseStart_3689780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689798 : List Nat := [6, 1, 1, 3, 2, 1, 2, 2, 1, 4]
def baseStart_3689798 : Nat := 118140960795 + 3689798 * 2 ^ 59
def prefixEnd_3689798 : Nat := 4983230072969 + 3 ^ 40 * 3689798 * 2
def baseEnd_3689798 : Nat := 631546630666153294018645

theorem tailTrace_3689798 : CollatzResearch.WordTrace tailWord_3689798 prefixEnd_3689798 631546630666153294018645 := by
  unfold tailWord_3689798
  simp only [CollatzResearch.WordTrace]
  refine ⟨4205562158953109005416439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 89718659390999658782217365 4205562158953109005416439)
  ·
    refine ⟨6308343238429663508124659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4205562158953109005416439 6308343238429663508124659)
    ·
      refine ⟨9462514857644495262186989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6308343238429663508124659 9462514857644495262186989)
      ·
        refine ⟨3548443071616685723320121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9462514857644495262186989 3548443071616685723320121)
        ·
          refine ⟨2661332303712514292490091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3548443071616685723320121 2661332303712514292490091)
          ·
            refine ⟨3991998455568771438735137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2661332303712514292490091 3991998455568771438735137)
            ·
              refine ⟨2993998841676578579051353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3991998455568771438735137 2993998841676578579051353)
              ·
                refine ⟨2245499131257433934288515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2993998841676578579051353 2245499131257433934288515)
                ·
                  refine ⟨3368248696886150901432773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2245499131257433934288515 3368248696886150901432773)
                  ·
                    refine ⟨631546630666153294018645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3368248696886150901432773 631546630666153294018645)
                    ·
                      rfl

theorem cell23_3689798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_3689798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3689798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3689798 prefixEnd_3689798 := by exact prefixLift 3689798
  have htrace : WordTrace (prefixWord ++ tailWord_3689798) baseStart_3689798 baseEnd_3689798 := by
    simpa [prefixWord, tailWord_3689798, baseEnd_3689798] using wordTrace_append hprefix tailTrace_3689798
  have hstable : (prefixWord ++ tailWord_3689798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689798).length < 2 ^ (prefixWord ++ tailWord_3689798).sum := by decide
  have hdescent : baseEnd_3689798 < baseStart_3689798 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689829 : List Nat := [1, 3, 1, 3, 1, 2, 1, 2, 2, 7]
def baseStart_3689829 : Nat := 118140960795 + 3689829 * 2 ^ 59
def prefixEnd_3689829 : Nat := 4983230072969 + 3 ^ 40 * 3689829 * 2
def baseEnd_3689829 : Nat := 631551936632916420256097

theorem tailTrace_3689829 : CollatzResearch.WordTrace tailWord_3689829 prefixEnd_3689829 631551936632916420256097 := by
  unfold tailWord_3689829
  simp only [CollatzResearch.WordTrace]
  refine ⟨134579119749387180467704541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89719413166258120311803027 134579119749387180467704541)
  ·
    refine ⟨50467169906020192675389203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134579119749387180467704541 50467169906020192675389203)
    ·
      refine ⟨75700754859030289013083805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50467169906020192675389203 75700754859030289013083805)
      ·
        refine ⟨28387783072136358379906427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75700754859030289013083805 28387783072136358379906427)
        ·
          refine ⟨42581674608204537569859641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28387783072136358379906427 42581674608204537569859641)
          ·
            refine ⟨31936255956153403177394731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42581674608204537569859641 31936255956153403177394731)
            ·
              refine ⟨47904383934230104766092097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31936255956153403177394731 47904383934230104766092097)
              ·
                refine ⟨35928287950672578574569073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47904383934230104766092097 35928287950672578574569073)
                ·
                  refine ⟨26946215963004433930926805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35928287950672578574569073 26946215963004433930926805)
                  ·
                    refine ⟨631551936632916420256097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26946215963004433930926805 631551936632916420256097)
                    ·
                      rfl

theorem cell23_3689829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 7].length) (baseStart_3689829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3689829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3689829 prefixEnd_3689829 := by exact prefixLift 3689829
  have htrace : WordTrace (prefixWord ++ tailWord_3689829) baseStart_3689829 baseEnd_3689829 := by
    simpa [prefixWord, tailWord_3689829, baseEnd_3689829] using wordTrace_append hprefix tailTrace_3689829
  have hstable : (prefixWord ++ tailWord_3689829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689829).length < 2 ^ (prefixWord ++ tailWord_3689829).sum := by decide
  have hdescent : baseEnd_3689829 < baseStart_3689829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689839 : List Nat := [1, 1, 2, 1, 3, 1, 4, 1, 2, 2, 5]
def baseStart_3689839 : Nat := 118140960795 + 3689839 * 2 ^ 59
def prefixEnd_3689839 : Nat := 4983230072969 + 3 ^ 40 * 3689839 * 2
def baseEnd_3689839 : Nat := 1894660944705294221643245

theorem tailTrace_3689839 : CollatzResearch.WordTrace tailWord_3689839 prefixEnd_3689839 1894660944705294221643245 := by
  unfold tailWord_3689839
  simp only [CollatzResearch.WordTrace]
  refine ⟨134579484479350952175568571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89719656319567301450379047 134579484479350952175568571)
  ·
    refine ⟨201869226719026428263352857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134579484479350952175568571 201869226719026428263352857)
    ·
      refine ⟨151401920039269821197514643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201869226719026428263352857 151401920039269821197514643)
      ·
        refine ⟨227102880058904731796271965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151401920039269821197514643 227102880058904731796271965)
        ·
          refine ⟨85163580022089274423601987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227102880058904731796271965 85163580022089274423601987)
          ·
            refine ⟨127745370033133911635402981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85163580022089274423601987 127745370033133911635402981)
            ·
              refine ⟨23952256881212608431638059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 127745370033133911635402981 23952256881212608431638059)
              ·
                refine ⟨35928385321818912647457089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23952256881212608431638059 35928385321818912647457089)
                ·
                  refine ⟨26946288991364184485592817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35928385321818912647457089 26946288991364184485592817)
                  ·
                    refine ⟨20209716743523138364194613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26946288991364184485592817 20209716743523138364194613)
                    ·
                      refine ⟨1894660944705294221643245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20209716743523138364194613 1894660944705294221643245)
                      ·
                        rfl

theorem cell23_3689839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 2, 2, 5].length) (baseStart_3689839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3689839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3689839 prefixEnd_3689839 := by exact prefixLift 3689839
  have htrace : WordTrace (prefixWord ++ tailWord_3689839) baseStart_3689839 baseEnd_3689839 := by
    simpa [prefixWord, tailWord_3689839, baseEnd_3689839] using wordTrace_append hprefix tailTrace_3689839
  have hstable : (prefixWord ++ tailWord_3689839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689839).length < 2 ^ (prefixWord ++ tailWord_3689839).sum := by decide
  have hdescent : baseEnd_3689839 < baseStart_3689839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689854 : List Nat := [4, 2, 3, 2, 1, 2, 1, 2, 2, 4]
def baseStart_3689854 : Nat := 118140960795 + 3689854 * 2 ^ 59
def prefixEnd_3689854 : Nat := 4983230072969 + 3 ^ 40 * 3689854 * 2
def baseEnd_3689854 : Nat := 631556215638370554318559

theorem tailTrace_3689854 : CollatzResearch.WordTrace tailWord_3689854 prefixEnd_3689854 631556215638370554318559 := by
  unfold tailWord_3689854
  simp only [CollatzResearch.WordTrace]
  refine ⟨16822503946787076217170577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89720021049531073158243077 16822503946787076217170577)
  ·
    refine ⟨12616877960090307162877933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16822503946787076217170577 12616877960090307162877933)
    ·
      refine ⟨4731329235033865186079225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12616877960090307162877933 4731329235033865186079225)
      ·
        refine ⟨3548496926275398889559419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4731329235033865186079225 3548496926275398889559419)
        ·
          refine ⟨5322745389413098334339129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3548496926275398889559419 5322745389413098334339129)
          ·
            refine ⟨3992059042059823750754347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5322745389413098334339129 3992059042059823750754347)
            ·
              refine ⟨5988088563089735626131521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3992059042059823750754347 5988088563089735626131521)
              ·
                refine ⟨4491066422317301719598641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5988088563089735626131521 4491066422317301719598641)
                ·
                  refine ⟨3368299816737976289698981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4491066422317301719598641 3368299816737976289698981)
                  ·
                    refine ⟨631556215638370554318559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3368299816737976289698981 631556215638370554318559)
                    ·
                      rfl

theorem cell23_3689854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_3689854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3689854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3689854 prefixEnd_3689854 := by exact prefixLift 3689854
  have htrace : WordTrace (prefixWord ++ tailWord_3689854) baseStart_3689854 baseEnd_3689854 := by
    simpa [prefixWord, tailWord_3689854, baseEnd_3689854] using wordTrace_append hprefix tailTrace_3689854
  have hstable : (prefixWord ++ tailWord_3689854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689854).length < 2 ^ (prefixWord ++ tailWord_3689854).sum := by decide
  have hdescent : baseEnd_3689854 < baseStart_3689854 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689860 : List Nat := [2, 3, 2, 1, 1, 3, 3, 2, 2, 1, 3]
def baseStart_3689860 : Nat := 118140960795 + 3689860 * 2 ^ 59
def prefixEnd_3689860 : Nat := 4983230072969 + 3 ^ 40 * 3689860 * 2
def baseEnd_3689860 : Nat := 1894671727799038639480649

theorem tailTrace_3689860 : CollatzResearch.WordTrace tailWord_3689860 prefixEnd_3689860 1894671727799038639480649 := by
  unfold tailWord_3689860
  simp only [CollatzResearch.WordTrace]
  refine ⟨67290125206137436381041517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89720166941516581841388689 67290125206137436381041517)
  ·
    refine ⟨25233796952301538642890569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67290125206137436381041517 25233796952301538642890569)
    ·
      refine ⟨18925347714226153982167927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25233796952301538642890569 18925347714226153982167927)
      ·
        refine ⟨28388021571339230973251891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18925347714226153982167927 28388021571339230973251891)
        ·
          refine ⟨42582032357008846459877837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28388021571339230973251891 42582032357008846459877837)
          ·
            refine ⟨15968262133878317422454189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42582032357008846459877837 15968262133878317422454189)
            ·
              refine ⟨5988098300204369033420321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15968262133878317422454189 5988098300204369033420321)
              ·
                refine ⟨4491073725153276775065241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5988098300204369033420321 4491073725153276775065241)
                ·
                  refine ⟨3368305293864957581298931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4491073725153276775065241 3368305293864957581298931)
                  ·
                    refine ⟨5052457940797436371948397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3368305293864957581298931 5052457940797436371948397)
                    ·
                      refine ⟨1894671727799038639480649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5052457940797436371948397 1894671727799038639480649)
                      ·
                        rfl

theorem cell23_3689860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 2, 2, 1, 3].length) (baseStart_3689860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3689860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3689860 prefixEnd_3689860 := by exact prefixLift 3689860
  have htrace : WordTrace (prefixWord ++ tailWord_3689860) baseStart_3689860 baseEnd_3689860 := by
    simpa [prefixWord, tailWord_3689860, baseEnd_3689860] using wordTrace_append hprefix tailTrace_3689860
  have hstable : (prefixWord ++ tailWord_3689860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689860).length < 2 ^ (prefixWord ++ tailWord_3689860).sum := by decide
  have hdescent : baseEnd_3689860 < baseStart_3689860 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689953 : List Nat := [1, 2, 3, 1, 2, 4, 2, 1, 2, 5]
def baseStart_3689953 : Nat := 118140960795 + 3689953 * 2 ^ 59
def prefixEnd_3689953 : Nat := 4983230072969 + 3 ^ 40 * 3689953 * 2
def baseEnd_3689953 : Nat := 631573160499968925205907

theorem tailTrace_3689953 : CollatzResearch.WordTrace tailWord_3689953 prefixEnd_3689953 631573160499968925205907 := by
  unfold tailWord_3689953
  simp only [CollatzResearch.WordTrace]
  refine ⟨134583642400937949645218513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89722428267291966430145675 134583642400937949645218513)
  ·
    refine ⟨100937731800703462233913885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134583642400937949645218513 100937731800703462233913885)
    ·
      refine ⟨37851649425263798337717707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100937731800703462233913885 37851649425263798337717707)
      ·
        refine ⟨56777474137895697506576561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37851649425263798337717707 56777474137895697506576561)
        ·
          refine ⟨42583105603421773129932421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56777474137895697506576561 42583105603421773129932421)
          ·
            refine ⟨7984332300641582461862329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42583105603421773129932421 7984332300641582461862329)
            ·
              refine ⟨5988249225481186846396747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7984332300641582461862329 5988249225481186846396747)
              ·
                refine ⟨8982373838221780269595121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5988249225481186846396747 8982373838221780269595121)
                ·
                  refine ⟨6736780378666335202196341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8982373838221780269595121 6736780378666335202196341)
                  ·
                    refine ⟨631573160499968925205907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6736780378666335202196341 631573160499968925205907)
                    ·
                      rfl

theorem cell23_3689953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 1, 2, 5].length) (baseStart_3689953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3689953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3689953 prefixEnd_3689953 := by exact prefixLift 3689953
  have htrace : WordTrace (prefixWord ++ tailWord_3689953) baseStart_3689953 baseEnd_3689953 := by
    simpa [prefixWord, tailWord_3689953, baseEnd_3689953] using wordTrace_append hprefix tailTrace_3689953
  have hstable : (prefixWord ++ tailWord_3689953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689953).length < 2 ^ (prefixWord ++ tailWord_3689953).sum := by decide
  have hdescent : baseEnd_3689953 < baseStart_3689953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689956 : List Nat := [2, 3, 1, 1, 1, 1, 1, 5, 1, 3, 4]
def baseStart_3689956 : Nat := 118140960795 + 3689956 * 2 ^ 59
def prefixEnd_3689956 : Nat := 4983230072969 + 3 ^ 40 * 3689956 * 2
def baseEnd_3689956 : Nat := 1894721021941870263880207

theorem tailTrace_3689956 : CollatzResearch.WordTrace tailWord_3689956 prefixEnd_3689956 1894721021941870263880207 := by
  unfold tailWord_3689956
  simp only [CollatzResearch.WordTrace]
  refine ⟨67291875909963540578788861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89722501213284720771718481 67291875909963540578788861)
  ·
    refine ⟨25234453466236327717045823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67291875909963540578788861 25234453466236327717045823)
    ·
      refine ⟨37851680199354491575568735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25234453466236327717045823 37851680199354491575568735)
      ·
        refine ⟨56777520299031737363353103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37851680199354491575568735 56777520299031737363353103)
        ·
          refine ⟨85166280448547606045029655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56777520299031737363353103 85166280448547606045029655)
          ·
            refine ⟨127749420672821409067544483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85166280448547606045029655 127749420672821409067544483)
            ·
              refine ⟨191624131009232113601316725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127749420672821409067544483 191624131009232113601316725)
              ·
                refine ⟨17964762282115510650123443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 191624131009232113601316725 17964762282115510650123443)
                ·
                  refine ⟨26947143423173265975185165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17964762282115510650123443 26947143423173265975185165)
                  ·
                    refine ⟨10105178783689974740694437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26947143423173265975185165 10105178783689974740694437)
                    ·
                      refine ⟨1894721021941870263880207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10105178783689974740694437 1894721021941870263880207)
                      ·
                        rfl

theorem cell23_3689956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5, 1, 3, 4].length) (baseStart_3689956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3689956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3689956 prefixEnd_3689956 := by exact prefixLift 3689956
  have htrace : WordTrace (prefixWord ++ tailWord_3689956) baseStart_3689956 baseEnd_3689956 := by
    simpa [prefixWord, tailWord_3689956, baseEnd_3689956] using wordTrace_append hprefix tailTrace_3689956
  have hstable : (prefixWord ++ tailWord_3689956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689956).length < 2 ^ (prefixWord ++ tailWord_3689956).sum := by decide
  have hdescent : baseEnd_3689956 < baseStart_3689956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690004 : List Nat := [2, 4, 3, 1, 3, 1, 1, 1, 2, 5]
def baseStart_3690004 : Nat := 118140960795 + 3690004 * 2 ^ 59
def prefixEnd_3690004 : Nat := 4983230072969 + 3 ^ 40 * 3690004 * 2
def baseEnd_3690004 : Nat := 631581889671095358693329

theorem tailTrace_3690004 : CollatzResearch.WordTrace tailWord_3690004 prefixEnd_3690004 631581889671095358693329 := by
  unfold tailWord_3690004
  simp only [CollatzResearch.WordTrace]
  refine ⟨67292751261876592677662533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89723668349168790236883377 67292751261876592677662533)
  ·
    refine ⟨12617390861601861127061725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67292751261876592677662533 12617390861601861127061725)
    ·
      refine ⟨4731521573100697922648147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12617390861601861127061725 4731521573100697922648147)
      ·
        refine ⟨7097282359651046883972221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4731521573100697922648147 7097282359651046883972221)
        ·
          refine ⟨2661480884869142581489583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7097282359651046883972221 2661480884869142581489583)
          ·
            refine ⟨3992221327303713872234375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2661480884869142581489583 3992221327303713872234375)
            ·
              refine ⟨5988331990955570808351563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3992221327303713872234375 5988331990955570808351563)
              ·
                refine ⟨8982497986433356212527345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5988331990955570808351563 8982497986433356212527345)
                ·
                  refine ⟨6736873489825017159395509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8982497986433356212527345 6736873489825017159395509)
                  ·
                    refine ⟨631581889671095358693329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6736873489825017159395509 631581889671095358693329)
                    ·
                      rfl

theorem cell23_3690004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_3690004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3690004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3690004 prefixEnd_3690004 := by exact prefixLift 3690004
  have htrace : WordTrace (prefixWord ++ tailWord_3690004) baseStart_3690004 baseEnd_3690004 := by
    simpa [prefixWord, tailWord_3690004, baseEnd_3690004] using wordTrace_append hprefix tailTrace_3690004
  have hstable : (prefixWord ++ tailWord_3690004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690004).length < 2 ^ (prefixWord ++ tailWord_3690004).sum := by decide
  have hdescent : baseEnd_3690004 < baseStart_3690004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690017 : List Nat := [1, 2, 3, 2, 2, 3, 2, 3, 1, 4]
def baseStart_3690017 : Nat := 118140960795 + 3690017 * 2 ^ 59
def prefixEnd_3690017 : Nat := 4983230072969 + 3 ^ 40 * 3690017 * 2
def baseEnd_3690017 : Nat := 631584114753931508405809

theorem tailTrace_3690017 : CollatzResearch.WordTrace tailWord_3690017 prefixEnd_3690017 631584114753931508405809 := by
  unfold tailWord_3690017
  simp only [CollatzResearch.WordTrace]
  refine ⟨134585976672706088575548305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89723984448470725717032203 134585976672706088575548305)
  ·
    refine ⟨100939482504529566431661229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134585976672706088575548305 100939482504529566431661229)
    ·
      refine ⟨37852305939198587411872961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100939482504529566431661229 37852305939198587411872961)
      ·
        refine ⟨28389229454398940558904721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37852305939198587411872961 28389229454398940558904721)
        ·
          refine ⟨21291922090799205419178541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28389229454398940558904721 21291922090799205419178541)
          ·
            refine ⟨7984470784049702032191953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21291922090799205419178541 7984470784049702032191953)
            ·
              refine ⟨5988353088037276524143965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7984470784049702032191953 5988353088037276524143965)
              ·
                refine ⟨2245632408013978696553987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5988353088037276524143965 2245632408013978696553987)
                ·
                  refine ⟨3368448612020968044830981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2245632408013978696553987 3368448612020968044830981)
                  ·
                    refine ⟨631584114753931508405809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3368448612020968044830981 631584114753931508405809)
                    ·
                      rfl

theorem cell23_3690017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 3, 1, 4].length) (baseStart_3690017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3690017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3690017 prefixEnd_3690017 := by exact prefixLift 3690017
  have htrace : WordTrace (prefixWord ++ tailWord_3690017) baseStart_3690017 baseEnd_3690017 := by
    simpa [prefixWord, tailWord_3690017, baseEnd_3690017] using wordTrace_append hprefix tailTrace_3690017
  have hstable : (prefixWord ++ tailWord_3690017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690017).length < 2 ^ (prefixWord ++ tailWord_3690017).sum := by decide
  have hdescent : baseEnd_3690017 < baseStart_3690017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690030 : List Nat := [4, 1, 3, 1, 2, 1, 3, 2, 6]
def baseStart_3690030 : Nat := 118140960795 + 3690030 * 2 ^ 59
def prefixEnd_3690030 : Nat := 4983230072969 + 3 ^ 40 * 3690030 * 2
def baseEnd_3690030 : Nat := 210528779945589219372763

theorem tailTrace_3690030 : CollatzResearch.WordTrace tailWord_3690030 prefixEnd_3690030 210528779945589219372763 := by
  unfold tailWord_3690030
  simp only [CollatzResearch.WordTrace]
  refine ⟨16823306352707373974471443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89724300547772661197181029 16823306352707373974471443)
  ·
    refine ⟨25234959529061060961707165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16823306352707373974471443 25234959529061060961707165)
    ·
      refine ⟨9463109823397897860640187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25234959529061060961707165 9463109823397897860640187)
      ·
        refine ⟨14194664735096846790960281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9463109823397897860640187 14194664735096846790960281)
        ·
          refine ⟨10645998551322635093220211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14194664735096846790960281 10645998551322635093220211)
          ·
            refine ⟨15968997826983952639830317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10645998551322635093220211 15968997826983952639830317)
            ·
              refine ⟨5988374185118982239936369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15968997826983952639830317 5988374185118982239936369)
              ·
                refine ⟨4491280638839236679952277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5988374185118982239936369 4491280638839236679952277)
                ·
                  refine ⟨210528779945589219372763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4491280638839236679952277 210528779945589219372763)
                  ·
                    rfl

theorem cell23_3690030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 2, 6].length) (baseStart_3690030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3690030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3690030 prefixEnd_3690030 := by exact prefixLift 3690030
  have htrace : WordTrace (prefixWord ++ tailWord_3690030) baseStart_3690030 baseEnd_3690030 := by
    simpa [prefixWord, tailWord_3690030, baseEnd_3690030] using wordTrace_append hprefix tailTrace_3690030
  have hstable : (prefixWord ++ tailWord_3690030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690030).length < 2 ^ (prefixWord ++ tailWord_3690030).sum := by decide
  have hdescent : baseEnd_3690030 < baseStart_3690030 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690040 : List Nat := [2, 1, 2, 1, 4, 2, 1, 3, 3, 1, 3]
def baseStart_3690040 : Nat := 118140960795 + 3690040 * 2 ^ 59
def prefixEnd_3690040 : Nat := 4983230072969 + 3 ^ 40 * 3690040 * 2
def baseEnd_3690040 : Nat := 1894764154316847935229821

theorem tailTrace_3690040 : CollatzResearch.WordTrace tailWord_3690040 prefixEnd_3690040 1894764154316847935229821 := by
  unfold tailWord_3690040
  simp only [CollatzResearch.WordTrace]
  refine ⟨67293407775811381751817787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89724543701081842335757049 67293407775811381751817787)
  ·
    refine ⟨100940111663717072627726681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67293407775811381751817787 100940111663717072627726681)
    ·
      refine ⟨75705083747787804470795011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100940111663717072627726681 75705083747787804470795011)
      ·
        refine ⟨113557625621681706706192517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75705083747787804470795011 113557625621681706706192517)
        ·
          refine ⟨21292054804065320007411097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113557625621681706706192517 21292054804065320007411097)
          ·
            refine ⟨15969041103048990005558323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21292054804065320007411097 15969041103048990005558323)
            ·
              refine ⟨23953561654573485008337485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15969041103048990005558323 23953561654573485008337485)
              ·
                refine ⟨8982585620465056878126557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23953561654573485008337485 8982585620465056878126557)
                ·
                  refine ⟨3368469607674396329297459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8982585620465056878126557 3368469607674396329297459)
                  ·
                    refine ⟨5052704411511594493946189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3368469607674396329297459 5052704411511594493946189)
                    ·
                      refine ⟨1894764154316847935229821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5052704411511594493946189 1894764154316847935229821)
                      ·
                        rfl

theorem cell23_3690040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 3, 3, 1, 3].length) (baseStart_3690040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3690040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3690040 prefixEnd_3690040 := by exact prefixLift 3690040
  have htrace : WordTrace (prefixWord ++ tailWord_3690040) baseStart_3690040 baseEnd_3690040 := by
    simpa [prefixWord, tailWord_3690040, baseEnd_3690040] using wordTrace_append hprefix tailTrace_3690040
  have hstable : (prefixWord ++ tailWord_3690040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690040).length < 2 ^ (prefixWord ++ tailWord_3690040).sum := by decide
  have hdescent : baseEnd_3690040 < baseStart_3690040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690060 : List Nat := [2, 2, 1, 3, 1, 4, 2, 2, 1, 5]
def baseStart_3690060 : Nat := 118140960795 + 3690060 * 2 ^ 59
def prefixEnd_3690060 : Nat := 4983230072969 + 3 ^ 40 * 3690060 * 2
def baseEnd_3690060 : Nat := 631591474643312618993243

theorem tailTrace_3690060 : CollatzResearch.WordTrace tailWord_3690060 prefixEnd_3690060 631591474643312618993243 := by
  unfold tailWord_3690060
  simp only [CollatzResearch.WordTrace]
  refine ⟨67293772505775153459681817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89725030007700204612909089 67293772505775153459681817)
  ·
    refine ⟨50470329379331365094761363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67293772505775153459681817 50470329379331365094761363)
    ·
      refine ⟨75705494068997047642142045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50470329379331365094761363 75705494068997047642142045)
      ·
        refine ⟨28389560275873892865803267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75705494068997047642142045 28389560275873892865803267)
        ·
          refine ⟨42584340413810839298704901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28389560275873892865803267 42584340413810839298704901)
          ·
            refine ⟨7984563827589532368507169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42584340413810839298704901 7984563827589532368507169)
            ·
              refine ⟨5988422870692149276380377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7984563827589532368507169 5988422870692149276380377)
              ·
                refine ⟨4491317153019111957285283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5988422870692149276380377 4491317153019111957285283)
                ·
                  refine ⟨6736975729528667935927925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4491317153019111957285283 6736975729528667935927925)
                  ·
                    refine ⟨631591474643312618993243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6736975729528667935927925 631591474643312618993243)
                    ·
                      rfl

theorem cell23_3690060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 2, 1, 5].length) (baseStart_3690060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3690060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3690060 prefixEnd_3690060 := by exact prefixLift 3690060
  have htrace : WordTrace (prefixWord ++ tailWord_3690060) baseStart_3690060 baseEnd_3690060 := by
    simpa [prefixWord, tailWord_3690060, baseEnd_3690060] using wordTrace_append hprefix tailTrace_3690060
  have hstable : (prefixWord ++ tailWord_3690060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690060).length < 2 ^ (prefixWord ++ tailWord_3690060).sum := by decide
  have hdescent : baseEnd_3690060 < baseStart_3690060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690063 : List Nat := [1, 1, 2, 1, 1, 2, 3, 1, 1, 8, 2]
def baseStart_3690063 : Nat := 118140960795 + 3690063 * 2 ^ 59
def prefixEnd_3690063 : Nat := 4983230072969 + 3 ^ 40 * 3690063 * 2
def baseEnd_3690063 : Nat := 1894775964371901345242215

theorem tailTrace_3690063 : CollatzResearch.WordTrace tailWord_3690063 prefixEnd_3690063 1894775964371901345242215 := by
  unfold tailWord_3690063
  simp only [CollatzResearch.WordTrace]
  refine ⟨134587654430539438431722843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89725102953692958954481895 134587654430539438431722843)
  ·
    refine ⟨201881481645809157647584265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134587654430539438431722843 201881481645809157647584265)
    ·
      refine ⟨151411111234356868235688199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201881481645809157647584265 151411111234356868235688199)
      ·
        refine ⟨227116666851535302353532299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151411111234356868235688199 227116666851535302353532299)
        ·
          refine ⟨340675000277302953530298449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227116666851535302353532299 340675000277302953530298449)
          ·
            refine ⟨255506250207977215147723837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 340675000277302953530298449 255506250207977215147723837)
            ·
              refine ⟨95814843827991455680396439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 255506250207977215147723837 95814843827991455680396439)
              ·
                refine ⟨143722265741987183520594659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95814843827991455680396439 143722265741987183520594659)
                ·
                  refine ⟨215583398612980775280891989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143722265741987183520594659 215583398612980775280891989)
                  ·
                    refine ⟨2526367952495868460322953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 215583398612980775280891989 2526367952495868460322953)
                    ·
                      refine ⟨1894775964371901345242215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2526367952495868460322953 1894775964371901345242215)
                      ·
                        rfl

theorem cell23_3690063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 8, 2].length) (baseStart_3690063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3690063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3690063 prefixEnd_3690063 := by exact prefixLift 3690063
  have htrace : WordTrace (prefixWord ++ tailWord_3690063) baseStart_3690063 baseEnd_3690063 := by
    simpa [prefixWord, tailWord_3690063, baseEnd_3690063] using wordTrace_append hprefix tailTrace_3690063
  have hstable : (prefixWord ++ tailWord_3690063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690063).length < 2 ^ (prefixWord ++ tailWord_3690063).sum := by decide
  have hdescent : baseEnd_3690063 < baseStart_3690063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690083 : List Nat := [1, 1, 1, 5, 1, 3, 1, 3, 1, 1, 5]
def baseStart_3690083 : Nat := 118140960795 + 3690083 * 2 ^ 59
def prefixEnd_3690083 : Nat := 4983230072969 + 3 ^ 40 * 3690083 * 2
def baseEnd_3690083 : Nat := 1894786233984991266992123

theorem tailTrace_3690083 : CollatzResearch.WordTrace tailWord_3690083 prefixEnd_3690083 1894786233984991266992123 := by
  unfold tailWord_3690083
  simp only [CollatzResearch.WordTrace]
  refine ⟨134588383890466981847450903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89725589260311321231633935 134588383890466981847450903)
  ·
    refine ⟨201882575835700472771176355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134588383890466981847450903 201882575835700472771176355)
    ·
      refine ⟨302823863753550709156764533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201882575835700472771176355 302823863753550709156764533)
      ·
        refine ⟨28389737226895378983446675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 302823863753550709156764533 28389737226895378983446675)
        ·
          refine ⟨42584605840343068475170013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28389737226895378983446675 42584605840343068475170013)
          ·
            refine ⟨15969227190128650678188755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42584605840343068475170013 15969227190128650678188755)
            ·
              refine ⟨23953840785192976017283133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15969227190128650678188755 23953840785192976017283133)
              ·
                refine ⟨8982690294447366006481175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23953840785192976017283133 8982690294447366006481175)
                ·
                  refine ⟨13474035441671049009721763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8982690294447366006481175 13474035441671049009721763)
                  ·
                    refine ⟨20211053162506573514582645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13474035441671049009721763 20211053162506573514582645)
                    ·
                      refine ⟨1894786233984991266992123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20211053162506573514582645 1894786233984991266992123)
                      ·
                        rfl

theorem cell23_3690083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_3690083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3690083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3690083 prefixEnd_3690083 := by exact prefixLift 3690083
  have htrace : WordTrace (prefixWord ++ tailWord_3690083) baseStart_3690083 baseEnd_3690083 := by
    simpa [prefixWord, tailWord_3690083, baseEnd_3690083] using wordTrace_append hprefix tailTrace_3690083
  have hstable : (prefixWord ++ tailWord_3690083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690083).length < 2 ^ (prefixWord ++ tailWord_3690083).sum := by decide
  have hdescent : baseEnd_3690083 < baseStart_3690083 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690090 : List Nat := [3, 1, 3, 2, 1, 2, 2, 1, 4, 4]
def baseStart_3690090 : Nat := 118140960795 + 3690090 * 2 ^ 59
def prefixEnd_3690090 : Nat := 4983230072969 + 3 ^ 40 * 3690090 * 2
def baseEnd_3690090 : Nat := 631596609449857579868197

theorem tailTrace_3690090 : CollatzResearch.WordTrace tailWord_3690090 prefixEnd_3690090 631596609449857579868197 := by
  unfold tailWord_3690090
  simp only [CollatzResearch.WordTrace]
  refine ⟨33647159800360405510738931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89725759467627748028637149 33647159800360405510738931)
  ·
    refine ⟨50470739700540608266108397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33647159800360405510738931 50470739700540608266108397)
    ·
      refine ⟨18926527387702728099790649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50470739700540608266108397 18926527387702728099790649)
      ·
        refine ⟨14194895540777046074842987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18926527387702728099790649 14194895540777046074842987)
        ·
          refine ⟨21292343311165569112264481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14194895540777046074842987 21292343311165569112264481)
          ·
            refine ⟨15969257483374176834198361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21292343311165569112264481 15969257483374176834198361)
            ·
              refine ⟨11976943112530632625648771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15969257483374176834198361 11976943112530632625648771)
              ·
                refine ⟨17965414668795948938473157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11976943112530632625648771 17965414668795948938473157)
                ·
                  refine ⟨3368515250399240425963717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17965414668795948938473157 3368515250399240425963717)
                  ·
                    refine ⟨631596609449857579868197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3368515250399240425963717 631596609449857579868197)
                    ·
                      rfl

theorem cell23_3690090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 1, 4, 4].length) (baseStart_3690090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3690090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3690090 prefixEnd_3690090 := by exact prefixLift 3690090
  have htrace : WordTrace (prefixWord ++ tailWord_3690090) baseStart_3690090 baseEnd_3690090 := by
    simpa [prefixWord, tailWord_3690090, baseEnd_3690090] using wordTrace_append hprefix tailTrace_3690090
  have hstable : (prefixWord ++ tailWord_3690090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690090).length < 2 ^ (prefixWord ++ tailWord_3690090).sum := by decide
  have hdescent : baseEnd_3690090 < baseStart_3690090 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690147 : List Nat := [1, 1, 1, 4, 1, 1, 6, 2, 2, 1, 3]
def baseStart_3690147 : Nat := 118140960795 + 3690147 * 2 ^ 59
def prefixEnd_3690147 : Nat := 4983230072969 + 3 ^ 40 * 3690147 * 2
def baseEnd_3690147 : Nat := 1894819096746879016591829

theorem tailTrace_3690147 : CollatzResearch.WordTrace tailWord_3690147 prefixEnd_3690147 1894819096746879016591829 := by
  unfold tailWord_3690147
  simp only [CollatzResearch.WordTrace]
  refine ⟨134590718162235120777780695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89727145441490080518520463 134590718162235120777780695)
  ·
    refine ⟨201886077243352681166671043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134590718162235120777780695 201886077243352681166671043)
    ·
      refine ⟨302829115865029021750006565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201886077243352681166671043 302829115865029021750006565)
      ·
        refine ⟨56780459224692941578126231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 302829115865029021750006565 56780459224692941578126231)
        ·
          refine ⟨85170688837039412367189347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56780459224692941578126231 85170688837039412367189347)
          ·
            refine ⟨127756033255559118550784021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85170688837039412367189347 127756033255559118550784021)
            ·
              refine ⟨5988564058854333682068001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 127756033255559118550784021 5988564058854333682068001)
              ·
                refine ⟨4491423044140750261551001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5988564058854333682068001 4491423044140750261551001)
                ·
                  refine ⟨3368567283105562696163251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4491423044140750261551001 3368567283105562696163251)
                  ·
                    refine ⟨5052850924658344044244877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3368567283105562696163251 5052850924658344044244877)
                    ·
                      refine ⟨1894819096746879016591829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5052850924658344044244877 1894819096746879016591829)
                      ·
                        rfl

theorem cell23_3690147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 2, 2, 1, 3].length) (baseStart_3690147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3690147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3690147 prefixEnd_3690147 := by exact prefixLift 3690147
  have htrace : WordTrace (prefixWord ++ tailWord_3690147) baseStart_3690147 baseEnd_3690147 := by
    simpa [prefixWord, tailWord_3690147, baseEnd_3690147] using wordTrace_append hprefix tailTrace_3690147
  have hstable : (prefixWord ++ tailWord_3690147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690147).length < 2 ^ (prefixWord ++ tailWord_3690147).sum := by decide
  have hdescent : baseEnd_3690147 < baseStart_3690147 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690148 : List Nat := [2, 3, 1, 2, 2, 4, 2, 2, 1, 2, 2]
def baseStart_3690148 : Nat := 118140960795 + 3690148 * 2 ^ 59
def prefixEnd_3690148 : Nat := 4983230072969 + 3 ^ 40 * 3690148 * 2
def baseEnd_3690148 : Nat := 1894819610227533512679325

theorem tailTrace_3690148 : CollatzResearch.WordTrace tailWord_3690148 prefixEnd_3690148 1894819610227533512679325 := by
  unfold tailWord_3690148
  simp only [CollatzResearch.WordTrace]
  refine ⟨67295377317615748974283549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89727169756820998632378065 67295377317615748974283549)
  ·
    refine ⟨25235766494105905865356331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67295377317615748974283549 25235766494105905865356331)
    ·
      refine ⟨37853649741158858798034497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25235766494105905865356331 37853649741158858798034497)
      ·
        refine ⟨28390237305869144098525873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37853649741158858798034497 28390237305869144098525873)
        ·
          refine ⟨21292677979401858073894405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28390237305869144098525873 21292677979401858073894405)
          ·
            refine ⟨3992377121137848388855201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21292677979401858073894405 3992377121137848388855201)
            ·
              refine ⟨2994282840853386291641401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3992377121137848388855201 2994282840853386291641401)
              ·
                refine ⟨2245712130640039718731051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2994282840853386291641401 2245712130640039718731051)
                ·
                  refine ⟨3368568195960059578096577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2245712130640039718731051 3368568195960059578096577)
                  ·
                    refine ⟨2526426146970044683572433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3368568195960059578096577 2526426146970044683572433)
                    ·
                      refine ⟨1894819610227533512679325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2526426146970044683572433 1894819610227533512679325)
                      ·
                        rfl

theorem cell23_3690148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 2, 2, 1, 2, 2].length) (baseStart_3690148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3690148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3690148 prefixEnd_3690148 := by exact prefixLift 3690148
  have htrace : WordTrace (prefixWord ++ tailWord_3690148) baseStart_3690148 baseEnd_3690148 := by
    simpa [prefixWord, tailWord_3690148, baseEnd_3690148] using wordTrace_append hprefix tailTrace_3690148
  have hstable : (prefixWord ++ tailWord_3690148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690148).length < 2 ^ (prefixWord ++ tailWord_3690148).sum := by decide
  have hdescent : baseEnd_3690148 < baseStart_3690148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690157 : List Nat := [1, 5, 2, 1, 1, 1, 1, 1, 5, 3, 2]
def baseStart_3690157 : Nat := 118140960795 + 3690157 * 2 ^ 59
def prefixEnd_3690157 : Nat := 4983230072969 + 3 ^ 40 * 3690157 * 2
def baseEnd_3690157 : Nat := 1894824231553423977466783

theorem tailTrace_3690157 : CollatzResearch.WordTrace tailWord_3690157 prefixEnd_3690157 1894824231553423977466783 := by
  unfold tailWord_3690157
  simp only [CollatzResearch.WordTrace]
  refine ⟨134591082892198892485644725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89727388594799261657096483 134591082892198892485644725)
  ·
    refine ⟨12617914021143646170529193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 134591082892198892485644725 12617914021143646170529193)
    ·
      refine ⟨9463435515857734627896895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12617914021143646170529193 9463435515857734627896895)
      ·
        refine ⟨14195153273786601941845343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9463435515857734627896895 14195153273786601941845343)
        ·
          refine ⟨21292729910679902912768015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14195153273786601941845343 21292729910679902912768015)
          ·
            refine ⟨31939094866019854369152023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21292729910679902912768015 31939094866019854369152023)
            ·
              refine ⟨47908642299029781553728035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31939094866019854369152023 47908642299029781553728035)
              ·
                refine ⟨71862963448544672330592053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47908642299029781553728035 71862963448544672330592053)
                ·
                  refine ⟨6737152823301063030993005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71862963448544672330592053 6737152823301063030993005)
                  ·
                    refine ⟨2526432308737898636622377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6737152823301063030993005 2526432308737898636622377)
                    ·
                      refine ⟨1894824231553423977466783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2526432308737898636622377 1894824231553423977466783)
                      ·
                        rfl

theorem cell23_3690157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 5, 3, 2].length) (baseStart_3690157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3690157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3690157 prefixEnd_3690157 := by exact prefixLift 3690157
  have htrace : WordTrace (prefixWord ++ tailWord_3690157) baseStart_3690157 baseEnd_3690157 := by
    simpa [prefixWord, tailWord_3690157, baseEnd_3690157] using wordTrace_append hprefix tailTrace_3690157
  have hstable : (prefixWord ++ tailWord_3690157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690157).length < 2 ^ (prefixWord ++ tailWord_3690157).sum := by decide
  have hdescent : baseEnd_3690157 < baseStart_3690157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690163 : List Nat := [1, 1, 1, 2, 3, 3, 3, 1, 2, 6]
def baseStart_3690163 : Nat := 118140960795 + 3690163 * 2 ^ 59
def prefixEnd_3690163 : Nat := 4983230072969 + 3 ^ 40 * 3690163 * 2
def baseEnd_3690163 : Nat := 631609104145783651330585

theorem tailTrace_3690163 : CollatzResearch.WordTrace tailWord_3690163 prefixEnd_3690163 631609104145783651330585 := by
  unfold tailWord_3690163
  simp only [CollatzResearch.WordTrace]
  refine ⟨134591301730177155510363143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89727534486784770340242095 134591301730177155510363143)
  ·
    refine ⟨201886952595265733265544715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134591301730177155510363143 201886952595265733265544715)
    ·
      refine ⟨302830428892898599898317073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201886952595265733265544715 302830428892898599898317073)
      ·
        refine ⟨227122821669673949923737805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302830428892898599898317073 227122821669673949923737805)
        ·
          refine ⟨85171058126127731221401677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227122821669673949923737805 85171058126127731221401677)
          ·
            refine ⟨31939146797297899208025629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85171058126127731221401677 31939146797297899208025629)
            ·
              refine ⟨11977180048986712203009611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31939146797297899208025629 11977180048986712203009611)
              ·
                refine ⟨17965770073480068304514417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11977180048986712203009611 17965770073480068304514417)
                ·
                  refine ⟨13474327555110051228385813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17965770073480068304514417 13474327555110051228385813)
                  ·
                    refine ⟨631609104145783651330585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13474327555110051228385813 631609104145783651330585)
                    ·
                      rfl

theorem cell23_3690163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 1, 2, 6].length) (baseStart_3690163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3690163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3690163 prefixEnd_3690163 := by exact prefixLift 3690163
  have htrace : WordTrace (prefixWord ++ tailWord_3690163) baseStart_3690163 baseEnd_3690163 := by
    simpa [prefixWord, tailWord_3690163, baseEnd_3690163] using wordTrace_append hprefix tailTrace_3690163
  have hstable : (prefixWord ++ tailWord_3690163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690163).length < 2 ^ (prefixWord ++ tailWord_3690163).sum := by decide
  have hdescent : baseEnd_3690163 < baseStart_3690163 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690183 : List Nat := [1, 1, 4, 1, 1, 1, 3, 2, 1, 4, 4]
def baseStart_3690183 : Nat := 118140960795 + 3690183 * 2 ^ 59
def prefixEnd_3690183 : Nat := 4983230072969 + 3 ^ 40 * 3690183 * 2
def baseEnd_3690183 : Nat := 1894837582050440875741663

theorem tailTrace_3690183 : CollatzResearch.WordTrace tailWord_3690183 prefixEnd_3690183 1894837582050440875741663 := by
  unfold tailWord_3690183
  simp only [CollatzResearch.WordTrace]
  refine ⟨134592031190104698926091203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89728020793403132617394135 134592031190104698926091203)
  ·
    refine ⟨201888046785157048389136805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134592031190104698926091203 201888046785157048389136805)
    ·
      refine ⟨37854008772216946572963151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 201888046785157048389136805 37854008772216946572963151)
      ·
        refine ⟨56781013158325419859444727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37854008772216946572963151 56781013158325419859444727)
        ·
          refine ⟨85171519737488129789167091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56781013158325419859444727 85171519737488129789167091)
          ·
            refine ⟨127757279606232194683750637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85171519737488129789167091 127757279606232194683750637)
            ·
              refine ⟨47908979852337073006406489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127757279606232194683750637 47908979852337073006406489)
              ·
                refine ⟨35931734889252804754804867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47908979852337073006406489 35931734889252804754804867)
                ·
                  refine ⟨53897602333879207132207301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35931734889252804754804867 53897602333879207132207301)
                  ·
                    refine ⟨10105800437602351337288869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53897602333879207132207301 10105800437602351337288869)
                    ·
                      refine ⟨1894837582050440875741663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10105800437602351337288869 1894837582050440875741663)
                      ·
                        rfl

theorem cell23_3690183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 4, 4].length) (baseStart_3690183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3690183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3690183 prefixEnd_3690183 := by exact prefixLift 3690183
  have htrace : WordTrace (prefixWord ++ tailWord_3690183) baseStart_3690183 baseEnd_3690183 := by
    simpa [prefixWord, tailWord_3690183, baseEnd_3690183] using wordTrace_append hprefix tailTrace_3690183
  have hstable : (prefixWord ++ tailWord_3690183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690183).length < 2 ^ (prefixWord ++ tailWord_3690183).sum := by decide
  have hdescent : baseEnd_3690183 < baseStart_3690183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690220 : List Nat := [2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 3]
def baseStart_3690220 : Nat := 118140960795 + 3690220 * 2 ^ 59
def prefixEnd_3690220 : Nat := 4983230072969 + 3 ^ 40 * 3690220 * 2
def baseEnd_3690220 : Nat := 1894856580834657230978993

theorem tailTrace_3690220 : CollatzResearch.WordTrace tailWord_3690220 prefixEnd_3690220 1894856580834657230978993 := by
  unfold tailWord_3690220
  simp only [CollatzResearch.WordTrace]
  refine ⟨67296690345485327122594057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89728920460647102830125409 67296690345485327122594057)
  ·
    refine ⟨50472517759113995341945543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67296690345485327122594057 50472517759113995341945543)
    ·
      refine ⟨75708776638670993012918315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50472517759113995341945543 75708776638670993012918315)
      ·
        refine ⟨113563164958006489519377473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75708776638670993012918315 113563164958006489519377473)
        ·
          refine ⟨85172373718504867139533105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113563164958006489519377473 85172373718504867139533105)
          ·
            refine ⟨63879280288878650354649829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85172373718504867139533105 63879280288878650354649829)
            ·
              refine ⟨11977365054164746941496843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63879280288878650354649829 11977365054164746941496843)
              ·
                refine ⟨17966047581247120412245265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11977365054164746941496843 17966047581247120412245265)
                ·
                  refine ⟨13474535685935340309183949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17966047581247120412245265 13474535685935340309183949)
                  ·
                    refine ⟨5052950882225752615943981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13474535685935340309183949 5052950882225752615943981)
                    ·
                      refine ⟨1894856580834657230978993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5052950882225752615943981 1894856580834657230978993)
                      ·
                        rfl

theorem cell23_3690220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 3].length) (baseStart_3690220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3690220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3690220 prefixEnd_3690220 := by exact prefixLift 3690220
  have htrace : WordTrace (prefixWord ++ tailWord_3690220) baseStart_3690220 baseEnd_3690220 := by
    simpa [prefixWord, tailWord_3690220, baseEnd_3690220] using wordTrace_append hprefix tailTrace_3690220
  have hstable : (prefixWord ++ tailWord_3690220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690220).length < 2 ^ (prefixWord ++ tailWord_3690220).sum := by decide
  have hdescent : baseEnd_3690220 < baseStart_3690220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690223 : List Nat := [1, 1, 2, 1, 5, 1, 1, 1, 3, 7]
def baseStart_3690223 : Nat := 118140960795 + 3690223 * 2 ^ 59
def prefixEnd_3690223 : Nat := 4983230072969 + 3 ^ 40 * 3690223 * 2
def baseEnd_3690223 : Nat := 631619373758873573080493

theorem tailTrace_3690223 : CollatzResearch.WordTrace tailWord_3690223 prefixEnd_3690223 631619373758873573080493 := by
  unfold tailWord_3690223
  simp only [CollatzResearch.WordTrace]
  refine ⟨134593490109959785757547323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89728993406639857171698215 134593490109959785757547323)
  ·
    refine ⟨201890235164939678636320985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134593490109959785757547323 201890235164939678636320985)
    ·
      refine ⟨151417676373704758977240739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201890235164939678636320985 151417676373704758977240739)
      ·
        refine ⟨227126514560557138465861109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151417676373704758977240739 227126514560557138465861109)
        ·
          refine ⟨21293110740052231731174479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 227126514560557138465861109 21293110740052231731174479)
          ·
            refine ⟨31939666110078347596761719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21293110740052231731174479 31939666110078347596761719)
            ·
              refine ⟨47909499165117521395142579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31939666110078347596761719 47909499165117521395142579)
              ·
                refine ⟨71864248747676282092713869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47909499165117521395142579 71864248747676282092713869)
                ·
                  refine ⟨26949093280378605784767701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71864248747676282092713869 26949093280378605784767701)
                  ·
                    refine ⟨631619373758873573080493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26949093280378605784767701 631619373758873573080493)
                    ·
                      rfl

theorem cell23_3690223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 3, 7].length) (baseStart_3690223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3690223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3690223 prefixEnd_3690223 := by exact prefixLift 3690223
  have htrace : WordTrace (prefixWord ++ tailWord_3690223) baseStart_3690223 baseEnd_3690223 := by
    simpa [prefixWord, tailWord_3690223, baseEnd_3690223] using wordTrace_append hprefix tailTrace_3690223
  have hstable : (prefixWord ++ tailWord_3690223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690223).length < 2 ^ (prefixWord ++ tailWord_3690223).sum := by decide
  have hdescent : baseEnd_3690223 < baseStart_3690223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690233 : List Nat := [1, 2, 1, 3, 1, 1, 1, 1, 5, 2, 5]
def baseStart_3690233 : Nat := 118140960795 + 3690233 * 2 ^ 59
def prefixEnd_3690233 : Nat := 4983230072969 + 3 ^ 40 * 3690233 * 2
def baseEnd_3690233 : Nat := 1894863256083165680116433

theorem tailTrace_3690233 : CollatzResearch.WordTrace tailWord_3690233 prefixEnd_3690233 1894863256083165680116433 := by
  unfold tailWord_3690233
  simp only [CollatzResearch.WordTrace]
  refine ⟨134593854839923557465411353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89729236559949038310274235 134593854839923557465411353)
  ·
    refine ⟨100945391129942668099058515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134593854839923557465411353 100945391129942668099058515)
    ·
      refine ⟨151418086694914002148587773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100945391129942668099058515 151418086694914002148587773)
      ·
        refine ⟨56781782510592750805720415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151418086694914002148587773 56781782510592750805720415)
        ·
          refine ⟨85172673765889126208580623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56781782510592750805720415 85172673765889126208580623)
          ·
            refine ⟨127759010648833689312870935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85172673765889126208580623 127759010648833689312870935)
            ·
              refine ⟨191638515973250533969306403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127759010648833689312870935 191638515973250533969306403)
              ·
                refine ⟨287457773959875800953959605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191638515973250533969306403 287457773959875800953959605)
                ·
                  refine ⟨26949166308738356339433713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 287457773959875800953959605 26949166308738356339433713)
                  ·
                    refine ⟨20211874731553767254575285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26949166308738356339433713 20211874731553767254575285)
                    ·
                      refine ⟨1894863256083165680116433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20211874731553767254575285 1894863256083165680116433)
                      ·
                        rfl

theorem cell23_3690233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5, 2, 5].length) (baseStart_3690233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3690233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3690233 prefixEnd_3690233 := by exact prefixLift 3690233
  have htrace : WordTrace (prefixWord ++ tailWord_3690233) baseStart_3690233 baseEnd_3690233 := by
    simpa [prefixWord, tailWord_3690233, baseEnd_3690233] using wordTrace_append hprefix tailTrace_3690233
  have hstable : (prefixWord ++ tailWord_3690233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690233).length < 2 ^ (prefixWord ++ tailWord_3690233).sum := by decide
  have hdescent : baseEnd_3690233 < baseStart_3690233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690244 : List Nat := [2, 3, 2, 2, 1, 4, 1, 3, 5]
def baseStart_3690244 : Nat := 118140960795 + 3690244 * 2 ^ 59
def prefixEnd_3690244 : Nat := 4983230072969 + 3 ^ 40 * 3690244 * 2
def baseEnd_3690244 : Nat := 210540989374485015230987

theorem tailTrace_3690244 : CollatzResearch.WordTrace tailWord_3690244 prefixEnd_3690244 210540989374485015230987 := by
  unfold tailWord_3690244
  simp only [CollatzResearch.WordTrace]
  refine ⟨67297128021441853172030893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89729504028589137562707857 67297128021441853172030893)
  ·
    refine ⟨25236423008040694939511585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67297128021441853172030893 25236423008040694939511585)
    ·
      refine ⟨18927317256030521204633689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25236423008040694939511585 18927317256030521204633689)
      ·
        refine ⟨14195487942022890903475267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18927317256030521204633689 14195487942022890903475267)
        ·
          refine ⟨21293231913034336355212901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14195487942022890903475267 21293231913034336355212901)
          ·
            refine ⟨3992480983693938066602419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21293231913034336355212901 3992480983693938066602419)
            ·
              refine ⟨5988721475540907099903629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3992480983693938066602419 5988721475540907099903629)
              ·
                refine ⟨2245770553327840162463861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5988721475540907099903629 2245770553327840162463861)
                ·
                  refine ⟨210540989374485015230987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2245770553327840162463861 210540989374485015230987)
                  ·
                    rfl

theorem cell23_3690244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 3, 5].length) (baseStart_3690244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3690244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3690244 prefixEnd_3690244 := by exact prefixLift 3690244
  have htrace : WordTrace (prefixWord ++ tailWord_3690244) baseStart_3690244 baseEnd_3690244 := by
    simpa [prefixWord, tailWord_3690244, baseEnd_3690244] using wordTrace_append hprefix tailTrace_3690244
  have hstable : (prefixWord ++ tailWord_3690244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690244).length < 2 ^ (prefixWord ++ tailWord_3690244).sum := by decide
  have hdescent : baseEnd_3690244 < baseStart_3690244 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
