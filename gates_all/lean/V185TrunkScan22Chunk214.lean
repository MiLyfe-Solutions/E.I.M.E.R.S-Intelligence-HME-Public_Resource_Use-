import V185TrunkScan22Chunk213

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1908688 : List Nat := [2, 1, 1, 1, 1, 2, 7, 2, 5]
def baseStart_1908688 : Nat := 118140960795 + 1908688 * 2 ^ 59
def prefixEnd_1908688 : Nat := 4983230072969 + 3 ^ 40 * 1908688 * 2
def baseEnd_1908688 : Nat := 217794302993096329582691

theorem tailTrace_1908688 : CollatzResearch.WordTrace tailWord_1908688 prefixEnd_1908688 217794302993096329582691 := by
  unfold tailWord_1908688
  simp only [CollatzResearch.WordTrace]
  refine ⟨34807785254578414401539359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46410380339437885868719145 34807785254578414401539359)
  ·
    refine ⟨52211677881867621602309039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34807785254578414401539359 52211677881867621602309039)
    ·
      refine ⟨78317516822801432403463559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52211677881867621602309039 78317516822801432403463559)
      ·
        refine ⟨117476275234202148605195339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78317516822801432403463559 117476275234202148605195339)
        ·
          refine ⟨176214412851303222907793009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117476275234202148605195339 176214412851303222907793009)
          ·
            refine ⟨132160809638477417180844757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176214412851303222907793009 132160809638477417180844757)
            ·
              refine ⟨3097518975901814465176049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 132160809638477417180844757 3097518975901814465176049)
              ·
                refine ⟨2323139231926360848882037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3097518975901814465176049 2323139231926360848882037)
                ·
                  refine ⟨217794302993096329582691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2323139231926360848882037 217794302993096329582691)
                  ·
                    rfl

theorem cell22_1908688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 2, 5].length) (baseStart_1908688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1908688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1908688 prefixEnd_1908688 := by exact prefixLift 1908688
  have htrace : WordTrace (prefixWord ++ tailWord_1908688) baseStart_1908688 baseEnd_1908688 := by
    simpa [prefixWord, tailWord_1908688, baseEnd_1908688] using wordTrace_append hprefix tailTrace_1908688
  have hstable : (prefixWord ++ tailWord_1908688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908688).length < 2 ^ (prefixWord ++ tailWord_1908688).sum := by decide
  have hdescent : baseEnd_1908688 < baseStart_1908688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908692 : List Nat := [2, 4, 1, 2, 1, 1, 1, 6, 1, 3]
def baseStart_1908692 : Nat := 118140960795 + 1908692 * 2 ^ 59
def prefixEnd_1908692 : Nat := 4983230072969 + 3 ^ 40 * 1908692 * 2
def baseEnd_1908692 : Nat := 653384278261034311648061

theorem tailTrace_1908692 : CollatzResearch.WordTrace tailWord_1908692 prefixEnd_1908692 653384278261034311648061 := by
  unfold tailWord_1908692
  simp only [CollatzResearch.WordTrace]
  refine ⟨34807858200571168743112165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46410477600761558324149553 34807858200571168743112165)
  ·
    refine ⟨6526473412607094139333531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34807858200571168743112165 6526473412607094139333531)
    ·
      refine ⟨9789710118910641209000297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6526473412607094139333531 9789710118910641209000297)
      ·
        refine ⟨7342282589182980906750223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9789710118910641209000297 7342282589182980906750223)
        ·
          refine ⟨11013423883774471360125335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7342282589182980906750223 11013423883774471360125335)
          ·
            refine ⟨16520135825661707040188003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11013423883774471360125335 16520135825661707040188003)
            ·
              refine ⟨24780203738492560560282005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16520135825661707040188003 24780203738492560560282005)
              ·
                refine ⟨1161572050241838776263219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24780203738492560560282005 1161572050241838776263219)
                ·
                  refine ⟨1742358075362758164394829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1161572050241838776263219 1742358075362758164394829)
                  ·
                    refine ⟨653384278261034311648061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1742358075362758164394829 653384278261034311648061)
                    ·
                      rfl

theorem cell22_1908692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 6, 1, 3].length) (baseStart_1908692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1908692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1908692 prefixEnd_1908692 := by exact prefixLift 1908692
  have htrace : WordTrace (prefixWord ++ tailWord_1908692) baseStart_1908692 baseEnd_1908692 := by
    simpa [prefixWord, tailWord_1908692, baseEnd_1908692] using wordTrace_append hprefix tailTrace_1908692
  have hstable : (prefixWord ++ tailWord_1908692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908692).length < 2 ^ (prefixWord ++ tailWord_1908692).sum := by decide
  have hdescent : baseEnd_1908692 < baseStart_1908692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908703 : List Nat := [1, 1, 2, 3, 4, 1, 2, 1, 2, 5]
def baseStart_1908703 : Nat := 118140960795 + 1908703 * 2 ^ 59
def prefixEnd_1908703 : Nat := 4983230072969 + 3 ^ 40 * 1908703 * 2
def baseEnd_1908703 : Nat := 653388043785833949623027

theorem tailTrace_1908703 : CollatzResearch.WordTrace tailWord_1908703 prefixEnd_1908703 653388043785833949623027 := by
  unfold tailWord_1908703
  simp only [CollatzResearch.WordTrace]
  refine ⟨69616117604102486364874763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46410745069401657576583175 69616117604102486364874763)
  ·
    refine ⟨104424176406153729547312145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69616117604102486364874763 104424176406153729547312145)
    ·
      refine ⟨78318132304615297160484109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104424176406153729547312145 78318132304615297160484109)
      ·
        refine ⟨29369299614230736435181541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78318132304615297160484109 29369299614230736435181541)
        ·
          refine ⟨5506743677668263081596539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29369299614230736435181541 5506743677668263081596539)
          ·
            refine ⟨8260115516502394622394809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5506743677668263081596539 8260115516502394622394809)
            ·
              refine ⟨6195086637376795966796107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8260115516502394622394809 6195086637376795966796107)
              ·
                refine ⟨9292629956065193950194161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6195086637376795966796107 9292629956065193950194161)
                ·
                  refine ⟨6969472467048895462645621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9292629956065193950194161 6969472467048895462645621)
                  ·
                    refine ⟨653388043785833949623027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6969472467048895462645621 653388043785833949623027)
                    ·
                      rfl

theorem cell22_1908703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 1, 2, 5].length) (baseStart_1908703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1908703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1908703 prefixEnd_1908703 := by exact prefixLift 1908703
  have htrace : WordTrace (prefixWord ++ tailWord_1908703) baseStart_1908703 baseEnd_1908703 := by
    simpa [prefixWord, tailWord_1908703, baseEnd_1908703] using wordTrace_append hprefix tailTrace_1908703
  have hstable : (prefixWord ++ tailWord_1908703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908703).length < 2 ^ (prefixWord ++ tailWord_1908703).sum := by decide
  have hdescent : baseEnd_1908703 < baseStart_1908703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908726 : List Nat := [5, 1, 1, 1, 4, 2, 1, 3, 1, 3]
def baseStart_1908726 : Nat := 118140960795 + 1908726 * 2 ^ 59
def prefixEnd_1908726 : Nat := 4983230072969 + 3 ^ 40 * 1908726 * 2
def baseEnd_1908726 : Nat := 653395917155869556297957

theorem tailTrace_1908726 : CollatzResearch.WordTrace tailWord_1908726 prefixEnd_1908726 653395917155869556297957 := by
  unfold tailWord_1908726
  simp only [CollatzResearch.WordTrace]
  refine ⟨4351059780188697580810127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46411304322012774195308021 4351059780188697580810127)
  ·
    refine ⟨6526589670283046371215191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4351059780188697580810127 6526589670283046371215191)
    ·
      refine ⟨9789884505424569556822787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6526589670283046371215191 9789884505424569556822787)
      ·
        refine ⟨14684826758136854335234181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9789884505424569556822787 14684826758136854335234181)
        ·
          refine ⟨2753405017150660187856409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14684826758136854335234181 2753405017150660187856409)
          ·
            refine ⟨2065053762862995140892307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2753405017150660187856409 2065053762862995140892307)
            ·
              refine ⟨3097580644294492711338461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2065053762862995140892307 3097580644294492711338461)
              ·
                refine ⟨1161592741610434766751923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3097580644294492711338461 1161592741610434766751923)
                ·
                  refine ⟨1742389112415652150127885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1161592741610434766751923 1742389112415652150127885)
                  ·
                    refine ⟨653395917155869556297957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1742389112415652150127885 653395917155869556297957)
                    ·
                      rfl

theorem cell22_1908726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 3, 1, 3].length) (baseStart_1908726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1908726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1908726 prefixEnd_1908726 := by exact prefixLift 1908726
  have htrace : WordTrace (prefixWord ++ tailWord_1908726) baseStart_1908726 baseEnd_1908726 := by
    simpa [prefixWord, tailWord_1908726, baseEnd_1908726] using wordTrace_append hprefix tailTrace_1908726
  have hstable : (prefixWord ++ tailWord_1908726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908726).length < 2 ^ (prefixWord ++ tailWord_1908726).sum := by decide
  have hdescent : baseEnd_1908726 < baseStart_1908726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908756 : List Nat := [2, 4, 3, 2, 1, 2, 2, 1, 5]
def baseStart_1908756 : Nat := 118140960795 + 1908756 * 2 ^ 59
def prefixEnd_1908756 : Nat := 4983230072969 + 3 ^ 40 * 1908756 * 2
def baseEnd_1908756 : Nat := 217802062256319826015955

theorem tailTrace_1908756 : CollatzResearch.WordTrace tailWord_1908756 prefixEnd_1908756 217802062256319826015955 := by
  unfold tailWord_1908756
  simp only [CollatzResearch.WordTrace]
  refine ⟨34809025336455238208277061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46412033781940317611036081 34809025336455238208277061)
  ·
    refine ⟨6526692250585357164051949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34809025336455238208277061 6526692250585357164051949)
    ·
      refine ⟨2447509593969508936519481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6526692250585357164051949 2447509593969508936519481)
      ·
        refine ⟨1835632195477131702389611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2447509593969508936519481 1835632195477131702389611)
        ·
          refine ⟨2753448293215697553584417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1835632195477131702389611 2753448293215697553584417)
          ·
            refine ⟨2065086219911773165188313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2753448293215697553584417 2065086219911773165188313)
            ·
              refine ⟨1548814664933829873891235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2065086219911773165188313 1548814664933829873891235)
              ·
                refine ⟨2323221997400744810836853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1548814664933829873891235 2323221997400744810836853)
                ·
                  refine ⟨217802062256319826015955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2323221997400744810836853 217802062256319826015955)
                  ·
                    rfl

theorem cell22_1908756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 2, 1, 5].length) (baseStart_1908756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1908756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1908756 prefixEnd_1908756 := by exact prefixLift 1908756
  have htrace : WordTrace (prefixWord ++ tailWord_1908756) baseStart_1908756 baseEnd_1908756 := by
    simpa [prefixWord, tailWord_1908756, baseEnd_1908756] using wordTrace_append hprefix tailTrace_1908756
  have hstable : (prefixWord ++ tailWord_1908756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908756).length < 2 ^ (prefixWord ++ tailWord_1908756).sum := by decide
  have hdescent : baseEnd_1908756 < baseStart_1908756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908769 : List Nat := [1, 2, 3, 2, 5, 1, 1, 2, 1, 4]
def baseStart_1908769 : Nat := 118140960795 + 1908769 * 2 ^ 59
def prefixEnd_1908769 : Nat := 4983230072969 + 3 ^ 40 * 1908769 * 2
def baseEnd_1908769 : Nat := 653410636934631777472825

theorem tailTrace_1908769 : CollatzResearch.WordTrace tailWord_1908769 prefixEnd_1908769 653410636934631777472825 := by
  unfold tailWord_1908769
  simp only [CollatzResearch.WordTrace]
  refine ⟨69618524821863379636777361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46412349881242253091184907 69618524821863379636777361)
  ·
    refine ⟨52213893616397534727583021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69618524821863379636777361 52213893616397534727583021)
    ·
      refine ⟨19580210106149075522843633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52213893616397534727583021 19580210106149075522843633)
      ·
        refine ⟨14685157579611806642132725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19580210106149075522843633 14685157579611806642132725)
        ·
          refine ⟨1376733523088606872699943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14685157579611806642132725 1376733523088606872699943)
          ·
            refine ⟨2065100284632910309049915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1376733523088606872699943 2065100284632910309049915)
            ·
              refine ⟨3097650426949365463574873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2065100284632910309049915 3097650426949365463574873)
              ·
                refine ⟨2323237820212024097681155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3097650426949365463574873 2323237820212024097681155)
                ·
                  refine ⟨3484856730318036146521733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2323237820212024097681155 3484856730318036146521733)
                  ·
                    refine ⟨653410636934631777472825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3484856730318036146521733 653410636934631777472825)
                    ·
                      rfl

theorem cell22_1908769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 2, 1, 4].length) (baseStart_1908769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1908769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1908769 prefixEnd_1908769 := by exact prefixLift 1908769
  have htrace : WordTrace (prefixWord ++ tailWord_1908769) baseStart_1908769 baseEnd_1908769 := by
    simpa [prefixWord, tailWord_1908769, baseEnd_1908769] using wordTrace_append hprefix tailTrace_1908769
  have hstable : (prefixWord ++ tailWord_1908769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908769).length < 2 ^ (prefixWord ++ tailWord_1908769).sum := by decide
  have hdescent : baseEnd_1908769 < baseStart_1908769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908810 : List Nat := [3, 1, 2, 1, 1, 2, 1, 5, 3, 3]
def baseStart_1908810 : Nat := 118140960795 + 1908810 * 2 ^ 59
def prefixEnd_1908810 : Nat := 4983230072969 + 3 ^ 40 * 1908810 * 2
def baseEnd_1908810 : Nat := 653424672072521337197699

theorem tailTrace_1908810 : CollatzResearch.WordTrace tailWord_1908810 prefixEnd_1908810 653424672072521337197699 := by
  unfold tailWord_1908810
  simp only [CollatzResearch.WordTrace]
  refine ⟨17405005053678710909754971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46413346809809895759346589 17405005053678710909754971)
  ·
    refine ⟨26107507580518066364632457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17405005053678710909754971 26107507580518066364632457)
    ·
      refine ⟨19580630685388549773474343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26107507580518066364632457 19580630685388549773474343)
      ·
        refine ⟨29370946028082824660211515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19580630685388549773474343 29370946028082824660211515)
        ·
          refine ⟨44056419042124236990317273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29370946028082824660211515 44056419042124236990317273)
          ·
            refine ⟨33042314281593177742737955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44056419042124236990317273 33042314281593177742737955)
            ·
              refine ⟨49563471422389766614106933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33042314281593177742737955 49563471422389766614106933)
              ·
                refine ⟨4646575445849040620072525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49563471422389766614106933 4646575445849040620072525)
                ·
                  refine ⟨1742465792193390232527197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4646575445849040620072525 1742465792193390232527197)
                  ·
                    refine ⟨653424672072521337197699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1742465792193390232527197 653424672072521337197699)
                    ·
                      rfl

theorem cell22_1908810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 5, 3, 3].length) (baseStart_1908810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1908810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1908810 prefixEnd_1908810 := by exact prefixLift 1908810
  have htrace : WordTrace (prefixWord ++ tailWord_1908810) baseStart_1908810 baseEnd_1908810 := by
    simpa [prefixWord, tailWord_1908810, baseEnd_1908810] using wordTrace_append hprefix tailTrace_1908810
  have hstable : (prefixWord ++ tailWord_1908810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908810).length < 2 ^ (prefixWord ++ tailWord_1908810).sum := by decide
  have hdescent : baseEnd_1908810 < baseStart_1908810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908844 : List Nat := [2, 2, 1, 1, 3, 4, 2, 3, 1, 3]
def baseStart_1908844 : Nat := 118140960795 + 1908844 * 2 ^ 59
def prefixEnd_1908844 : Nat := 4983230072969 + 3 ^ 40 * 1908844 * 2
def baseEnd_1908844 : Nat := 653436310967356581847595

theorem tailTrace_1908844 : CollatzResearch.WordTrace tailWord_1908844 prefixEnd_1908844 653436310967356581847595 := by
  unfold tailWord_1908844
  simp only [CollatzResearch.WordTrace]
  refine ⟨34810630148295833722878793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46414173531061111630505057 34810630148295833722878793)
  ·
    refine ⟨26107972611221875292159095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34810630148295833722878793 26107972611221875292159095)
    ·
      refine ⟨39161958916832812938238643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26107972611221875292159095 39161958916832812938238643)
      ·
        refine ⟨58742938375249219407357965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39161958916832812938238643 58742938375249219407357965)
        ·
          refine ⟨22028601890718457277759237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58742938375249219407357965 22028601890718457277759237)
          ·
            refine ⟨4130362854509710739579857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22028601890718457277759237 4130362854509710739579857)
            ·
              refine ⟨3097772140882283054684893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4130362854509710739579857 3097772140882283054684893)
              ·
                refine ⟨1161664552830856145506835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3097772140882283054684893 1161664552830856145506835)
                ·
                  refine ⟨1742496829246284218260253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1161664552830856145506835 1742496829246284218260253)
                  ·
                    refine ⟨653436310967356581847595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1742496829246284218260253 653436310967356581847595)
                    ·
                      rfl

theorem cell22_1908844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 3, 1, 3].length) (baseStart_1908844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1908844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1908844 prefixEnd_1908844 := by exact prefixLift 1908844
  have htrace : WordTrace (prefixWord ++ tailWord_1908844) baseStart_1908844 baseEnd_1908844 := by
    simpa [prefixWord, tailWord_1908844, baseEnd_1908844] using wordTrace_append hprefix tailTrace_1908844
  have hstable : (prefixWord ++ tailWord_1908844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908844).length < 2 ^ (prefixWord ++ tailWord_1908844).sum := by decide
  have hdescent : baseEnd_1908844 < baseStart_1908844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908857 : List Nat := [1, 2, 1, 3, 4, 3, 1, 2, 5]
def baseStart_1908857 : Nat := 118140960795 + 1908857 * 2 ^ 59
def prefixEnd_1908857 : Nat := 4983230072969 + 3 ^ 40 * 1908857 * 2
def baseEnd_1908857 : Nat := 217813587044342960424185

theorem tailTrace_1908857 : CollatzResearch.WordTrace tailWord_1908857 prefixEnd_1908857 217813587044342960424185 := by
  unfold tailWord_1908857
  simp only [CollatzResearch.WordTrace]
  refine ⟨69621734445544570665980825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46414489630363047110653883 69621734445544570665980825)
  ·
    refine ⟨52216300834158427999485619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69621734445544570665980825 52216300834158427999485619)
    ·
      refine ⟨78324451251237641999228429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52216300834158427999485619 78324451251237641999228429)
      ·
        refine ⟨29371669219214115749710661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78324451251237641999228429 29371669219214115749710661)
        ·
          refine ⟨5507187978602646703070749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29371669219214115749710661 5507187978602646703070749)
          ·
            refine ⟨2065195491975992513651531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5507187978602646703070749 2065195491975992513651531)
            ·
              refine ⟨3097793237963988770477297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2065195491975992513651531 3097793237963988770477297)
              ·
                refine ⟨2323344928472991577857973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3097793237963988770477297 2323344928472991577857973)
                ·
                  refine ⟨217813587044342960424185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2323344928472991577857973 217813587044342960424185)
                  ·
                    rfl

theorem cell22_1908857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 2, 5].length) (baseStart_1908857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1908857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1908857 prefixEnd_1908857 := by exact prefixLift 1908857
  have htrace : WordTrace (prefixWord ++ tailWord_1908857) baseStart_1908857 baseEnd_1908857 := by
    simpa [prefixWord, tailWord_1908857, baseEnd_1908857] using wordTrace_append hprefix tailTrace_1908857
  have hstable : (prefixWord ++ tailWord_1908857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908857).length < 2 ^ (prefixWord ++ tailWord_1908857).sum := by decide
  have hdescent : baseEnd_1908857 < baseStart_1908857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908919 : List Nat := [1, 1, 3, 1, 4, 3, 3, 2, 4]
def baseStart_1908919 : Nat := 118140960795 + 1908919 * 2 ^ 59
def prefixEnd_1908919 : Nat := 4983230072969 + 3 ^ 40 * 1908919 * 2
def baseEnd_1908919 : Nat := 217820661666693795407455

theorem tailTrace_1908919 : CollatzResearch.WordTrace tailWord_1908919 prefixEnd_1908919 217820661666693795407455 := by
  unfold tailWord_1908919
  simp only [CollatzResearch.WordTrace]
  refine ⟨69623995771319955254737811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46415997180879970169825207 69623995771319955254737811)
  ·
    refine ⟨104435993656979932882106717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69623995771319955254737811 104435993656979932882106717)
    ·
      refine ⟨39163497621367474830790019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104435993656979932882106717 39163497621367474830790019)
      ·
        refine ⟨58745246432051212246185029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39163497621367474830790019 58745246432051212246185029)
        ·
          refine ⟨11014733706009602296159693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58745246432051212246185029 11014733706009602296159693)
          ·
            refine ⟨4130525139753600861059885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11014733706009602296159693 4130525139753600861059885)
            ·
              refine ⟨1548946927407600322897457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4130525139753600861059885 1548946927407600322897457)
              ·
                refine ⟨1161710195555700242173093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1548946927407600322897457 1161710195555700242173093)
                ·
                  refine ⟨217820661666693795407455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1161710195555700242173093 217820661666693795407455)
                  ·
                    rfl

theorem cell22_1908919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 3, 2, 4].length) (baseStart_1908919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1908919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1908919 prefixEnd_1908919 := by exact prefixLift 1908919
  have htrace : WordTrace (prefixWord ++ tailWord_1908919) baseStart_1908919 baseEnd_1908919 := by
    simpa [prefixWord, tailWord_1908919, baseEnd_1908919] using wordTrace_append hprefix tailTrace_1908919
  have hstable : (prefixWord ++ tailWord_1908919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908919).length < 2 ^ (prefixWord ++ tailWord_1908919).sum := by decide
  have hdescent : baseEnd_1908919 < baseStart_1908919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908949 : List Nat := [1, 3, 2, 4, 2, 1, 2, 1, 2, 4]
def baseStart_1908949 : Nat := 118140960795 + 1908949 * 2 ^ 59
def prefixEnd_1908949 : Nat := 4983230072969 + 3 ^ 40 * 1908949 * 2
def baseEnd_1908949 : Nat := 653472254613171307972273

theorem tailTrace_1908949 : CollatzResearch.WordTrace tailWord_1908949 prefixEnd_1908949 653472254613171307972273 := by
  unfold tailWord_1908949
  simp only [CollatzResearch.WordTrace]
  refine ⟨69625089961211270378329901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46416726640807513585553267 69625089961211270378329901)
  ·
    refine ⟨26109408735454226391873713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69625089961211270378329901 26109408735454226391873713)
    ·
      refine ⟨19582056551590669793905285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26109408735454226391873713 19582056551590669793905285)
      ·
        refine ⟨3671635603423250586357241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19582056551590669793905285 3671635603423250586357241)
        ·
          refine ⟨2753726702567437939767931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3671635603423250586357241 2753726702567437939767931)
          ·
            refine ⟨4130590053851156909651897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2753726702567437939767931 4130590053851156909651897)
            ·
              refine ⟨3097942540388367682238923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4130590053851156909651897 3097942540388367682238923)
              ·
                refine ⟨4646913810582551523358385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3097942540388367682238923 4646913810582551523358385)
                ·
                  refine ⟨3485185357936913642518789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4646913810582551523358385 3485185357936913642518789)
                  ·
                    refine ⟨653472254613171307972273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3485185357936913642518789 653472254613171307972273)
                    ·
                      rfl

theorem cell22_1908949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 1, 2, 4].length) (baseStart_1908949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1908949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1908949 prefixEnd_1908949 := by exact prefixLift 1908949
  have htrace : WordTrace (prefixWord ++ tailWord_1908949) baseStart_1908949 baseEnd_1908949 := by
    simpa [prefixWord, tailWord_1908949, baseEnd_1908949] using wordTrace_append hprefix tailTrace_1908949
  have hstable : (prefixWord ++ tailWord_1908949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908949).length < 2 ^ (prefixWord ++ tailWord_1908949).sum := by decide
  have hdescent : baseEnd_1908949 < baseStart_1908949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1908979 : List Nat := [1, 1, 1, 2, 2, 4, 3, 4, 1, 3]
def baseStart_1908979 : Nat := 118140960795 + 1908979 * 2 ^ 59
def prefixEnd_1908979 : Nat := 4983230072969 + 3 ^ 40 * 1908979 * 2
def baseEnd_1908979 : Nat := 653482524226261229722181

theorem tailTrace_1908979 : CollatzResearch.WordTrace tailWord_1908979 prefixEnd_1908979 653482524226261229722181 := by
  unfold tailWord_1908979
  simp only [CollatzResearch.WordTrace]
  refine ⟨69626184151102585501921991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46417456100735057001281327 69626184151102585501921991)
  ·
    refine ⟨104439276226653878252882987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69626184151102585501921991 104439276226653878252882987)
    ·
      refine ⟨156658914339980817379324481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104439276226653878252882987 156658914339980817379324481)
      ·
        refine ⟨117494185754985613034493361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156658914339980817379324481 117494185754985613034493361)
        ·
          refine ⟨88120639316239209775870021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117494185754985613034493361 88120639316239209775870021)
          ·
            refine ⟨16522619871794851832975629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88120639316239209775870021 16522619871794851832975629)
            ·
              refine ⟨6195982451923069437365861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16522619871794851832975629 6195982451923069437365861)
              ·
                refine ⟨1161746709735575519506099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6195982451923069437365861 1161746709735575519506099)
                ·
                  refine ⟨1742620064603363279259149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1161746709735575519506099 1742620064603363279259149)
                  ·
                    refine ⟨653482524226261229722181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1742620064603363279259149 653482524226261229722181)
                    ·
                      rfl

theorem cell22_1908979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 4, 1, 3].length) (baseStart_1908979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1908979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1908979 prefixEnd_1908979 := by exact prefixLift 1908979
  have htrace : WordTrace (prefixWord ++ tailWord_1908979) baseStart_1908979 baseEnd_1908979 := by
    simpa [prefixWord, tailWord_1908979, baseEnd_1908979] using wordTrace_append hprefix tailTrace_1908979
  have hstable : (prefixWord ++ tailWord_1908979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1908979).length < 2 ^ (prefixWord ++ tailWord_1908979).sum := by decide
  have hdescent : baseEnd_1908979 < baseStart_1908979 := by decide
  rcases family_descends (prefixWord ++ tailWord_1908979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909020 : List Nat := [2, 2, 3, 1, 1, 1, 1, 1, 10]
def baseStart_1909020 : Nat := 118140960795 + 1909020 * 2 ^ 59
def prefixEnd_1909020 : Nat := 4983230072969 + 3 ^ 40 * 1909020 * 2
def baseEnd_1909020 : Nat := 217832186454716929815685

theorem tailTrace_1909020 : CollatzResearch.WordTrace tailWord_1909020 prefixEnd_1909020 217832186454716929815685 := by
  unfold tailWord_1909020
  simp only [CollatzResearch.WordTrace]
  refine ⟨34813839771977024752082257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46418453029302699669443009 34813839771977024752082257)
  ·
    refine ⟨26110379828982768564061693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34813839771977024752082257 26110379828982768564061693)
    ·
      refine ⟨9791392435868538211523135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26110379828982768564061693 9791392435868538211523135)
      ·
        refine ⟨14687088653802807317284703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9791392435868538211523135 14687088653802807317284703)
        ·
          refine ⟨22030632980704210975927055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14687088653802807317284703 22030632980704210975927055)
          ·
            refine ⟨33045949471056316463890583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22030632980704210975927055 33045949471056316463890583)
            ·
              refine ⟨49568924206584474695835875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33045949471056316463890583 49568924206584474695835875)
              ·
                refine ⟨74353386309876712043753813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49568924206584474695835875 74353386309876712043753813)
                ·
                  refine ⟨217832186454716929815685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 74353386309876712043753813 217832186454716929815685)
                  ·
                    rfl

theorem cell22_1909020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 10].length) (baseStart_1909020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1909020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1909020 prefixEnd_1909020 := by exact prefixLift 1909020
  have htrace : WordTrace (prefixWord ++ tailWord_1909020) baseStart_1909020 baseEnd_1909020 := by
    simpa [prefixWord, tailWord_1909020, baseEnd_1909020] using wordTrace_append hprefix tailTrace_1909020
  have hstable : (prefixWord ++ tailWord_1909020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909020).length < 2 ^ (prefixWord ++ tailWord_1909020).sum := by decide
  have hdescent : baseEnd_1909020 < baseStart_1909020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909144 : List Nat := [2, 1, 2, 5, 1, 1, 1, 4, 5]
def baseStart_1909144 : Nat := 118140960795 + 1909144 * 2 ^ 59
def prefixEnd_1909144 : Nat := 4983230072969 + 3 ^ 40 * 1909144 * 2
def baseEnd_1909144 : Nat := 217846335699418599782225

theorem tailTrace_1909144 : CollatzResearch.WordTrace tailWord_1909144 prefixEnd_1909144 217846335699418599782225 := by
  unfold tailWord_1909144
  simp only [CollatzResearch.WordTrace]
  refine ⟨34816101097752409340839243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46421468130336545787785657 34816101097752409340839243)
  ·
    refine ⟨52224151646628614011258865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34816101097752409340839243 52224151646628614011258865)
    ·
      refine ⟨39168113734971460508444149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52224151646628614011258865 39168113734971460508444149)
      ·
        refine ⟨3672010662653574422666639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39168113734971460508444149 3672010662653574422666639)
        ·
          refine ⟨5508015993980361633999959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3672010662653574422666639 5508015993980361633999959)
          ·
            refine ⟨8262023990970542450999939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5508015993980361633999959 8262023990970542450999939)
            ·
              refine ⟨12393035986455813676499909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8262023990970542450999939 12393035986455813676499909)
              ·
                refine ⟨2323694247460465064343733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12393035986455813676499909 2323694247460465064343733)
                ·
                  refine ⟨217846335699418599782225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2323694247460465064343733 217846335699418599782225)
                  ·
                    rfl

theorem cell22_1909144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 4, 5].length) (baseStart_1909144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1909144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1909144 prefixEnd_1909144 := by exact prefixLift 1909144
  have htrace : WordTrace (prefixWord ++ tailWord_1909144) baseStart_1909144 baseEnd_1909144 := by
    simpa [prefixWord, tailWord_1909144, baseEnd_1909144] using wordTrace_append hprefix tailTrace_1909144
  have hstable : (prefixWord ++ tailWord_1909144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909144).length < 2 ^ (prefixWord ++ tailWord_1909144).sum := by decide
  have hdescent : baseEnd_1909144 < baseStart_1909144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909157 : List Nat := [1, 3, 1, 2, 1, 1, 3, 1, 5, 4]
def baseStart_1909157 : Nat := 118140960795 + 1909157 * 2 ^ 59
def prefixEnd_1909157 : Nat := 4983230072969 + 3 ^ 40 * 1909157 * 2
def baseEnd_1909157 : Nat := 653543457263928098771635

theorem tailTrace_1909157 : CollatzResearch.WordTrace tailWord_1909157 prefixEnd_1909157 653543457263928098771635 := by
  unfold tailWord_1909157
  simp only [CollatzResearch.WordTrace]
  refine ⟨69632676344457721901901725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46421784229638481267934483 69632676344457721901901725)
  ·
    refine ⟨26112253629171645713213147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69632676344457721901901725 26112253629171645713213147)
    ·
      refine ⟨39168380443757468569819721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26112253629171645713213147 39168380443757468569819721)
      ·
        refine ⟨29376285332818101427364791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39168380443757468569819721 29376285332818101427364791)
        ·
          refine ⟨44064427999227152141047187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29376285332818101427364791 44064427999227152141047187)
          ·
            refine ⟨66096641998840728211570781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44064427999227152141047187 66096641998840728211570781)
            ·
              refine ⟨24786240749565273079339043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66096641998840728211570781 24786240749565273079339043)
              ·
                refine ⟨37179361124347909619008565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24786240749565273079339043 37179361124347909619008565)
                ·
                  refine ⟨3485565105407616526782053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37179361124347909619008565 3485565105407616526782053)
                  ·
                    refine ⟨653543457263928098771635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3485565105407616526782053 653543457263928098771635)
                    ·
                      rfl

theorem cell22_1909157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 5, 4].length) (baseStart_1909157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1909157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1909157 prefixEnd_1909157 := by exact prefixLift 1909157
  have htrace : WordTrace (prefixWord ++ tailWord_1909157) baseStart_1909157 baseEnd_1909157 := by
    simpa [prefixWord, tailWord_1909157, baseEnd_1909157] using wordTrace_append hprefix tailTrace_1909157
  have hstable : (prefixWord ++ tailWord_1909157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909157).length < 2 ^ (prefixWord ++ tailWord_1909157).sum := by decide
  have hdescent : baseEnd_1909157 < baseStart_1909157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909159 : List Nat := [1, 1, 6, 1, 1, 3, 1, 1, 2, 5]
def baseStart_1909159 : Nat := 118140960795 + 1909159 * 2 ^ 59
def prefixEnd_1909159 : Nat := 4983230072969 + 3 ^ 40 * 1909159 * 2
def baseEnd_1909159 : Nat := 653544141904800760221629

theorem tailTrace_1909159 : CollatzResearch.WordTrace tailWord_1909159 prefixEnd_1909159 653544141904800760221629 := by
  unfold tailWord_1909159
  simp only [CollatzResearch.WordTrace]
  refine ⟨69632749290450476243474531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46421832860300317495649687 69632749290450476243474531)
  ·
    refine ⟨104449123935675714365211797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69632749290450476243474531 104449123935675714365211797)
    ·
      refine ⟨4896052684484799110869303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 104449123935675714365211797 4896052684484799110869303)
      ·
        refine ⟨7344079026727198666303955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4896052684484799110869303 7344079026727198666303955)
        ·
          refine ⟨11016118540090797999455933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7344079026727198666303955 11016118540090797999455933)
          ·
            refine ⟨4131044452534049249795975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11016118540090797999455933 4131044452534049249795975)
            ·
              refine ⟨6196566678801073874693963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4131044452534049249795975 6196566678801073874693963)
              ·
                refine ⟨9294850018201610812040945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6196566678801073874693963 9294850018201610812040945)
                ·
                  refine ⟨6971137513651208109030709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9294850018201610812040945 6971137513651208109030709)
                  ·
                    refine ⟨653544141904800760221629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6971137513651208109030709 653544141904800760221629)
                    ·
                      rfl

theorem cell22_1909159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_1909159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1909159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1909159 prefixEnd_1909159 := by exact prefixLift 1909159
  have htrace : WordTrace (prefixWord ++ tailWord_1909159) baseStart_1909159 baseEnd_1909159 := by
    simpa [prefixWord, tailWord_1909159, baseEnd_1909159] using wordTrace_append hprefix tailTrace_1909159
  have hstable : (prefixWord ++ tailWord_1909159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909159).length < 2 ^ (prefixWord ++ tailWord_1909159).sum := by decide
  have hdescent : baseEnd_1909159 < baseStart_1909159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909191 : List Nat := [1, 1, 4, 1, 1, 4, 4, 1, 1, 4]
def baseStart_1909191 : Nat := 118140960795 + 1909191 * 2 ^ 59
def prefixEnd_1909191 : Nat := 4983230072969 + 3 ^ 40 * 1909191 * 2
def baseEnd_1909191 : Nat := 653555096158763343421531

theorem tailTrace_1909191 : CollatzResearch.WordTrace tailWord_1909191 prefixEnd_1909191 653555096158763343421531 := by
  unfold tailWord_1909191
  simp only [CollatzResearch.WordTrace]
  refine ⟨69633916426334545708639427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46422610950889697139092951 69633916426334545708639427)
  ·
    refine ⟨104450874639501818562959141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69633916426334545708639427 104450874639501818562959141)
    ·
      refine ⟨19584538994906590980554839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104450874639501818562959141 19584538994906590980554839)
      ·
        refine ⟨29376808492359886470832259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19584538994906590980554839 29376808492359886470832259)
        ·
          refine ⟨44065212738539829706248389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29376808492359886470832259 44065212738539829706248389)
          ·
            refine ⟨8262227388476218069921573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44065212738539829706248389 8262227388476218069921573)
            ·
              refine ⟨1549167635339290888110295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8262227388476218069921573 1549167635339290888110295)
              ·
                refine ⟨2323751453008936332165443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1549167635339290888110295 2323751453008936332165443)
                ·
                  refine ⟨3485627179513404498248165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2323751453008936332165443 3485627179513404498248165)
                  ·
                    refine ⟨653555096158763343421531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3485627179513404498248165 653555096158763343421531)
                    ·
                      rfl

theorem cell22_1909191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 4, 1, 1, 4].length) (baseStart_1909191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1909191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1909191 prefixEnd_1909191 := by exact prefixLift 1909191
  have htrace : WordTrace (prefixWord ++ tailWord_1909191) baseStart_1909191 baseEnd_1909191 := by
    simpa [prefixWord, tailWord_1909191, baseEnd_1909191] using wordTrace_append hprefix tailTrace_1909191
  have hstable : (prefixWord ++ tailWord_1909191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909191).length < 2 ^ (prefixWord ++ tailWord_1909191).sum := by decide
  have hdescent : baseEnd_1909191 < baseStart_1909191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909206 : List Nat := [5, 2, 1, 1, 1, 1, 4, 1, 6]
def baseStart_1909206 : Nat := 118140960795 + 1909206 * 2 ^ 59
def prefixEnd_1909206 : Nat := 4983230072969 + 3 ^ 40 * 1909206 * 2
def baseEnd_1909206 : Nat := 217853410321769434765495

theorem tailTrace_1909206 : CollatzResearch.WordTrace tailWord_1909206 prefixEnd_1909206 217853410321769434765495 := by
  unfold tailWord_1909206
  simp only [CollatzResearch.WordTrace]
  refine ⟨4352153970080012704402217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46422975680853468846956981 4352153970080012704402217)
  ·
    refine ⟨3264115477560009528301663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4352153970080012704402217 3264115477560009528301663)
    ·
      refine ⟨4896173216340014292452495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3264115477560009528301663 4896173216340014292452495)
      ·
        refine ⟨7344259824510021438678743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4896173216340014292452495 7344259824510021438678743)
        ·
          refine ⟨11016389736765032158018115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7344259824510021438678743 11016389736765032158018115)
          ·
            refine ⟨16524584605147548237027173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11016389736765032158018115 16524584605147548237027173)
            ·
              refine ⟨3098359613465165294442595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16524584605147548237027173 3098359613465165294442595)
              ·
                refine ⟨4647539420197747941663893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3098359613465165294442595 4647539420197747941663893)
                ·
                  refine ⟨217853410321769434765495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4647539420197747941663893 217853410321769434765495)
                  ·
                    rfl

theorem cell22_1909206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_1909206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1909206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1909206 prefixEnd_1909206 := by exact prefixLift 1909206
  have htrace : WordTrace (prefixWord ++ tailWord_1909206) baseStart_1909206 baseEnd_1909206 := by
    simpa [prefixWord, tailWord_1909206, baseEnd_1909206] using wordTrace_append hprefix tailTrace_1909206
  have hstable : (prefixWord ++ tailWord_1909206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909206).length < 2 ^ (prefixWord ++ tailWord_1909206).sum := by decide
  have hdescent : baseEnd_1909206 < baseStart_1909206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909217 : List Nat := [1, 2, 3, 1, 2, 2, 2, 9]
def baseStart_1909217 : Nat := 118140960795 + 1909217 * 2 ^ 59
def prefixEnd_1909217 : Nat := 4983230072969 + 3 ^ 40 * 1909217 * 2
def baseEnd_1909217 : Nat := 72618221832234215807939

theorem tailTrace_1909217 : CollatzResearch.WordTrace tailWord_1909217 prefixEnd_1909217 72618221832234215807939 := by
  unfold tailWord_1909217
  simp only [CollatzResearch.WordTrace]
  refine ⟨69634864724240352149085905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46423243149493568099390603 69634864724240352149085905)
  ·
    refine ⟨52226148543180264111814429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69634864724240352149085905 52226148543180264111814429)
    ·
      refine ⟨19584805703692599041930411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52226148543180264111814429 19584805703692599041930411)
      ·
        refine ⟨29377208555538898562895617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19584805703692599041930411 29377208555538898562895617)
        ·
          refine ⟨22032906416654173922171713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29377208555538898562895617 22032906416654173922171713)
          ·
            refine ⟨16524679812490630441628785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22032906416654173922171713 16524679812490630441628785)
            ·
              refine ⟨12393509859367972831221589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16524679812490630441628785 12393509859367972831221589)
              ·
                refine ⟨72618221832234215807939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12393509859367972831221589 72618221832234215807939)
                ·
                  rfl

theorem cell22_1909217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 9].length) (baseStart_1909217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1909217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1909217 prefixEnd_1909217 := by exact prefixLift 1909217
  have htrace : WordTrace (prefixWord ++ tailWord_1909217) baseStart_1909217 baseEnd_1909217 := by
    simpa [prefixWord, tailWord_1909217, baseEnd_1909217] using wordTrace_append hprefix tailTrace_1909217
  have hstable : (prefixWord ++ tailWord_1909217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909217).length < 2 ^ (prefixWord ++ tailWord_1909217).sum := by decide
  have hdescent : baseEnd_1909217 < baseStart_1909217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909232 : List Nat := [2, 1, 1, 1, 3, 3, 1, 1, 2, 7]
def baseStart_1909232 : Nat := 118140960795 + 1909232 * 2 ^ 59
def prefixEnd_1909232 : Nat := 4983230072969 + 3 ^ 40 * 1909232 * 2
def baseEnd_1909232 : Nat := 653569131296652903146405

theorem tailTrace_1909232 : CollatzResearch.WordTrace tailWord_1909232 prefixEnd_1909232 653569131296652903146405 := by
  unfold tailWord_1909232
  simp only [CollatzResearch.WordTrace]
  refine ⟨34817705909593004855440975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46423607879457339807254633 34817705909593004855440975)
  ·
    refine ⟨52226558864389507283161463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34817705909593004855440975 52226558864389507283161463)
    ·
      refine ⟨78339838296584260924742195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52226558864389507283161463 78339838296584260924742195)
      ·
        refine ⟨117509757444876391387113293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78339838296584260924742195 117509757444876391387113293)
        ·
          refine ⟨44066159041828646770167485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117509757444876391387113293 44066159041828646770167485)
          ·
            refine ⟨16524809640685742538812807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44066159041828646770167485 16524809640685742538812807)
            ·
              refine ⟨24787214461028613808219211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16524809640685742538812807 24787214461028613808219211)
              ·
                refine ⟨37180821691542920712328817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24787214461028613808219211 37180821691542920712328817)
                ·
                  refine ⟨27885616268657190534246613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37180821691542920712328817 27885616268657190534246613)
                  ·
                    refine ⟨653569131296652903146405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27885616268657190534246613 653569131296652903146405)
                    ·
                      rfl

theorem cell22_1909232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 2, 7].length) (baseStart_1909232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1909232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1909232 prefixEnd_1909232 := by exact prefixLift 1909232
  have htrace : WordTrace (prefixWord ++ tailWord_1909232) baseStart_1909232 baseEnd_1909232 := by
    simpa [prefixWord, tailWord_1909232, baseEnd_1909232] using wordTrace_append hprefix tailTrace_1909232
  have hstable : (prefixWord ++ tailWord_1909232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909232).length < 2 ^ (prefixWord ++ tailWord_1909232).sum := by decide
  have hdescent : baseEnd_1909232 < baseStart_1909232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909324 : List Nat := [2, 2, 1, 3, 1, 2, 2, 3, 6]
def baseStart_1909324 : Nat := 118140960795 + 1909324 * 2 ^ 59
def prefixEnd_1909324 : Nat := 4983230072969 + 3 ^ 40 * 1909324 * 2
def baseEnd_1909324 : Nat := 217866874925598443282041

theorem tailTrace_1909324 : CollatzResearch.WordTrace tailWord_1909324 prefixEnd_1909324 217866874925598443282041 := by
  unfold tailWord_1909324
  simp only [CollatzResearch.WordTrace]
  refine ⟨34819383667426354711615513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46425844889901806282154017 34819383667426354711615513)
  ·
    refine ⟨26114537750569766033711635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34819383667426354711615513 26114537750569766033711635)
    ·
      refine ⟨39171806625854649050567453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26114537750569766033711635 39171806625854649050567453)
      ·
        refine ⟨14689427484695493393962795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39171806625854649050567453 14689427484695493393962795)
        ·
          refine ⟨22034141227043240090944193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14689427484695493393962795 22034141227043240090944193)
          ·
            refine ⟨16525605920282430068208145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22034141227043240090944193 16525605920282430068208145)
            ·
              refine ⟨12394204440211822551156109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16525605920282430068208145 12394204440211822551156109)
              ·
                refine ⟨4647826665079433456683541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12394204440211822551156109 4647826665079433456683541)
                ·
                  refine ⟨217866874925598443282041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4647826665079433456683541 217866874925598443282041)
                  ·
                    rfl

theorem cell22_1909324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 3, 6].length) (baseStart_1909324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1909324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1909324 prefixEnd_1909324 := by exact prefixLift 1909324
  have htrace : WordTrace (prefixWord ++ tailWord_1909324) baseStart_1909324 baseEnd_1909324 := by
    simpa [prefixWord, tailWord_1909324, baseEnd_1909324] using wordTrace_append hprefix tailTrace_1909324
  have hstable : (prefixWord ++ tailWord_1909324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909324).length < 2 ^ (prefixWord ++ tailWord_1909324).sum := by decide
  have hdescent : baseEnd_1909324 < baseStart_1909324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909358 : List Nat := [4, 1, 2, 2, 2, 1, 1, 5, 4]
def baseStart_1909358 : Nat := 118140960795 + 1909358 * 2 ^ 59
def prefixEnd_1909358 : Nat := 4983230072969 + 3 ^ 40 * 1909358 * 2
def baseEnd_1909358 : Nat := 217870754557210191498673

theorem tailTrace_1909358 : CollatzResearch.WordTrace tailWord_1909358 prefixEnd_1909358 217870754557210191498673 := by
  unfold tailWord_1909358
  simp only [CollatzResearch.WordTrace]
  refine ⟨8705000927091191653746091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46426671611153022153312485 8705000927091191653746091)
  ·
    refine ⟨13057501390636787480619137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8705000927091191653746091 13057501390636787480619137)
    ·
      refine ⟨9793126042977590610464353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13057501390636787480619137 9793126042977590610464353)
      ·
        refine ⟨7344844532233192957848265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9793126042977590610464353 7344844532233192957848265)
        ·
          refine ⟨5508633399174894718386199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7344844532233192957848265 5508633399174894718386199)
          ·
            refine ⟨8262950098762342077579299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5508633399174894718386199 8262950098762342077579299)
            ·
              refine ⟨12394425148143513116368949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8262950098762342077579299 12394425148143513116368949)
              ·
                refine ⟨1161977357638454354659589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12394425148143513116368949 1161977357638454354659589)
                ·
                  refine ⟨217870754557210191498673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1161977357638454354659589 217870754557210191498673)
                  ·
                    rfl

theorem cell22_1909358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 5, 4].length) (baseStart_1909358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1909358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1909358 prefixEnd_1909358 := by exact prefixLift 1909358
  have htrace : WordTrace (prefixWord ++ tailWord_1909358) baseStart_1909358 baseEnd_1909358 := by
    simpa [prefixWord, tailWord_1909358, baseEnd_1909358] using wordTrace_append hprefix tailTrace_1909358
  have hstable : (prefixWord ++ tailWord_1909358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909358).length < 2 ^ (prefixWord ++ tailWord_1909358).sum := by decide
  have hdescent : baseEnd_1909358 < baseStart_1909358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909360 : List Nat := [2, 1, 1, 1, 7, 2, 2, 1, 1, 4]
def baseStart_1909360 : Nat := 118140960795 + 1909360 * 2 ^ 59
def prefixEnd_1909360 : Nat := 4983230072969 + 3 ^ 40 * 1909360 * 2
def baseEnd_1909360 : Nat := 653612948312503235946013

theorem tailTrace_1909360 : CollatzResearch.WordTrace tailWord_1909360 prefixEnd_1909360 653612948312503235946013 := by
  unfold tailWord_1909360
  simp only [CollatzResearch.WordTrace]
  refine ⟨34820040181361143785770767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46426720241814858381027689 34820040181361143785770767)
  ·
    refine ⟨52230060272041715678656151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34820040181361143785770767 52230060272041715678656151)
    ·
      refine ⟨78345090408062573517984227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52230060272041715678656151 78345090408062573517984227)
      ·
        refine ⟨117517635612093860276976341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78345090408062573517984227 117517635612093860276976341)
        ·
          refine ⟨2754319584658449850241633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 117517635612093860276976341 2754319584658449850241633)
          ·
            refine ⟨2065739688493837387681225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2754319584658449850241633 2065739688493837387681225)
            ·
              refine ⟨1549304766370378040760919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2065739688493837387681225 1549304766370378040760919)
              ·
                refine ⟨2323957149555567061141379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1549304766370378040760919 2323957149555567061141379)
                ·
                  refine ⟨3485935724333350591712069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2323957149555567061141379 3485935724333350591712069)
                  ·
                    refine ⟨653612948312503235946013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3485935724333350591712069 653612948312503235946013)
                    ·
                      rfl

theorem cell22_1909360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 2, 1, 1, 4].length) (baseStart_1909360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1909360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1909360 prefixEnd_1909360 := by exact prefixLift 1909360
  have htrace : WordTrace (prefixWord ++ tailWord_1909360) baseStart_1909360 baseEnd_1909360 := by
    simpa [prefixWord, tailWord_1909360, baseEnd_1909360] using wordTrace_append hprefix tailTrace_1909360
  have hstable : (prefixWord ++ tailWord_1909360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909360).length < 2 ^ (prefixWord ++ tailWord_1909360).sum := by decide
  have hdescent : baseEnd_1909360 < baseStart_1909360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909369 : List Nat := [1, 2, 1, 3, 3, 3, 9]
def baseStart_1909369 : Nat := 118140960795 + 1909369 * 2 ^ 59
def prefixEnd_1909369 : Nat := 4983230072969 + 3 ^ 40 * 1909369 * 2
def baseEnd_1909369 : Nat := 24208001081349267128555

theorem tailTrace_1909369 : CollatzResearch.WordTrace tailWord_1909369 prefixEnd_1909369 24208001081349267128555 := by
  unfold tailWord_1909369
  simp only [CollatzResearch.WordTrace]
  refine ⟨69640408619689682108619161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46426939079793121405746107 69640408619689682108619161)
  ·
    refine ⟨52230306464767261581464371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69640408619689682108619161 52230306464767261581464371)
    ·
      refine ⟨78345459697150892372196557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52230306464767261581464371 78345459697150892372196557)
      ·
        refine ⟨29379547386431584639573709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78345459697150892372196557 29379547386431584639573709)
        ·
          refine ⟨11017330269911844239840141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29379547386431584639573709 11017330269911844239840141)
          ·
            refine ⟨4131498851216941589940053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11017330269911844239840141 4131498851216941589940053)
            ·
              refine ⟨24208001081349267128555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4131498851216941589940053 24208001081349267128555)
              ·
                rfl

theorem cell22_1909369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 9].length) (baseStart_1909369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1909369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1909369 prefixEnd_1909369 := by exact prefixLift 1909369
  have htrace : WordTrace (prefixWord ++ tailWord_1909369) baseStart_1909369 baseEnd_1909369 := by
    simpa [prefixWord, tailWord_1909369, baseEnd_1909369] using wordTrace_append hprefix tailTrace_1909369
  have hstable : (prefixWord ++ tailWord_1909369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909369).length < 2 ^ (prefixWord ++ tailWord_1909369).sum := by decide
  have hdescent : baseEnd_1909369 < baseStart_1909369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909373 : List Nat := [1, 4, 1, 1, 5, 1, 1, 1, 4, 3]
def baseStart_1909373 : Nat := 118140960795 + 1909373 * 2 ^ 59
def prefixEnd_1909373 : Nat := 4983230072969 + 3 ^ 40 * 1909373 * 2
def baseEnd_1909373 : Nat := 653617398478175535370973

theorem tailTrace_1909373 : CollatzResearch.WordTrace tailWord_1909373 prefixEnd_1909373 653617398478175535370973 := by
  unfold tailWord_1909373
  simp only [CollatzResearch.WordTrace]
  refine ⟨69640554511675190791764773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46427036341116793861176515 69640554511675190791764773)
  ·
    refine ⟨13057603970939098273455895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69640554511675190791764773 13057603970939098273455895)
    ·
      refine ⟨19586405956408647410183843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13057603970939098273455895 19586405956408647410183843)
      ·
        refine ⟨29379608934612971115275765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19586405956408647410183843 29379608934612971115275765)
        ·
          refine ⟨2754338337619966042057103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29379608934612971115275765 2754338337619966042057103)
          ·
            refine ⟨4131507506429949063085655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2754338337619966042057103 4131507506429949063085655)
            ·
              refine ⟨6197261259644923594628483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4131507506429949063085655 6197261259644923594628483)
              ·
                refine ⟨9295891889467385391942725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6197261259644923594628483 9295891889467385391942725)
                ·
                  refine ⟨1742979729275134760989261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9295891889467385391942725 1742979729275134760989261)
                  ·
                    refine ⟨653617398478175535370973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1742979729275134760989261 653617398478175535370973)
                    ·
                      rfl

theorem cell22_1909373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 1, 4, 3].length) (baseStart_1909373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1909373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1909373 prefixEnd_1909373 := by exact prefixLift 1909373
  have htrace : WordTrace (prefixWord ++ tailWord_1909373) baseStart_1909373 baseEnd_1909373 := by
    simpa [prefixWord, tailWord_1909373, baseEnd_1909373] using wordTrace_append hprefix tailTrace_1909373
  have hstable : (prefixWord ++ tailWord_1909373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909373).length < 2 ^ (prefixWord ++ tailWord_1909373).sum := by decide
  have hdescent : baseEnd_1909373 < baseStart_1909373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909390 : List Nat := [4, 1, 1, 3, 1, 1, 5, 1, 2, 3]
def baseStart_1909390 : Nat := 118140960795 + 1909390 * 2 ^ 59
def prefixEnd_1909390 : Nat := 4983230072969 + 3 ^ 40 * 1909390 * 2
def baseEnd_1909390 : Nat := 653623217925593157695921

theorem tailTrace_1909390 : CollatzResearch.WordTrace tailWord_1909390 prefixEnd_1909390 653623217925593157695921 := by
  unfold tailWord_1909390
  simp only [CollatzResearch.WordTrace]
  refine ⟨8705146819076700336891703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46427449701742401796755749 8705146819076700336891703)
  ·
    refine ⟨13057720228615050505337555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8705146819076700336891703 13057720228615050505337555)
    ·
      refine ⟨19586580342922575758006333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13057720228615050505337555 19586580342922575758006333)
      ·
        refine ⟨7344967628595965909252375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19586580342922575758006333 7344967628595965909252375)
        ·
          refine ⟨11017451442893948863878563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7344967628595965909252375 11017451442893948863878563)
          ·
            refine ⟨16526177164340923295817845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11017451442893948863878563 16526177164340923295817845)
            ·
              refine ⟨1549329109156961558982923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16526177164340923295817845 1549329109156961558982923)
              ·
                refine ⟨2323993663735442338474385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1549329109156961558982923 2323993663735442338474385)
                ·
                  refine ⟨1742995247801581753855789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2323993663735442338474385 1742995247801581753855789)
                  ·
                    refine ⟨653623217925593157695921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1742995247801581753855789 653623217925593157695921)
                    ·
                      rfl

theorem cell22_1909390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 5, 1, 2, 3].length) (baseStart_1909390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1909390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1909390 prefixEnd_1909390 := by exact prefixLift 1909390
  have htrace : WordTrace (prefixWord ++ tailWord_1909390) baseStart_1909390 baseEnd_1909390 := by
    simpa [prefixWord, tailWord_1909390, baseEnd_1909390] using wordTrace_append hprefix tailTrace_1909390
  have hstable : (prefixWord ++ tailWord_1909390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909390).length < 2 ^ (prefixWord ++ tailWord_1909390).sum := by decide
  have hdescent : baseEnd_1909390 < baseStart_1909390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909401 : List Nat := [1, 2, 1, 2, 1, 2, 3, 4, 3, 3]
def baseStart_1909401 : Nat := 118140960795 + 1909401 * 2 ^ 59
def prefixEnd_1909401 : Nat := 4983230072969 + 3 ^ 40 * 1909401 * 2
def baseEnd_1909401 : Nat := 653626983450392795670887

theorem tailTrace_1909401 : CollatzResearch.WordTrace tailWord_1909401 prefixEnd_1909401 653626983450392795670887 := by
  unfold tailWord_1909401
  simp only [CollatzResearch.WordTrace]
  refine ⟨69641575755573751573784057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46427717170382501049189371 69641575755573751573784057)
  ·
    refine ⟨52231181816680313680338043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69641575755573751573784057 52231181816680313680338043)
    ·
      refine ⟨78346772725020470520507065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52231181816680313680338043 78346772725020470520507065)
      ·
        refine ⟨58760079543765352890380299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78346772725020470520507065 58760079543765352890380299)
        ·
          refine ⟨88140119315648029335570449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58760079543765352890380299 88140119315648029335570449)
          ·
            refine ⟨66105089486736022001677837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88140119315648029335570449 66105089486736022001677837)
            ·
              refine ⟨24789408557526008250629189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66105089486736022001677837 24789408557526008250629189)
              ·
                refine ⟨4648014104536126546992973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24789408557526008250629189 4648014104536126546992973)
                ·
                  refine ⟨1743005289201047455122365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4648014104536126546992973 1743005289201047455122365)
                  ·
                    refine ⟨653626983450392795670887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1743005289201047455122365 653626983450392795670887)
                    ·
                      rfl

theorem cell22_1909401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 4, 3, 3].length) (baseStart_1909401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1909401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1909401 prefixEnd_1909401 := by exact prefixLift 1909401
  have htrace : WordTrace (prefixWord ++ tailWord_1909401) baseStart_1909401 baseEnd_1909401 := by
    simpa [prefixWord, tailWord_1909401, baseEnd_1909401] using wordTrace_append hprefix tailTrace_1909401
  have hstable : (prefixWord ++ tailWord_1909401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909401).length < 2 ^ (prefixWord ++ tailWord_1909401).sum := by decide
  have hdescent : baseEnd_1909401 < baseStart_1909401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909441 : List Nat := [1, 2, 6, 2, 2, 1, 2, 1, 2, 3]
def baseStart_1909441 : Nat := 118140960795 + 1909441 * 2 ^ 59
def prefixEnd_1909441 : Nat := 4983230072969 + 3 ^ 40 * 1909441 * 2
def baseEnd_1909441 : Nat := 653640676267846024670765

theorem tailTrace_1909441 : CollatzResearch.WordTrace tailWord_1909441 prefixEnd_1909441 653640676267846024670765 := by
  unfold tailWord_1909441
  simp only [CollatzResearch.WordTrace]
  refine ⟨69643034675428838405240177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46428689783619225603493451 69643034675428838405240177)
  ·
    refine ⟨52232276006571628803930133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69643034675428838405240177 52232276006571628803930133)
    ·
      refine ⟨2448387937808045100184225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 52232276006571628803930133 2448387937808045100184225)
      ·
        refine ⟨1836290953356033825138169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2448387937808045100184225 1836290953356033825138169)
        ·
          refine ⟨1377218215017025368853627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1836290953356033825138169 1377218215017025368853627)
          ·
            refine ⟨2065827322525538053280441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1377218215017025368853627 2065827322525538053280441)
            ·
              refine ⟨1549370491894153539960331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2065827322525538053280441 1549370491894153539960331)
              ·
                refine ⟨2324055737841230309940497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1549370491894153539960331 2324055737841230309940497)
                ·
                  refine ⟨1743041803380922732455373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2324055737841230309940497 1743041803380922732455373)
                  ·
                    refine ⟨653640676267846024670765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1743041803380922732455373 653640676267846024670765)
                    ·
                      rfl

theorem cell22_1909441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_1909441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1909441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1909441 prefixEnd_1909441 := by exact prefixLift 1909441
  have htrace : WordTrace (prefixWord ++ tailWord_1909441) baseStart_1909441 baseEnd_1909441 := by
    simpa [prefixWord, tailWord_1909441, baseEnd_1909441] using wordTrace_append hprefix tailTrace_1909441
  have hstable : (prefixWord ++ tailWord_1909441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909441).length < 2 ^ (prefixWord ++ tailWord_1909441).sum := by decide
  have hdescent : baseEnd_1909441 < baseStart_1909441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909448 : List Nat := [2, 1, 3, 1, 2, 3, 4, 1, 5]
def baseStart_1909448 : Nat := 118140960795 + 1909448 * 2 ^ 59
def prefixEnd_1909448 : Nat := 4983230072969 + 3 ^ 40 * 1909448 * 2
def baseEnd_1909448 : Nat := 217881024170300113248581

theorem tailTrace_1909448 : CollatzResearch.WordTrace tailWord_1909448 prefixEnd_1909448 217881024170300113248581 := by
  unfold tailWord_1909448
  simp only [CollatzResearch.WordTrace]
  refine ⟨34821644993201739300372499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46428859990935652400496665 34821644993201739300372499)
  ·
    refine ⟨52232467489802608950558749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34821644993201739300372499 52232467489802608950558749)
    ·
      refine ⟨19587175308675978356459531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52232467489802608950558749 19587175308675978356459531)
      ·
        refine ⟨29380762963013967534689297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19587175308675978356459531 29380762963013967534689297)
        ·
          refine ⟨22035572222260475651016973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29380762963013967534689297 22035572222260475651016973)
          ·
            refine ⟨8263339583347678369131365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22035572222260475651016973 8263339583347678369131365)
            ·
              refine ⟨1549376171877689694212131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8263339583347678369131365 1549376171877689694212131)
              ·
                refine ⟨2324064257816534541318197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1549376171877689694212131 2324064257816534541318197)
                ·
                  refine ⟨217881024170300113248581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2324064257816534541318197 217881024170300113248581)
                  ·
                    rfl

theorem cell22_1909448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 4, 1, 5].length) (baseStart_1909448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1909448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1909448 prefixEnd_1909448 := by exact prefixLift 1909448
  have htrace : WordTrace (prefixWord ++ tailWord_1909448) baseStart_1909448 baseEnd_1909448 := by
    simpa [prefixWord, tailWord_1909448, baseEnd_1909448] using wordTrace_append hprefix tailTrace_1909448
  have hstable : (prefixWord ++ tailWord_1909448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909448).length < 2 ^ (prefixWord ++ tailWord_1909448).sum := by decide
  have hdescent : baseEnd_1909448 < baseStart_1909448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909508 : List Nat := [2, 3, 2, 2, 1, 1, 4, 1, 1, 5]
def baseStart_1909508 : Nat := 118140960795 + 1909508 * 2 ^ 59
def prefixEnd_1909508 : Nat := 4983230072969 + 3 ^ 40 * 1909508 * 2
def baseEnd_1909508 : Nat := 653663611737080183245559

theorem tailTrace_1909508 : CollatzResearch.WordTrace tailWord_1909508 prefixEnd_1909508 653663611737080183245559 := by
  unfold tailWord_1909508
  simp only [CollatzResearch.WordTrace]
  refine ⟨34822739183093054423964589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46430318910790739231952785 34822739183093054423964589)
  ·
    refine ⟨13058527193659895408986721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34822739183093054423964589 13058527193659895408986721)
    ·
      refine ⟨9793895395244921556740041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13058527193659895408986721 9793895395244921556740041)
      ·
        refine ⟨7345421546433691167555031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9793895395244921556740041 7345421546433691167555031)
        ·
          refine ⟨11018132319650536751332547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7345421546433691167555031 11018132319650536751332547)
          ·
            refine ⟨16527198479475805126998821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11018132319650536751332547 16527198479475805126998821)
            ·
              refine ⟨3098849714901713461312279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16527198479475805126998821 3098849714901713461312279)
              ·
                refine ⟨4648274572352570191968419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3098849714901713461312279 4648274572352570191968419)
                ·
                  refine ⟨6972411858528855287952629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4648274572352570191968419 6972411858528855287952629)
                  ·
                    refine ⟨653663611737080183245559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6972411858528855287952629 653663611737080183245559)
                    ·
                      rfl

theorem cell22_1909508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_1909508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1909508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1909508 prefixEnd_1909508 := by exact prefixLift 1909508
  have htrace : WordTrace (prefixWord ++ tailWord_1909508) baseStart_1909508 baseEnd_1909508 := by
    simpa [prefixWord, tailWord_1909508, baseEnd_1909508] using wordTrace_append hprefix tailTrace_1909508
  have hstable : (prefixWord ++ tailWord_1909508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909508).length < 2 ^ (prefixWord ++ tailWord_1909508).sum := by decide
  have hdescent : baseEnd_1909508 < baseStart_1909508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909604 : List Nat := [2, 3, 1, 1, 4, 2, 3, 2, 1, 3]
def baseStart_1909604 : Nat := 118140960795 + 1909604 * 2 ^ 59
def prefixEnd_1909604 : Nat := 4983230072969 + 3 ^ 40 * 1909604 * 2
def baseEnd_1909604 : Nat := 653696474498967932845265

theorem tailTrace_1909604 : CollatzResearch.WordTrace tailWord_1909604 prefixEnd_1909604 653696474498967932845265 := by
  unfold tailWord_1909604
  simp only [CollatzResearch.WordTrace]
  refine ⟨34824489886919158621711933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46432653182558878162282577 34824489886919158621711933)
  ·
    refine ⟨13059183707594684483141975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34824489886919158621711933 13059183707594684483141975)
    ·
      refine ⟨19588775561392026724712963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13059183707594684483141975 19588775561392026724712963)
      ·
        refine ⟨29383163342088040087069445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19588775561392026724712963 29383163342088040087069445)
        ·
          refine ⟨5509343126641507516325521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29383163342088040087069445 5509343126641507516325521)
          ·
            refine ⟨4132007344981130637244141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5509343126641507516325521 4132007344981130637244141)
            ·
              refine ⟨1549502754367923988966553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4132007344981130637244141 1549502754367923988966553)
              ·
                refine ⟨1162127065775942991724915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1549502754367923988966553 1162127065775942991724915)
                ·
                  refine ⟨1743190598663914487587373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1162127065775942991724915 1743190598663914487587373)
                  ·
                    refine ⟨653696474498967932845265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1743190598663914487587373 653696474498967932845265)
                    ·
                      rfl

theorem cell22_1909604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 3, 2, 1, 3].length) (baseStart_1909604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1909604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1909604 prefixEnd_1909604 := by exact prefixLift 1909604
  have htrace : WordTrace (prefixWord ++ tailWord_1909604) baseStart_1909604 baseEnd_1909604 := by
    simpa [prefixWord, tailWord_1909604, baseEnd_1909604] using wordTrace_append hprefix tailTrace_1909604
  have hstable : (prefixWord ++ tailWord_1909604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909604).length < 2 ^ (prefixWord ++ tailWord_1909604).sum := by decide
  have hdescent : baseEnd_1909604 < baseStart_1909604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909613 : List Nat := [1, 5, 1, 1, 1, 1, 1, 4, 3, 4]
def baseStart_1909613 : Nat := 118140960795 + 1909613 * 2 ^ 59
def prefixEnd_1909613 : Nat := 4983230072969 + 3 ^ 40 * 1909613 * 2
def baseEnd_1909613 : Nat := 653699555382894909370237

theorem tailTrace_1909613 : CollatzResearch.WordTrace tailWord_1909613 prefixEnd_1909613 653699555382894909370237 := by
  unfold tailWord_1909613
  simp only [CollatzResearch.WordTrace]
  refine ⟨69649308030805711780501493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46432872020537141187000995 69649308030805711780501493)
  ·
    refine ⟨6529622627888035479422015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69649308030805711780501493 6529622627888035479422015)
    ·
      refine ⟨9794433941832053219133023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6529622627888035479422015 9794433941832053219133023)
      ·
        refine ⟨14691650912748079828699535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9794433941832053219133023 14691650912748079828699535)
        ·
          refine ⟨22037476369122119743049303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14691650912748079828699535 22037476369122119743049303)
          ·
            refine ⟨33056214553683179614573955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22037476369122119743049303 33056214553683179614573955)
            ·
              refine ⟨49584321830524769421860933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33056214553683179614573955 49584321830524769421860933)
              ·
                refine ⟨9297060343223394266598925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49584321830524769421860933 9297060343223394266598925)
                ·
                  refine ⟨3486397628708772849974597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9297060343223394266598925 3486397628708772849974597)
                  ·
                    refine ⟨653699555382894909370237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3486397628708772849974597 653699555382894909370237)
                    ·
                      rfl

theorem cell22_1909613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_1909613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1909613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1909613 prefixEnd_1909613 := by exact prefixLift 1909613
  have htrace : WordTrace (prefixWord ++ tailWord_1909613) baseStart_1909613 baseEnd_1909613 := by
    simpa [prefixWord, tailWord_1909613, baseEnd_1909613] using wordTrace_append hprefix tailTrace_1909613
  have hstable : (prefixWord ++ tailWord_1909613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909613).length < 2 ^ (prefixWord ++ tailWord_1909613).sum := by decide
  have hdescent : baseEnd_1909613 < baseStart_1909613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909643 : List Nat := [1, 1, 1, 1, 4, 2, 2, 1, 6, 3]
def baseStart_1909643 : Nat := 118140960795 + 1909643 * 2 ^ 59
def prefixEnd_1909643 : Nat := 4983230072969 + 3 ^ 40 * 1909643 * 2
def baseEnd_1909643 : Nat := 653709824995984831120145

theorem tailTrace_1909643 : CollatzResearch.WordTrace tailWord_1909643 prefixEnd_1909643 653709824995984831120145 := by
  unfold tailWord_1909643
  simp only [CollatzResearch.WordTrace]
  refine ⟨69650402220697026904093583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46433601480464684602729055 69650402220697026904093583)
  ·
    refine ⟨104475603331045540356140375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69650402220697026904093583 104475603331045540356140375)
    ·
      refine ⟨156713404996568310534210563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104475603331045540356140375 156713404996568310534210563)
      ·
        refine ⟨235070107494852465801315845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156713404996568310534210563 235070107494852465801315845)
        ·
          refine ⟨44075645155284837337746721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 235070107494852465801315845 44075645155284837337746721)
          ·
            refine ⟨33056733866463628003310041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44075645155284837337746721 33056733866463628003310041)
            ·
              refine ⟨24792550399847721002482531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33056733866463628003310041 24792550399847721002482531)
              ·
                refine ⟨37188825599771581503723797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24792550399847721002482531 37188825599771581503723797)
                ·
                  refine ⟨1743226199989292882987053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 37188825599771581503723797 1743226199989292882987053)
                  ·
                    refine ⟨653709824995984831120145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1743226199989292882987053 653709824995984831120145)
                    ·
                      rfl

theorem cell22_1909643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 6, 3].length) (baseStart_1909643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1909643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1909643 prefixEnd_1909643 := by exact prefixLift 1909643
  have htrace : WordTrace (prefixWord ++ tailWord_1909643) baseStart_1909643 baseEnd_1909643 := by
    simpa [prefixWord, tailWord_1909643, baseEnd_1909643] using wordTrace_append hprefix tailTrace_1909643
  have hstable : (prefixWord ++ tailWord_1909643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909643).length < 2 ^ (prefixWord ++ tailWord_1909643).sum := by decide
  have hdescent : baseEnd_1909643 < baseStart_1909643 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909656 : List Nat := [2, 1, 2, 17]
def baseStart_1909656 : Nat := 118140960795 + 1909656 * 2 ^ 59
def prefixEnd_1909656 : Nat := 4983230072969 + 3 ^ 40 * 1909656 * 2
def baseEnd_1909656 : Nat := 896727400770448738745

theorem tailTrace_1909656 : CollatzResearch.WordTrace tailWord_1909656 prefixEnd_1909656 896727400770448738745 := by
  unfold tailWord_1909656
  simp only [CollatzResearch.WordTrace]
  refine ⟨34825438184824965062158411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46433917579766620082877881 34825438184824965062158411)
  ·
    refine ⟨52238157277237447593237617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34825438184824965062158411 52238157277237447593237617)
    ·
      refine ⟨39178617957928085694928213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52238157277237447593237617 39178617957928085694928213)
      ·
        refine ⟨896727400770448738745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 17 39178617957928085694928213 896727400770448738745)
        ·
          rfl

theorem cell22_1909656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 17].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 17].length) (baseStart_1909656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1909656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1909656 prefixEnd_1909656 := by exact prefixLift 1909656
  have htrace : WordTrace (prefixWord ++ tailWord_1909656) baseStart_1909656 baseEnd_1909656 := by
    simpa [prefixWord, tailWord_1909656, baseEnd_1909656] using wordTrace_append hprefix tailTrace_1909656
  have hstable : (prefixWord ++ tailWord_1909656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909656).length < 2 ^ (prefixWord ++ tailWord_1909656).sum := by decide
  have hdescent : baseEnd_1909656 < baseStart_1909656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909722 : List Nat := [3, 1, 1, 2, 4, 2, 2, 1, 3, 3]
def baseStart_1909722 : Nat := 118140960795 + 1909722 * 2 ^ 59
def prefixEnd_1909722 : Nat := 4983230072969 + 3 ^ 40 * 1909722 * 2
def baseEnd_1909722 : Nat := 653736868310454958394903

theorem tailTrace_1909722 : CollatzResearch.WordTrace tailWord_1909722 prefixEnd_1909722 653736868310454958394903 := by
  unfold tailWord_1909722
  simp only [CollatzResearch.WordTrace]
  refine ⟨17413320896852705849054855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46435522391607215597479613 17413320896852705849054855)
  ·
    refine ⟨26119981345279058773582283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17413320896852705849054855 26119981345279058773582283)
    ·
      refine ⟨39179972017918588160373425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26119981345279058773582283 39179972017918588160373425)
      ·
        refine ⟨29384979013438941120280069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39179972017918588160373425 29384979013438941120280069)
        ·
          refine ⟨5509683565019801460052513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29384979013438941120280069 5509683565019801460052513)
          ·
            refine ⟨4132262673764851095039385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5509683565019801460052513 4132262673764851095039385)
            ·
              refine ⟨3099197005323638321279539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4132262673764851095039385 3099197005323638321279539)
              ·
                refine ⟨4648795507985457481919309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3099197005323638321279539 4648795507985457481919309)
                ·
                  refine ⟨1743298315494546555719741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4648795507985457481919309 1743298315494546555719741)
                  ·
                    refine ⟨653736868310454958394903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1743298315494546555719741 653736868310454958394903)
                    ·
                      rfl

theorem cell22_1909722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 1, 3, 3].length) (baseStart_1909722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1909722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1909722 prefixEnd_1909722 := by exact prefixLift 1909722
  have htrace : WordTrace (prefixWord ++ tailWord_1909722) baseStart_1909722 baseEnd_1909722 := by
    simpa [prefixWord, tailWord_1909722, baseEnd_1909722] using wordTrace_append hprefix tailTrace_1909722
  have hstable : (prefixWord ++ tailWord_1909722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909722).length < 2 ^ (prefixWord ++ tailWord_1909722).sum := by decide
  have hdescent : baseEnd_1909722 < baseStart_1909722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909765 : List Nat := [1, 3, 1, 1, 2, 3, 1, 5, 1, 4]
def baseStart_1909765 : Nat := 118140960795 + 1909765 * 2 ^ 59
def prefixEnd_1909765 : Nat := 4983230072969 + 3 ^ 40 * 1909765 * 2
def baseEnd_1909765 : Nat := 653751588089217179569771

theorem tailTrace_1909765 : CollatzResearch.WordTrace tailWord_1909765 prefixEnd_1909765 653751588089217179569771 := by
  unfold tailWord_1909765
  simp only [CollatzResearch.WordTrace]
  refine ⟨69654851926255041740034749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46436567950836694493356499 69654851926255041740034749)
  ·
    refine ⟨26120569472345640652513031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69654851926255041740034749 26120569472345640652513031)
    ·
      refine ⟨39180854208518460978769547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26120569472345640652513031 39180854208518460978769547)
      ·
        refine ⟨58771281312777691468154321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39180854208518460978769547 58771281312777691468154321)
        ·
          refine ⟨44078460984583268601115741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58771281312777691468154321 44078460984583268601115741)
          ·
            refine ⟨16529422869218725725418403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44078460984583268601115741 16529422869218725725418403)
            ·
              refine ⟨24794134303828088588127605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16529422869218725725418403 24794134303828088588127605)
              ·
                refine ⟨2324450090983883305136963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24794134303828088588127605 2324450090983883305136963)
                ·
                  refine ⟨3486675136475824957705445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2324450090983883305136963 3486675136475824957705445)
                  ·
                    refine ⟨653751588089217179569771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3486675136475824957705445 653751588089217179569771)
                    ·
                      rfl

theorem cell22_1909765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 5, 1, 4].length) (baseStart_1909765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1909765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1909765 prefixEnd_1909765 := by exact prefixLift 1909765
  have htrace : WordTrace (prefixWord ++ tailWord_1909765) baseStart_1909765 baseEnd_1909765 := by
    simpa [prefixWord, tailWord_1909765, baseEnd_1909765] using wordTrace_append hprefix tailTrace_1909765
  have hstable : (prefixWord ++ tailWord_1909765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909765).length < 2 ^ (prefixWord ++ tailWord_1909765).sum := by decide
  have hdescent : baseEnd_1909765 < baseStart_1909765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909799 : List Nat := [1, 1, 7, 1, 1, 1, 3, 2, 1, 4]
def baseStart_1909799 : Nat := 118140960795 + 1909799 * 2 ^ 59
def prefixEnd_1909799 : Nat := 4983230072969 + 3 ^ 40 * 1909799 * 2
def baseEnd_1909799 : Nat := 653763226984052424219667

theorem tailTrace_1909799 : CollatzResearch.WordTrace tailWord_1909799 prefixEnd_1909799 653763226984052424219667 := by
  unfold tailWord_1909799
  simp only [CollatzResearch.WordTrace]
  refine ⟨69656092008131865546772451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46437394672087910364514967 69656092008131865546772451)
  ·
    refine ⟨104484138012197798320158677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69656092008131865546772451 104484138012197798320158677)
    ·
      refine ⟨2448846984660885898128719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 104484138012197798320158677 2448846984660885898128719)
      ·
        refine ⟨3673270476991328847193079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2448846984660885898128719 3673270476991328847193079)
        ·
          refine ⟨5509905715486993270789619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3673270476991328847193079 5509905715486993270789619)
          ·
            refine ⟨8264858573230489906184429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5509905715486993270789619 8264858573230489906184429)
            ·
              refine ⟨3099321964961433714819161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8264858573230489906184429 3099321964961433714819161)
              ·
                refine ⟨2324491473721075286114371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3099321964961433714819161 2324491473721075286114371)
                ·
                  refine ⟨3486737210581612929171557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2324491473721075286114371 3486737210581612929171557)
                  ·
                    refine ⟨653763226984052424219667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3486737210581612929171557 653763226984052424219667)
                    ·
                      rfl

theorem cell22_1909799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_1909799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1909799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1909799 prefixEnd_1909799 := by exact prefixLift 1909799
  have htrace : WordTrace (prefixWord ++ tailWord_1909799) baseStart_1909799 baseEnd_1909799 := by
    simpa [prefixWord, tailWord_1909799, baseEnd_1909799] using wordTrace_append hprefix tailTrace_1909799
  have hstable : (prefixWord ++ tailWord_1909799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909799).length < 2 ^ (prefixWord ++ tailWord_1909799).sum := by decide
  have hdescent : baseEnd_1909799 < baseStart_1909799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909808 : List Nat := [2, 1, 1, 1, 2, 4, 1, 10]
def baseStart_1909808 : Nat := 118140960795 + 1909808 * 2 ^ 59
def prefixEnd_1909808 : Nat := 4983230072969 + 3 ^ 40 * 1909808 * 2
def baseEnd_1909808 : Nat := 72640700874219933416071

theorem tailTrace_1909808 : CollatzResearch.WordTrace tailWord_1909808 prefixEnd_1909808 72640700874219933416071 := by
  unfold tailWord_1909808
  simp only [CollatzResearch.WordTrace]
  refine ⟨34828210132549630041925039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46437613510066173389233385 34828210132549630041925039)
  ·
    refine ⟨52242315198824445062887559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34828210132549630041925039 52242315198824445062887559)
    ·
      refine ⟨78363472798236667594331339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52242315198824445062887559 78363472798236667594331339)
      ·
        refine ⟨117545209197355001391497009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78363472798236667594331339 117545209197355001391497009)
        ·
          refine ⟨88158906898016251043622757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117545209197355001391497009 88158906898016251043622757)
          ·
            refine ⟨16529795043378047070679267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88158906898016251043622757 16529795043378047070679267)
            ·
              refine ⟨24794692565067070606018901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16529795043378047070679267 24794692565067070606018901)
              ·
                refine ⟨72640700874219933416071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 24794692565067070606018901 72640700874219933416071)
                ·
                  rfl

theorem cell22_1909808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 10].length) (baseStart_1909808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1909808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1909808 prefixEnd_1909808 := by exact prefixLift 1909808
  have htrace : WordTrace (prefixWord ++ tailWord_1909808) baseStart_1909808 baseEnd_1909808 := by
    simpa [prefixWord, tailWord_1909808, baseEnd_1909808] using wordTrace_append hprefix tailTrace_1909808
  have hstable : (prefixWord ++ tailWord_1909808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909808).length < 2 ^ (prefixWord ++ tailWord_1909808).sum := by decide
  have hdescent : baseEnd_1909808 < baseStart_1909808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909812 : List Nat := [2, 5, 1, 2, 1, 1, 1, 1, 3, 5]
def baseStart_1909812 : Nat := 118140960795 + 1909812 * 2 ^ 59
def prefixEnd_1909812 : Nat := 4983230072969 + 3 ^ 40 * 1909812 * 2
def baseEnd_1909812 : Nat := 653767677149724723644627

theorem tailTrace_1909812 : CollatzResearch.WordTrace tailWord_1909812 prefixEnd_1909812 653767677149724723644627 := by
  unfold tailWord_1909812
  simp only [CollatzResearch.WordTrace]
  refine ⟨34828283078542384383497845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46437710771389845844663793 34828283078542384383497845)
  ·
    refine ⟨3265151538613348535952923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34828283078542384383497845 3265151538613348535952923)
    ·
      refine ⟨4897727307920022803929385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3265151538613348535952923 4897727307920022803929385)
      ·
        refine ⟨3673295480940017102947039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4897727307920022803929385 3673295480940017102947039)
        ·
          refine ⟨5509943221410025654420559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3673295480940017102947039 5509943221410025654420559)
          ·
            refine ⟨8264914832115038481630839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5509943221410025654420559 8264914832115038481630839)
            ·
              refine ⟨12397372248172557722446259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8264914832115038481630839 12397372248172557722446259)
              ·
                refine ⟨18596058372258836583669389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12397372248172557722446259 18596058372258836583669389)
                ·
                  refine ⟨6973521889597063718876021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18596058372258836583669389 6973521889597063718876021)
                  ·
                    refine ⟨653767677149724723644627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6973521889597063718876021 653767677149724723644627)
                    ·
                      rfl

theorem cell22_1909812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_1909812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1909812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1909812 prefixEnd_1909812 := by exact prefixLift 1909812
  have htrace : WordTrace (prefixWord ++ tailWord_1909812) baseStart_1909812 baseEnd_1909812 := by
    simpa [prefixWord, tailWord_1909812, baseEnd_1909812] using wordTrace_append hprefix tailTrace_1909812
  have hstable : (prefixWord ++ tailWord_1909812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909812).length < 2 ^ (prefixWord ++ tailWord_1909812).sum := by decide
  have hdescent : baseEnd_1909812 < baseStart_1909812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909825 : List Nat := [1, 2, 5, 1, 3, 10]
def baseStart_1909825 : Nat := 118140960795 + 1909825 * 2 ^ 59
def prefixEnd_1909825 : Nat := 4983230072969 + 3 ^ 40 * 1909825 * 2
def baseEnd_1909825 : Nat := 8071260831054284235427

theorem tailTrace_1909825 : CollatzResearch.WordTrace tailWord_1909825 prefixEnd_1909825 8071260831054284235427 := by
  unfold tailWord_1909825
  simp only [CollatzResearch.WordTrace]
  refine ⟨69657040306037671987218929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46438026870691781324812619 69657040306037671987218929)
  ·
    refine ⟨52242780229528253990414197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69657040306037671987218929 52242780229528253990414197)
    ·
      refine ⟨4897760646518273811601331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52242780229528253990414197 4897760646518273811601331)
      ·
        refine ⟨7346640969777410717401997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4897760646518273811601331 7346640969777410717401997)
        ·
          refine ⟨2754990363666529019025749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7346640969777410717401997 2754990363666529019025749)
          ·
            refine ⟨8071260831054284235427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2754990363666529019025749 8071260831054284235427)
            ·
              rfl

theorem cell22_1909825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 10].length) (baseStart_1909825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1909825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1909825 prefixEnd_1909825 := by exact prefixLift 1909825
  have htrace : WordTrace (prefixWord ++ tailWord_1909825) baseStart_1909825 baseEnd_1909825 := by
    simpa [prefixWord, tailWord_1909825, baseEnd_1909825] using wordTrace_append hprefix tailTrace_1909825
  have hstable : (prefixWord ++ tailWord_1909825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909825).length < 2 ^ (prefixWord ++ tailWord_1909825).sum := by decide
  have hdescent : baseEnd_1909825 < baseStart_1909825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909840 : List Nat := [2, 1, 1, 1, 1, 3, 1, 2, 7, 3]
def baseStart_1909840 : Nat := 118140960795 + 1909840 * 2 ^ 59
def prefixEnd_1909840 : Nat := 4983230072969 + 3 ^ 40 * 1909840 * 2
def baseEnd_1909840 : Nat := 653777262121941983944541

theorem tailTrace_1909840 : CollatzResearch.WordTrace tailWord_1909840 prefixEnd_1909840 653777262121941983944541 := by
  unfold tailWord_1909840
  simp only [CollatzResearch.WordTrace]
  refine ⟨34828793700491664774507487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46438391600655553032676649 34828793700491664774507487)
  ·
    refine ⟨52243190550737497161761231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34828793700491664774507487 52243190550737497161761231)
    ·
      refine ⟨78364785826106245742641847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52243190550737497161761231 78364785826106245742641847)
      ·
        refine ⟨117547178739159368613962771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78364785826106245742641847 117547178739159368613962771)
        ·
          refine ⟨176320768108739052920944157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117547178739159368613962771 176320768108739052920944157)
          ·
            refine ⟨66120288040777144845354059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176320768108739052920944157 66120288040777144845354059)
            ·
              refine ⟨99180432061165717268031089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66120288040777144845354059 99180432061165717268031089)
              ·
                refine ⟨74385324045874287951023317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99180432061165717268031089 74385324045874287951023317)
                ·
                  refine ⟨1743406032325178623852109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 74385324045874287951023317 1743406032325178623852109)
                  ·
                    refine ⟨653777262121941983944541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1743406032325178623852109 653777262121941983944541)
                    ·
                      rfl

theorem cell22_1909840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 7, 3].length) (baseStart_1909840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1909840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1909840 prefixEnd_1909840 := by exact prefixLift 1909840
  have htrace : WordTrace (prefixWord ++ tailWord_1909840) baseStart_1909840 baseEnd_1909840 := by
    simpa [prefixWord, tailWord_1909840, baseEnd_1909840] using wordTrace_append hprefix tailTrace_1909840
  have hstable : (prefixWord ++ tailWord_1909840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909840).length < 2 ^ (prefixWord ++ tailWord_1909840).sum := by decide
  have hdescent : baseEnd_1909840 < baseStart_1909840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909842 : List Nat := [3, 2, 2, 1, 3, 3, 1, 7]
def baseStart_1909842 : Nat := 118140960795 + 1909842 * 2 ^ 59
def prefixEnd_1909842 : Nat := 4983230072969 + 3 ^ 40 * 1909842 * 2
def baseEnd_1909842 : Nat := 72641994084757182821615

theorem tailTrace_1909842 : CollatzResearch.WordTrace tailWord_1909842 prefixEnd_1909842 72641994084757182821615 := by
  unfold tailWord_1909842
  simp only [CollatzResearch.WordTrace]
  refine ⟨17414415086744020972646945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46438440231317389260391853 17414415086744020972646945)
  ·
    refine ⟨13060811315058015729485209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17414415086744020972646945 13060811315058015729485209)
    ·
      refine ⟨9795608486293511797113907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13060811315058015729485209 9795608486293511797113907)
      ·
        refine ⟨14693412729440267695670861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9795608486293511797113907 14693412729440267695670861)
        ·
          refine ⟨5510029773540100385876573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14693412729440267695670861 5510029773540100385876573)
          ·
            refine ⟨2066261165077537644703715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5510029773540100385876573 2066261165077537644703715)
            ·
              refine ⟨3099391747616306467055573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2066261165077537644703715 3099391747616306467055573)
              ·
                refine ⟨72641994084757182821615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3099391747616306467055573 72641994084757182821615)
                ·
                  rfl

theorem cell22_1909842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 7].length) (baseStart_1909842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1909842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1909842 prefixEnd_1909842 := by exact prefixLift 1909842
  have htrace : WordTrace (prefixWord ++ tailWord_1909842) baseStart_1909842 baseEnd_1909842 := by
    simpa [prefixWord, tailWord_1909842, baseEnd_1909842] using wordTrace_append hprefix tailTrace_1909842
  have hstable : (prefixWord ++ tailWord_1909842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909842).length < 2 ^ (prefixWord ++ tailWord_1909842).sum := by decide
  have hdescent : baseEnd_1909842 < baseStart_1909842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909846 : List Nat := [5, 2, 2, 1, 2, 1, 2, 1, 1, 5]
def baseStart_1909846 : Nat := 118140960795 + 1909846 * 2 ^ 59
def prefixEnd_1909846 : Nat := 4983230072969 + 3 ^ 40 * 1909846 * 2
def baseEnd_1909846 : Nat := 653779316044559968294523

theorem tailTrace_1909846 : CollatzResearch.WordTrace tailWord_1909846 prefixEnd_1909846 653779316044559968294523 := by
  unfold tailWord_1909846
  simp only [CollatzResearch.WordTrace]
  refine ⟨4353612889935099535858337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46438537492641061715822261 4353612889935099535858337)
  ·
    refine ⟨3265209667451324651893753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4353612889935099535858337 3265209667451324651893753)
    ·
      refine ⟨2448907250588493488920315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3265209667451324651893753 2448907250588493488920315)
      ·
        refine ⟨3673360875882740233380473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2448907250588493488920315 3673360875882740233380473)
        ·
          refine ⟨2755020656912055175035355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3673360875882740233380473 2755020656912055175035355)
          ·
            refine ⟨4132530985368082762553033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2755020656912055175035355 4132530985368082762553033)
            ·
              refine ⟨3099398239026062071914775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4132530985368082762553033 3099398239026062071914775)
              ·
                refine ⟨4649097358539093107872163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3099398239026062071914775 4649097358539093107872163)
                ·
                  refine ⟨6973646037808639661808245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4649097358539093107872163 6973646037808639661808245)
                  ·
                    refine ⟨653779316044559968294523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6973646037808639661808245 653779316044559968294523)
                    ·
                      rfl

theorem cell22_1909846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_1909846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1909846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1909846 prefixEnd_1909846 := by exact prefixLift 1909846
  have htrace : WordTrace (prefixWord ++ tailWord_1909846) baseStart_1909846 baseEnd_1909846 := by
    simpa [prefixWord, tailWord_1909846, baseEnd_1909846] using wordTrace_append hprefix tailTrace_1909846
  have hstable : (prefixWord ++ tailWord_1909846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909846).length < 2 ^ (prefixWord ++ tailWord_1909846).sum := by decide
  have hdescent : baseEnd_1909846 < baseStart_1909846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909885 : List Nat := [1, 4, 1, 1, 3, 1, 1, 1, 4, 5]
def baseStart_1909885 : Nat := 118140960795 + 1909885 * 2 ^ 59
def prefixEnd_1909885 : Nat := 4983230072969 + 3 ^ 40 * 1909885 * 2
def baseEnd_1909885 : Nat := 653792666541576866569403

theorem tailTrace_1909885 : CollatzResearch.WordTrace tailWord_1909885 prefixEnd_1909885 653792666541576866569403 := by
  unfold tailWord_1909885
  simp only [CollatzResearch.WordTrace]
  refine ⟨69659228685820302234403109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46439485790546868156268739 69659228685820302234403109)
  ·
    refine ⟨13061105378591306668950583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69659228685820302234403109 13061105378591306668950583)
    ·
      refine ⟨19591658067886960003425875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13061105378591306668950583 19591658067886960003425875)
      ·
        refine ⟨29387487101830440005138813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19591658067886960003425875 29387487101830440005138813)
        ·
          refine ⟨11020307663186415001927055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29387487101830440005138813 11020307663186415001927055)
          ·
            refine ⟨16530461494779622502890583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11020307663186415001927055 16530461494779622502890583)
            ·
              refine ⟨24795692242169433754335875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16530461494779622502890583 24795692242169433754335875)
              ·
                refine ⟨37193538363254150631503813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24795692242169433754335875 37193538363254150631503813)
                ·
                  refine ⟨6973788443110153243406965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37193538363254150631503813 6973788443110153243406965)
                  ·
                    refine ⟨653792666541576866569403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6973788443110153243406965 653792666541576866569403)
                    ·
                      rfl

theorem cell22_1909885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 4, 5].length) (baseStart_1909885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1909885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1909885 prefixEnd_1909885 := by exact prefixLift 1909885
  have htrace : WordTrace (prefixWord ++ tailWord_1909885) baseStart_1909885 baseEnd_1909885 := by
    simpa [prefixWord, tailWord_1909885, baseEnd_1909885] using wordTrace_append hprefix tailTrace_1909885
  have hstable : (prefixWord ++ tailWord_1909885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909885).length < 2 ^ (prefixWord ++ tailWord_1909885).sum := by decide
  have hdescent : baseEnd_1909885 < baseStart_1909885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909900 : List Nat := [2, 2, 1, 2, 1, 1, 1, 3, 5, 4]
def baseStart_1909900 : Nat := 118140960795 + 1909900 * 2 ^ 59
def prefixEnd_1909900 : Nat := 4983230072969 + 3 ^ 40 * 1909900 * 2
def baseEnd_1909900 : Nat := 653797801348121827444357

theorem tailTrace_1909900 : CollatzResearch.WordTrace tailWord_1909900 prefixEnd_1909900 653797801348121827444357 := by
  unfold tailWord_1909900
  simp only [CollatzResearch.WordTrace]
  refine ⟨34829887890382979898099577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46439850520510639864132769 34829887890382979898099577)
  ·
    refine ⟨26122415917787234923574683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34829887890382979898099577 26122415917787234923574683)
    ·
      refine ⟨39183623876680852385362025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26122415917787234923574683 39183623876680852385362025)
      ·
        refine ⟨29387717907510639289021519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39183623876680852385362025 29387717907510639289021519)
        ·
          refine ⟨44081576861265958933532279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29387717907510639289021519 44081576861265958933532279)
          ·
            refine ⟨66122365291898938400298419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44081576861265958933532279 66122365291898938400298419)
            ·
              refine ⟨99183547937848407600447629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66122365291898938400298419 99183547937848407600447629)
              ·
                refine ⟨37193830476693152850167861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99183547937848407600447629 37193830476693152850167861)
                ·
                  refine ⟨3486921607189983079703237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37193830476693152850167861 3486921607189983079703237)
                  ·
                    refine ⟨653797801348121827444357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3486921607189983079703237 653797801348121827444357)
                    ·
                      rfl

theorem cell22_1909900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 5, 4].length) (baseStart_1909900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1909900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1909900 prefixEnd_1909900 := by exact prefixLift 1909900
  have htrace : WordTrace (prefixWord ++ tailWord_1909900) baseStart_1909900 baseEnd_1909900 := by
    simpa [prefixWord, tailWord_1909900, baseEnd_1909900] using wordTrace_append hprefix tailTrace_1909900
  have hstable : (prefixWord ++ tailWord_1909900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909900).length < 2 ^ (prefixWord ++ tailWord_1909900).sum := by decide
  have hdescent : baseEnd_1909900 < baseStart_1909900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909902 : List Nat := [4, 1, 1, 3, 2, 1, 2, 1, 2, 5]
def baseStart_1909902 : Nat := 118140960795 + 1909902 * 2 ^ 59
def prefixEnd_1909902 : Nat := 4983230072969 + 3 ^ 40 * 1909902 * 2
def baseEnd_1909902 : Nat := 653798485988994488894351

theorem tailTrace_1909902 : CollatzResearch.WordTrace tailWord_1909902 prefixEnd_1909902 653798485988994488894351 := by
  unfold tailWord_1909902
  simp only [CollatzResearch.WordTrace]
  refine ⟨8707481090844839267221495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46439899151172476091847973 8707481090844839267221495)
  ·
    refine ⟨13061221636267258900832243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8707481090844839267221495 13061221636267258900832243)
    ·
      refine ⟨19591832454400888351248365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13061221636267258900832243 19591832454400888351248365)
      ·
        refine ⟨7346937170400333131718137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19591832454400888351248365 7346937170400333131718137)
        ·
          refine ⟨5510202877800249848788603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7346937170400333131718137 5510202877800249848788603)
          ·
            refine ⟨8265304316700374773182905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5510202877800249848788603 8265304316700374773182905)
            ·
              refine ⟨6198978237525281079887179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8265304316700374773182905 6198978237525281079887179)
              ·
                refine ⟨9298467356287921619830769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6198978237525281079887179 9298467356287921619830769)
                ·
                  refine ⟨6973850517215941214873077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9298467356287921619830769 6973850517215941214873077)
                  ·
                    refine ⟨653798485988994488894351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6973850517215941214873077 653798485988994488894351)
                    ·
                      rfl

theorem cell22_1909902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 1, 2, 5].length) (baseStart_1909902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1909902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1909902 prefixEnd_1909902 := by exact prefixLift 1909902
  have htrace : WordTrace (prefixWord ++ tailWord_1909902) baseStart_1909902 baseEnd_1909902 := by
    simpa [prefixWord, tailWord_1909902, baseEnd_1909902] using wordTrace_append hprefix tailTrace_1909902
  have hstable : (prefixWord ++ tailWord_1909902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909902).length < 2 ^ (prefixWord ++ tailWord_1909902).sum := by decide
  have hdescent : baseEnd_1909902 < baseStart_1909902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909932 : List Nat := [2, 2, 1, 1, 1, 1, 1, 9, 4]
def baseStart_1909932 : Nat := 118140960795 + 1909932 * 2 ^ 59
def prefixEnd_1909932 : Nat := 4983230072969 + 3 ^ 40 * 1909932 * 2
def baseEnd_1909932 : Nat := 217936251867361470214753

theorem tailTrace_1909932 : CollatzResearch.WordTrace tailWord_1909932 prefixEnd_1909932 217936251867361470214753 := by
  unfold tailWord_1909932
  simp only [CollatzResearch.WordTrace]
  refine ⟨34830471458325014630682025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46440628611100019507576033 34830471458325014630682025)
  ·
    refine ⟨26122853593743760973011519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34830471458325014630682025 26122853593743760973011519)
    ·
      refine ⟨39184280390615641459517279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26122853593743760973011519 39184280390615641459517279)
      ·
        refine ⟨58776420585923462189275919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39184280390615641459517279 58776420585923462189275919)
        ·
          refine ⟨88164630878885193283913879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58776420585923462189275919 88164630878885193283913879)
          ·
            refine ⟨132246946318327789925870819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88164630878885193283913879 132246946318327789925870819)
            ·
              refine ⟨198370419477491684888806229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132246946318327789925870819 198370419477491684888806229)
              ·
                refine ⟨1162326676625927841145349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 198370419477491684888806229 1162326676625927841145349)
                ·
                  refine ⟨217936251867361470214753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1162326676625927841145349 217936251867361470214753)
                  ·
                    rfl

theorem cell22_1909932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 9, 4].length) (baseStart_1909932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1909932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1909932 prefixEnd_1909932 := by exact prefixLift 1909932
  have htrace : WordTrace (prefixWord ++ tailWord_1909932) baseStart_1909932 baseEnd_1909932 := by
    simpa [prefixWord, tailWord_1909932, baseEnd_1909932] using wordTrace_append hprefix tailTrace_1909932
  have hstable : (prefixWord ++ tailWord_1909932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909932).length < 2 ^ (prefixWord ++ tailWord_1909932).sum := by decide
  have hdescent : baseEnd_1909932 < baseStart_1909932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909942 : List Nat := [5, 1, 3, 2, 1, 1, 3, 2, 1, 3]
def baseStart_1909942 : Nat := 118140960795 + 1909942 * 2 ^ 59
def prefixEnd_1909942 : Nat := 4983230072969 + 3 ^ 40 * 1909942 * 2
def baseEnd_1909942 : Nat := 653812178806447717894229

theorem tailTrace_1909942 : CollatzResearch.WordTrace tailWord_1909942 prefixEnd_1909942 653812178806447717894229 := by
  unfold tailWord_1909942
  simp only [CollatzResearch.WordTrace]
  refine ⟨4353831727913362560576755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46440871764409200646152053 4353831727913362560576755)
  ·
    refine ⟨6530747591870043840865133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4353831727913362560576755 6530747591870043840865133)
    ·
      refine ⟨2449030346951266440324425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6530747591870043840865133 2449030346951266440324425)
      ·
        refine ⟨1836772760213449830243319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2449030346951266440324425 1836772760213449830243319)
        ·
          refine ⟨2755159140320174745364979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1836772760213449830243319 2755159140320174745364979)
          ·
            refine ⟨4132738710480262118047469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2755159140320174745364979 4132738710480262118047469)
            ·
              refine ⟨1549777016430098294267801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4132738710480262118047469 1549777016430098294267801)
              ·
                refine ⟨1162332762322573720700851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1549777016430098294267801 1162332762322573720700851)
                ·
                  refine ⟨1743499143483860581051277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1162332762322573720700851 1743499143483860581051277)
                  ·
                    refine ⟨653812178806447717894229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1743499143483860581051277 653812178806447717894229)
                    ·
                      rfl

theorem cell22_1909942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_1909942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1909942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1909942 prefixEnd_1909942 := by exact prefixLift 1909942
  have htrace : WordTrace (prefixWord ++ tailWord_1909942) baseStart_1909942 baseEnd_1909942 := by
    simpa [prefixWord, tailWord_1909942, baseEnd_1909942] using wordTrace_append hprefix tailTrace_1909942
  have hstable : (prefixWord ++ tailWord_1909942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909942).length < 2 ^ (prefixWord ++ tailWord_1909942).sum := by decide
  have hdescent : baseEnd_1909942 < baseStart_1909942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909960 : List Nat := [2, 1, 3, 1, 2, 1, 3, 9]
def baseStart_1909960 : Nat := 118140960795 + 1909960 * 2 ^ 59
def prefixEnd_1909960 : Nat := 4983230072969 + 3 ^ 40 * 1909960 * 2
def baseEnd_1909960 : Nat := 72646482286033518993797

theorem tailTrace_1909960 : CollatzResearch.WordTrace tailWord_1909960 prefixEnd_1909960 72646482286033518993797 := by
  unfold tailWord_1909960
  simp only [CollatzResearch.WordTrace]
  refine ⟨34830982080274295021691667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46441309440365726695588889 34830982080274295021691667)
  ·
    refine ⟨52246473120411442532537501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34830982080274295021691667 52246473120411442532537501)
    ·
      refine ⟨19592427420154290949701563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52246473120411442532537501 19592427420154290949701563)
      ·
        refine ⟨29388641130231436424552345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19592427420154290949701563 29388641130231436424552345)
        ·
          refine ⟨22041480847673577318414259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29388641130231436424552345 22041480847673577318414259)
          ·
            refine ⟨33062221271510365977621389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22041480847673577318414259 33062221271510365977621389)
            ·
              refine ⟨12398332976816387241608021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33062221271510365977621389 12398332976816387241608021)
              ·
                refine ⟨72646482286033518993797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12398332976816387241608021 72646482286033518993797)
                ·
                  rfl

theorem cell22_1909960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 9].length) (baseStart_1909960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1909960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1909960 prefixEnd_1909960 := by exact prefixLift 1909960
  have htrace : WordTrace (prefixWord ++ tailWord_1909960) baseStart_1909960 baseEnd_1909960 := by
    simpa [prefixWord, tailWord_1909960, baseEnd_1909960] using wordTrace_append hprefix tailTrace_1909960
  have hstable : (prefixWord ++ tailWord_1909960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909960).length < 2 ^ (prefixWord ++ tailWord_1909960).sum := by decide
  have hdescent : baseEnd_1909960 < baseStart_1909960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1909975 : List Nat := [1, 1, 3, 2, 1, 2, 2, 1, 2, 7]
def baseStart_1909975 : Nat := 118140960795 + 1909975 * 2 ^ 59
def prefixEnd_1909975 : Nat := 4983230072969 + 3 ^ 40 * 1909975 * 2
def baseEnd_1909975 : Nat := 653823475380846631819127

theorem tailTrace_1909975 : CollatzResearch.WordTrace tailWord_1909975 prefixEnd_1909975 653823475380846631819127 := by
  unfold tailWord_1909975
  simp only [CollatzResearch.WordTrace]
  refine ⟨69662511255494247605179379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46441674170329498403452919 69662511255494247605179379)
  ·
    refine ⟨104493766883241371407769069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69662511255494247605179379 104493766883241371407769069)
    ·
      refine ⟨39185162581215514277913401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104493766883241371407769069 39185162581215514277913401)
      ·
        refine ⟨29388871935911635708435051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39185162581215514277913401 29388871935911635708435051)
        ·
          refine ⟨44083307903867453562652577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29388871935911635708435051 44083307903867453562652577)
          ·
            refine ⟨33062480927900590171989433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44083307903867453562652577 33062480927900590171989433)
            ·
              refine ⟨24796860695925442628992075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33062480927900590171989433 24796860695925442628992075)
              ·
                refine ⟨37195291043888163943488113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24796860695925442628992075 37195291043888163943488113)
                ·
                  refine ⟨27896468282916122957616085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37195291043888163943488113 27896468282916122957616085)
                  ·
                    refine ⟨653823475380846631819127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27896468282916122957616085 653823475380846631819127)
                    ·
                      rfl

theorem cell22_1909975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 7].length) (baseStart_1909975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1909975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1909975 prefixEnd_1909975 := by exact prefixLift 1909975
  have htrace : WordTrace (prefixWord ++ tailWord_1909975) baseStart_1909975 baseEnd_1909975 := by
    simpa [prefixWord, tailWord_1909975, baseEnd_1909975] using wordTrace_append hprefix tailTrace_1909975
  have hstable : (prefixWord ++ tailWord_1909975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1909975).length < 2 ^ (prefixWord ++ tailWord_1909975).sum := by decide
  have hdescent : baseEnd_1909975 < baseStart_1909975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1909975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910056 : List Nat := [2, 1, 5, 1, 2, 3, 1, 2, 5]
def baseStart_1910056 : Nat := 118140960795 + 1910056 * 2 ^ 59
def prefixEnd_1910056 : Nat := 4983230072969 + 3 ^ 40 * 1910056 * 2
def baseEnd_1910056 : Nat := 217950401112063140181293

theorem tailTrace_1910056 : CollatzResearch.WordTrace tailWord_1910056 prefixEnd_1910056 217950401112063140181293 := by
  unfold tailWord_1910056
  simp only [CollatzResearch.WordTrace]
  refine ⟨34832732784100399219439011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46443643712133865625918681 34832732784100399219439011)
  ·
    refine ⟨52249099176150598829158517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34832732784100399219439011 52249099176150598829158517)
    ·
      refine ⟨4898353047764118640233611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52249099176150598829158517 4898353047764118640233611)
      ·
        refine ⟨7347529571646177960350417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4898353047764118640233611 7347529571646177960350417)
        ·
          refine ⟨5510647178734633470262813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7347529571646177960350417 5510647178734633470262813)
          ·
            refine ⟨2066492692025487551348555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5510647178734633470262813 2066492692025487551348555)
            ·
              refine ⟨3099739038038231327022833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2066492692025487551348555 3099739038038231327022833)
              ·
                refine ⟨2324804278528673495267125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3099739038038231327022833 2324804278528673495267125)
                ·
                  refine ⟨217950401112063140181293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2324804278528673495267125 217950401112063140181293)
                  ·
                    rfl

theorem cell22_1910056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 2, 5].length) (baseStart_1910056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1910056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1910056 prefixEnd_1910056 := by exact prefixLift 1910056
  have htrace : WordTrace (prefixWord ++ tailWord_1910056) baseStart_1910056 baseEnd_1910056 := by
    simpa [prefixWord, tailWord_1910056, baseEnd_1910056] using wordTrace_append hprefix tailTrace_1910056
  have hstable : (prefixWord ++ tailWord_1910056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910056).length < 2 ^ (prefixWord ++ tailWord_1910056).sum := by decide
  have hdescent : baseEnd_1910056 < baseStart_1910056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910067 : List Nat := [1, 1, 1, 2, 5, 2, 1, 3, 6]
def baseStart_1910067 : Nat := 118140960795 + 1910067 * 2 ^ 59
def prefixEnd_1910067 : Nat := 4983230072969 + 3 ^ 40 * 1910067 * 2
def baseEnd_1910067 : Nat := 217951656286996352839615

theorem tailTrace_1910067 : CollatzResearch.WordTrace tailWord_1910067 prefixEnd_1910067 217951656286996352839615 := by
  unfold tailWord_1910067
  simp only [CollatzResearch.WordTrace]
  refine ⟨69665866771160947317528455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46443911180773964878352303 69665866771160947317528455)
  ·
    refine ⟨104498800156741420976292683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69665866771160947317528455 104498800156741420976292683)
    ·
      refine ⟨156748200235112131464439025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104498800156741420976292683 156748200235112131464439025)
      ·
        refine ⟨117561150176334098598329269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156748200235112131464439025 117561150176334098598329269)
        ·
          refine ⟨11021357829031321743593369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 117561150176334098598329269 11021357829031321743593369)
          ·
            refine ⟨8266018371773491307695027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11021357829031321743593369 8266018371773491307695027)
            ·
              refine ⟨12399027557660236961542541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8266018371773491307695027 12399027557660236961542541)
              ·
                refine ⟨4649635334122588860578453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12399027557660236961542541 4649635334122588860578453)
                ·
                  refine ⟨217951656286996352839615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4649635334122588860578453 217951656286996352839615)
                  ·
                    rfl

theorem cell22_1910067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 3, 6].length) (baseStart_1910067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1910067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1910067 prefixEnd_1910067 := by exact prefixLift 1910067
  have htrace : WordTrace (prefixWord ++ tailWord_1910067) baseStart_1910067 baseEnd_1910067 := by
    simpa [prefixWord, tailWord_1910067, baseEnd_1910067] using wordTrace_append hprefix tailTrace_1910067
  have hstable : (prefixWord ++ tailWord_1910067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910067).length < 2 ^ (prefixWord ++ tailWord_1910067).sum := by decide
  have hdescent : baseEnd_1910067 < baseStart_1910067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910097 : List Nat := [1, 2, 2, 1, 4, 1, 1, 3, 1, 6]
def baseStart_1910097 : Nat := 118140960795 + 1910097 * 2 ^ 59
def prefixEnd_1910097 : Nat := 4983230072969 + 3 ^ 40 * 1910097 * 2
def baseEnd_1910097 : Nat := 653865238474078980268753

theorem tailTrace_1910097 : CollatzResearch.WordTrace tailWord_1910097 prefixEnd_1910097 653865238474078980268753 := by
  unfold tailWord_1910097
  simp only [CollatzResearch.WordTrace]
  refine ⟨69666960961052262441120545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46444640640701508294080363 69666960961052262441120545)
  ·
    refine ⟨52250220720789196830840409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69666960961052262441120545 52250220720789196830840409)
    ·
      refine ⟨39187665540591897623130307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52250220720789196830840409 39187665540591897623130307)
      ·
        refine ⟨58781498310887846434695461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39187665540591897623130307 58781498310887846434695461)
        ·
          refine ⟨11021530933291471206505399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58781498310887846434695461 11021530933291471206505399)
          ·
            refine ⟨16532296399937206809758099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11021530933291471206505399 16532296399937206809758099)
            ·
              refine ⟨24798444599905810214637149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16532296399937206809758099 24798444599905810214637149)
              ·
                refine ⟨9299416724964678830488931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24798444599905810214637149 9299416724964678830488931)
                ·
                  refine ⟨13949125087447018245733397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9299416724964678830488931 13949125087447018245733397)
                  ·
                    refine ⟨653865238474078980268753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13949125087447018245733397 653865238474078980268753)
                    ·
                      rfl

theorem cell22_1910097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3, 1, 6].length) (baseStart_1910097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1910097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1910097 prefixEnd_1910097 := by exact prefixLift 1910097
  have htrace : WordTrace (prefixWord ++ tailWord_1910097) baseStart_1910097 baseEnd_1910097 := by
    simpa [prefixWord, tailWord_1910097, baseEnd_1910097] using wordTrace_append hprefix tailTrace_1910097
  have hstable : (prefixWord ++ tailWord_1910097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910097).length < 2 ^ (prefixWord ++ tailWord_1910097).sum := by decide
  have hdescent : baseEnd_1910097 < baseStart_1910097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910101 : List Nat := [1, 3, 2, 2, 3, 1, 3, 3, 4]
def baseStart_1910101 : Nat := 118140960795 + 1910101 * 2 ^ 59
def prefixEnd_1910101 : Nat := 4983230072969 + 3 ^ 40 * 1910101 * 2
def baseEnd_1910101 : Nat := 217955535918608101056247

theorem tailTrace_1910101 : CollatzResearch.WordTrace tailWord_1910101 prefixEnd_1910101 217955535918608101056247 := by
  unfold tailWord_1910101
  simp only [CollatzResearch.WordTrace]
  refine ⟨69667106853037771124266157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46444737902025180749510771 69667106853037771124266157)
  ·
    refine ⟨26125165069889164171599809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69667106853037771124266157 26125165069889164171599809)
    ·
      refine ⟨19593873802416873128699857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26125165069889164171599809 19593873802416873128699857)
      ·
        refine ⟨14695405351812654846524893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19593873802416873128699857 14695405351812654846524893)
        ·
          refine ⟨5510777006929745567446835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14695405351812654846524893 5510777006929745567446835)
          ·
            refine ⟨8266165510394618351170253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5510777006929745567446835 8266165510394618351170253)
            ·
              refine ⟨3099812066397981881688845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8266165510394618351170253 3099812066397981881688845)
              ·
                refine ⟨1162429524899243205633317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3099812066397981881688845 1162429524899243205633317)
                ·
                  refine ⟨217955535918608101056247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1162429524899243205633317 217955535918608101056247)
                  ·
                    rfl

theorem cell22_1910101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 3, 4].length) (baseStart_1910101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1910101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1910101 prefixEnd_1910101 := by exact prefixLift 1910101
  have htrace : WordTrace (prefixWord ++ tailWord_1910101) baseStart_1910101 baseEnd_1910101 := by
    simpa [prefixWord, tailWord_1910101, baseEnd_1910101] using wordTrace_append hprefix tailTrace_1910101
  have hstable : (prefixWord ++ tailWord_1910101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910101).length < 2 ^ (prefixWord ++ tailWord_1910101).sum := by decide
  have hdescent : baseEnd_1910101 < baseStart_1910101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910112 : List Nat := [2, 1, 1, 3, 4, 1, 10]
def baseStart_1910112 : Nat := 118140960795 + 1910112 * 2 ^ 59
def prefixEnd_1910112 : Nat := 4983230072969 + 3 ^ 40 * 1910112 * 2
def baseEnd_1910112 : Nat := 24217421232615701523841

theorem tailTrace_1910112 : CollatzResearch.WordTrace tailWord_1910112 prefixEnd_1910112 24217421232615701523841 := by
  unfold tailWord_1910112
  simp only [CollatzResearch.WordTrace]
  refine ⟨34833754027998960001458295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46445005370665280001944393 34833754027998960001458295)
  ·
    refine ⟨52250631041998440002187443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34833754027998960001458295 52250631041998440002187443)
    ·
      refine ⟨78375946562997660003281165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52250631041998440002187443 78375946562997660003281165)
      ·
        refine ⟨29390979961124122501230437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78375946562997660003281165 29390979961124122501230437)
        ·
          refine ⟨5510808742710772968980707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29390979961124122501230437 5510808742710772968980707)
          ·
            refine ⟨8266213114066159453471061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5510808742710772968980707 8266213114066159453471061)
            ·
              refine ⟨24217421232615701523841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8266213114066159453471061 24217421232615701523841)
              ·
                rfl

theorem cell22_1910112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 10].length) (baseStart_1910112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1910112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1910112 prefixEnd_1910112 := by exact prefixLift 1910112
  have htrace : WordTrace (prefixWord ++ tailWord_1910112) baseStart_1910112 baseEnd_1910112 := by
    simpa [prefixWord, tailWord_1910112, baseEnd_1910112] using wordTrace_append hprefix tailTrace_1910112
  have hstable : (prefixWord ++ tailWord_1910112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910112).length < 2 ^ (prefixWord ++ tailWord_1910112).sum := by decide
  have hdescent : baseEnd_1910112 < baseStart_1910112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910133 : List Nat := [1, 3, 4, 1, 3, 1, 1, 3, 2, 3]
def baseStart_1910133 : Nat := 118140960795 + 1910133 * 2 ^ 59
def prefixEnd_1910133 : Nat := 4983230072969 + 3 ^ 40 * 1910133 * 2
def baseEnd_1910133 : Nat := 653877562009786886368643

theorem tailTrace_1910133 : CollatzResearch.WordTrace tailWord_1910133 prefixEnd_1910133 653877562009786886368643 := by
  unfold tailWord_1910133
  simp only [CollatzResearch.WordTrace]
  refine ⟨69668273988921840589431053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46445515992614560392954035 69668273988921840589431053)
  ·
    refine ⟨26125602745845690221036645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69668273988921840589431053 26125602745845690221036645)
    ·
      refine ⟨4898550514846066916444371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26125602745845690221036645 4898550514846066916444371)
      ·
        refine ⟨7347825772269100374666557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4898550514846066916444371 7347825772269100374666557)
        ·
          refine ⟨2755434664600912640499959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7347825772269100374666557 2755434664600912640499959)
          ·
            refine ⟨4133151996901368960749939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2755434664600912640499959 4133151996901368960749939)
            ·
              refine ⟨6199727995352053441124909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4133151996901368960749939 6199727995352053441124909)
              ·
                refine ⟨2324897998257020040421841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6199727995352053441124909 2324897998257020040421841)
                ·
                  refine ⟨1743673498692765030316381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2324897998257020040421841 1743673498692765030316381)
                  ·
                    refine ⟨653877562009786886368643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1743673498692765030316381 653877562009786886368643)
                    ·
                      rfl

theorem cell22_1910133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_1910133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1910133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1910133 prefixEnd_1910133 := by exact prefixLift 1910133
  have htrace : WordTrace (prefixWord ++ tailWord_1910133) baseStart_1910133 baseEnd_1910133 := by
    simpa [prefixWord, tailWord_1910133, baseEnd_1910133] using wordTrace_append hprefix tailTrace_1910133
  have hstable : (prefixWord ++ tailWord_1910133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910133).length < 2 ^ (prefixWord ++ tailWord_1910133).sum := by decide
  have hdescent : baseEnd_1910133 < baseStart_1910133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910144 : List Nat := [2, 1, 1, 2, 1, 2, 1, 6, 3, 3]
def baseStart_1910144 : Nat := 118140960795 + 1910144 * 2 ^ 59
def prefixEnd_1910144 : Nat := 4983230072969 + 3 ^ 40 * 1910144 * 2
def baseEnd_1910144 : Nat := 653881327534586524343609

theorem tailTrace_1910144 : CollatzResearch.WordTrace tailWord_1910144 prefixEnd_1910144 653881327534586524343609 := by
  unfold tailWord_1910144
  simp only [CollatzResearch.WordTrace]
  refine ⟨34834337595940994734040743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46445783461254659645387657 34834337595940994734040743)
  ·
    refine ⟨52251506393911492101061115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34834337595940994734040743 52251506393911492101061115)
    ·
      refine ⟨78377259590867238151591673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52251506393911492101061115 78377259590867238151591673)
      ·
        refine ⟨58782944693150428613693755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78377259590867238151591673 58782944693150428613693755)
        ·
          refine ⟨88174417039725642920540633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58782944693150428613693755 88174417039725642920540633)
          ·
            refine ⟨66130812779794232190405475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88174417039725642920540633 66130812779794232190405475)
            ·
              refine ⟨99196219169691348285608213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66130812779794232190405475 99196219169691348285608213)
              ·
                refine ⟨4649822773579281950887885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 99196219169691348285608213 4649822773579281950887885)
                ·
                  refine ⟨1743683540092230731582957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4649822773579281950887885 1743683540092230731582957)
                  ·
                    refine ⟨653881327534586524343609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1743683540092230731582957 653881327534586524343609)
                    ·
                      rfl

theorem cell22_1910144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 6, 3, 3].length) (baseStart_1910144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1910144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1910144 prefixEnd_1910144 := by exact prefixLift 1910144
  have htrace : WordTrace (prefixWord ++ tailWord_1910144) baseStart_1910144 baseEnd_1910144 := by
    simpa [prefixWord, tailWord_1910144, baseEnd_1910144] using wordTrace_append hprefix tailTrace_1910144
  have hstable : (prefixWord ++ tailWord_1910144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910144).length < 2 ^ (prefixWord ++ tailWord_1910144).sum := by decide
  have hdescent : baseEnd_1910144 < baseStart_1910144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910146 : List Nat := [3, 4, 2, 1, 1, 1, 2, 8]
def baseStart_1910146 : Nat := 118140960795 + 1910146 * 2 ^ 59
def prefixEnd_1910146 : Nat := 4983230072969 + 3 ^ 40 * 1910146 * 2
def baseEnd_1910146 : Nat := 72653556908384353977067

theorem tailTrace_1910146 : CollatzResearch.WordTrace tailWord_1910146 prefixEnd_1910146 72653556908384353977067 := by
  unfold tailWord_1910146
  simp only [CollatzResearch.WordTrace]
  refine ⟨17417187034468685952413573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46445832091916495873102861 17417187034468685952413573)
  ·
    refine ⟨3265722568962878616077545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17417187034468685952413573 3265722568962878616077545)
    ·
      refine ⟨2449291926722158962058159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3265722568962878616077545 2449291926722158962058159)
      ·
        refine ⟨3673937890083238443087239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2449291926722158962058159 3673937890083238443087239)
        ·
          refine ⟨5510906835124857664630859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3673937890083238443087239 5510906835124857664630859)
          ·
            refine ⟨8266360252687286496946289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5510906835124857664630859 8266360252687286496946289)
            ·
              refine ⟨6199770189515464872709717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8266360252687286496946289 6199770189515464872709717)
              ·
                refine ⟨72653556908384353977067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6199770189515464872709717 72653556908384353977067)
                ·
                  rfl

theorem cell22_1910146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 8].length) (baseStart_1910146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1910146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1910146 prefixEnd_1910146 := by exact prefixLift 1910146
  have htrace : WordTrace (prefixWord ++ tailWord_1910146) baseStart_1910146 baseEnd_1910146 := by
    simpa [prefixWord, tailWord_1910146, baseEnd_1910146] using wordTrace_append hprefix tailTrace_1910146
  have hstable : (prefixWord ++ tailWord_1910146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910146).length < 2 ^ (prefixWord ++ tailWord_1910146).sum := by decide
  have hdescent : baseEnd_1910146 < baseStart_1910146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910264 : List Nat := [2, 1, 2, 1, 1, 6, 1, 8]
def baseStart_1910264 : Nat := 118140960795 + 1910264 * 2 ^ 59
def prefixEnd_1910264 : Nat := 4983230072969 + 3 ^ 40 * 1910264 * 2
def baseEnd_1910264 : Nat := 72658045109660690149249

theorem tailTrace_1910264 : CollatzResearch.WordTrace tailWord_1910264 prefixEnd_1910264 72658045109660690149249 := by
  unfold tailWord_1910264
  simp only [CollatzResearch.WordTrace]
  refine ⟨34836525975723624981224923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46448701300964833308299897 34836525975723624981224923)
  ·
    refine ⟨52254788963585437471837385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34836525975723624981224923 52254788963585437471837385)
    ·
      refine ⟨39191091722689078103878039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52254788963585437471837385 39191091722689078103878039)
      ·
        refine ⟨58786637584033617155817059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39191091722689078103878039 58786637584033617155817059)
        ·
          refine ⟨88179956376050425733725589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58786637584033617155817059 88179956376050425733725589)
          ·
            refine ⟨4133435455127363706268387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 88179956376050425733725589 4133435455127363706268387)
            ·
              refine ⟨6200153182691045559402581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4133435455127363706268387 6200153182691045559402581)
              ·
                refine ⟨72658045109660690149249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6200153182691045559402581 72658045109660690149249)
                ·
                  rfl

theorem cell22_1910264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 8].length) (baseStart_1910264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1910264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1910264 prefixEnd_1910264 := by exact prefixLift 1910264
  have htrace : WordTrace (prefixWord ++ tailWord_1910264) baseStart_1910264 baseEnd_1910264 := by
    simpa [prefixWord, tailWord_1910264, baseEnd_1910264] using wordTrace_append hprefix tailTrace_1910264
  have hstable : (prefixWord ++ tailWord_1910264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910264).length < 2 ^ (prefixWord ++ tailWord_1910264).sum := by decide
  have hdescent : baseEnd_1910264 < baseStart_1910264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910343 : List Nat := [1, 1, 4, 1, 5, 1, 2, 2, 5]
def baseStart_1910343 : Nat := 118140960795 + 1910343 * 2 ^ 59
def prefixEnd_1910343 : Nat := 4983230072969 + 3 ^ 40 * 1910343 * 2
def baseEnd_1910343 : Nat := 217983149767138779539333

theorem tailTrace_1910343 : CollatzResearch.WordTrace tailWord_1910343 prefixEnd_1910343 217983149767138779539333 := by
  unfold tailWord_1910343
  simp only [CollatzResearch.WordTrace]
  refine ⟨69675933318161046454575683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46450622212107364303050455 69675933318161046454575683)
  ·
    refine ⟨104513899977241569681863525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69675933318161046454575683 104513899977241569681863525)
    ·
      refine ⟨19596356245732794315349411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104513899977241569681863525 19596356245732794315349411)
      ·
        refine ⟨29394534368599191473024117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19596356245732794315349411 29394534368599191473024117)
        ·
          refine ⟨2755737597056174200596011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29394534368599191473024117 2755737597056174200596011)
          ·
            refine ⟨4133606395584261300894017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2755737597056174200596011 4133606395584261300894017)
            ·
              refine ⟨3100204796688195975670513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4133606395584261300894017 3100204796688195975670513)
              ·
                refine ⟨2325153597516146981752885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3100204796688195975670513 2325153597516146981752885)
                ·
                  refine ⟨217983149767138779539333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2325153597516146981752885 217983149767138779539333)
                  ·
                    rfl

theorem cell22_1910343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 2, 5].length) (baseStart_1910343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1910343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1910343 prefixEnd_1910343 := by exact prefixLift 1910343
  have htrace : WordTrace (prefixWord ++ tailWord_1910343) baseStart_1910343 baseEnd_1910343 := by
    simpa [prefixWord, tailWord_1910343, baseEnd_1910343] using wordTrace_append hprefix tailTrace_1910343
  have hstable : (prefixWord ++ tailWord_1910343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910343).length < 2 ^ (prefixWord ++ tailWord_1910343).sum := by decide
  have hdescent : baseEnd_1910343 < baseStart_1910343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910356 : List Nat := [2, 4, 1, 1, 1, 2, 1, 1, 5, 4]
def baseStart_1910356 : Nat := 118140960795 + 1910356 * 2 ^ 59
def prefixEnd_1910356 : Nat := 4983230072969 + 3 ^ 40 * 1910356 * 2
def baseEnd_1910356 : Nat := 653953899467088638042959

theorem tailTrace_1910356 : CollatzResearch.WordTrace tailWord_1910356 prefixEnd_1910356 653953899467088638042959 := by
  unfold tailWord_1910356
  simp only [CollatzResearch.WordTrace]
  refine ⟨34838203733556974837399461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46450938311409299783199281 34838203733556974837399461)
  ·
    refine ⟨6532163200041932782012399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34838203733556974837399461 6532163200041932782012399)
    ·
      refine ⟨9798244800062899173018599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6532163200041932782012399 9798244800062899173018599)
      ·
        refine ⟨14697367200094348759527899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9798244800062899173018599 14697367200094348759527899)
        ·
          refine ⟨22046050800141523139291849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14697367200094348759527899 22046050800141523139291849)
          ·
            refine ⟨16534538100106142354468887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22046050800141523139291849 16534538100106142354468887)
            ·
              refine ⟨24801807150159213531703331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16534538100106142354468887 24801807150159213531703331)
              ·
                refine ⟨37202710725238820297554997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24801807150159213531703331 37202710725238820297554997)
                ·
                  refine ⟨3487754130491139402895781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37202710725238820297554997 3487754130491139402895781)
                  ·
                    refine ⟨653953899467088638042959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3487754130491139402895781 653953899467088638042959)
                    ·
                      rfl

theorem cell22_1910356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_1910356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1910356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1910356 prefixEnd_1910356 := by exact prefixLift 1910356
  have htrace : WordTrace (prefixWord ++ tailWord_1910356) baseStart_1910356 baseEnd_1910356 := by
    simpa [prefixWord, tailWord_1910356, baseEnd_1910356] using wordTrace_append hprefix tailTrace_1910356
  have hstable : (prefixWord ++ tailWord_1910356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910356).length < 2 ^ (prefixWord ++ tailWord_1910356).sum := by decide
  have hdescent : baseEnd_1910356 < baseStart_1910356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910371 : List Nat := [1, 1, 1, 5, 1, 4, 1, 2, 6]
def baseStart_1910371 : Nat := 118140960795 + 1910371 * 2 ^ 59
def prefixEnd_1910371 : Nat := 4983230072969 + 3 ^ 40 * 1910371 * 2
def baseEnd_1910371 : Nat := 217986344757877866305971

theorem tailTrace_1910371 : CollatzResearch.WordTrace tailWord_1910371 prefixEnd_1910371 217986344757877866305971 := by
  unfold tailWord_1910371
  simp only [CollatzResearch.WordTrace]
  refine ⟨69676954562059607236594967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46451303041373071491063311 69676954562059607236594967)
  ·
    refine ⟨104515431843089410854892451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69676954562059607236594967 104515431843089410854892451)
    ·
      refine ⟨156773147764634116282338677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104515431843089410854892451 156773147764634116282338677)
      ·
        refine ⟨14697482602934448401469251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 156773147764634116282338677 14697482602934448401469251)
        ·
          refine ⟨22046223904401672602203877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14697482602934448401469251 22046223904401672602203877)
          ·
            refine ⟨4133666982075313612913227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22046223904401672602203877 4133666982075313612913227)
            ·
              refine ⟨6200500473112970419369841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4133666982075313612913227 6200500473112970419369841)
              ·
                refine ⟨4650375354834727814527381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6200500473112970419369841 4650375354834727814527381)
                ·
                  refine ⟨217986344757877866305971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4650375354834727814527381 217986344757877866305971)
                  ·
                    rfl

theorem cell22_1910371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 2, 6].length) (baseStart_1910371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1910371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1910371 prefixEnd_1910371 := by exact prefixLift 1910371
  have htrace : WordTrace (prefixWord ++ tailWord_1910371) baseStart_1910371 baseEnd_1910371 := by
    simpa [prefixWord, tailWord_1910371, baseEnd_1910371] using wordTrace_append hprefix tailTrace_1910371
  have hstable : (prefixWord ++ tailWord_1910371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910371).length < 2 ^ (prefixWord ++ tailWord_1910371).sum := by decide
  have hdescent : baseEnd_1910371 < baseStart_1910371 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910390 : List Nat := [5, 1, 1, 2, 2, 2, 1, 3, 1, 4]
def baseStart_1910390 : Nat := 118140960795 + 1910390 * 2 ^ 59
def prefixEnd_1910390 : Nat := 4983230072969 + 3 ^ 40 * 1910390 * 2
def baseEnd_1910390 : Nat := 653965538361923882692855

theorem tailTrace_1910390 : CollatzResearch.WordTrace tailWord_1910390 prefixEnd_1910390 653965538361923882692855 := by
  unfold tailWord_1910390
  simp only [CollatzResearch.WordTrace]
  refine ⟨4354852971811923342596039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46451765032660515654357749 4354852971811923342596039)
  ·
    refine ⟨6532279457717885013894059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4354852971811923342596039 6532279457717885013894059)
    ·
      refine ⟨9798419186576827520841089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6532279457717885013894059 9798419186576827520841089)
      ·
        refine ⟨7348814389932620640630817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9798419186576827520841089 7348814389932620640630817)
        ·
          refine ⟨5511610792449465480473113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7348814389932620640630817 5511610792449465480473113)
          ·
            refine ⟨4133708094337099110354835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5511610792449465480473113 4133708094337099110354835)
            ·
              refine ⟨6200562141505648665532253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4133708094337099110354835 6200562141505648665532253)
              ·
                refine ⟨2325210803064618249574595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6200562141505648665532253 2325210803064618249574595)
                ·
                  refine ⟨3487816204596927374361893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2325210803064618249574595 3487816204596927374361893)
                  ·
                    refine ⟨653965538361923882692855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3487816204596927374361893 653965538361923882692855)
                    ·
                      rfl

theorem cell22_1910390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_1910390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1910390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1910390 prefixEnd_1910390 := by exact prefixLift 1910390
  have htrace : WordTrace (prefixWord ++ tailWord_1910390) baseStart_1910390 baseEnd_1910390 := by
    simpa [prefixWord, tailWord_1910390, baseEnd_1910390] using wordTrace_append hprefix tailTrace_1910390
  have hstable : (prefixWord ++ tailWord_1910390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910390).length < 2 ^ (prefixWord ++ tailWord_1910390).sum := by decide
  have hdescent : baseEnd_1910390 < baseStart_1910390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910433 : List Nat := [1, 2, 3, 3, 2, 1, 4, 6]
def baseStart_1910433 : Nat := 118140960795 + 1910433 * 2 ^ 59
def prefixEnd_1910433 : Nat := 4983230072969 + 3 ^ 40 * 1910433 * 2
def baseEnd_1910433 : Nat := 72664473126742900429747

theorem tailTrace_1910433 : CollatzResearch.WordTrace tailWord_1910433 prefixEnd_1910433 72664473126742900429747 := by
  unfold tailWord_1910433
  simp only [CollatzResearch.WordTrace]
  refine ⟨69679215887834991825351953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46452810591889994550234635 69679215887834991825351953)
  ·
    refine ⟨52259411915876243869013965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69679215887834991825351953 52259411915876243869013965)
    ·
      refine ⟨19597279468453591450880237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52259411915876243869013965 19597279468453591450880237)
      ·
        refine ⟨7348979800670096794080089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19597279468453591450880237 7348979800670096794080089)
        ·
          refine ⟨5511734850502572595560067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7348979800670096794080089 5511734850502572595560067)
          ·
            refine ⟨8267602275753858893340101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5511734850502572595560067 8267602275753858893340101)
            ·
              refine ⟨1550175426703848542501269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8267602275753858893340101 1550175426703848542501269)
              ·
                refine ⟨72664473126742900429747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1550175426703848542501269 72664473126742900429747)
                ·
                  rfl

theorem cell22_1910433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 4, 6].length) (baseStart_1910433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1910433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1910433 prefixEnd_1910433 := by exact prefixLift 1910433
  have htrace : WordTrace (prefixWord ++ tailWord_1910433) baseStart_1910433 baseEnd_1910433 := by
    simpa [prefixWord, tailWord_1910433, baseEnd_1910433] using wordTrace_append hprefix tailTrace_1910433
  have hstable : (prefixWord ++ tailWord_1910433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910433).length < 2 ^ (prefixWord ++ tailWord_1910433).sum := by decide
  have hdescent : baseEnd_1910433 < baseStart_1910433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910461 : List Nat := [1, 4, 1, 2, 1, 2, 1, 3, 7]
def baseStart_1910461 : Nat := 118140960795 + 1910461 * 2 ^ 59
def prefixEnd_1910461 : Nat := 4983230072969 + 3 ^ 40 * 1910461 * 2
def baseEnd_1910461 : Nat := 217996614370967788055879

theorem tailTrace_1910461 : CollatzResearch.WordTrace tailWord_1910461 prefixEnd_1910461 217996614370967788055879 := by
  unfold tailWord_1910461
  simp only [CollatzResearch.WordTrace]
  refine ⟨69680237131733552607371237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46453491421155701738247491 69680237131733552607371237)
  ·
    refine ⟨13065044462200041113882107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69680237131733552607371237 13065044462200041113882107)
    ·
      refine ⟨19597566693300061670823161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13065044462200041113882107 19597566693300061670823161)
      ·
        refine ⟨14698175019975046253117371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19597566693300061670823161 14698175019975046253117371)
        ·
          refine ⟨22047262529962569379676057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14698175019975046253117371 22047262529962569379676057)
          ·
            refine ⟨16535446897471927034757043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22047262529962569379676057 16535446897471927034757043)
            ·
              refine ⟨24803170346207890552135565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16535446897471927034757043 24803170346207890552135565)
              ·
                refine ⟨9301188879827958957050837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24803170346207890552135565 9301188879827958957050837)
                ·
                  refine ⟨217996614370967788055879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9301188879827958957050837 217996614370967788055879)
                  ·
                    rfl

theorem cell22_1910461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3, 7].length) (baseStart_1910461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1910461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1910461 prefixEnd_1910461 := by exact prefixLift 1910461
  have htrace : WordTrace (prefixWord ++ tailWord_1910461) baseStart_1910461 baseEnd_1910461 := by
    simpa [prefixWord, tailWord_1910461, baseEnd_1910461] using wordTrace_append hprefix tailTrace_1910461
  have hstable : (prefixWord ++ tailWord_1910461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910461).length < 2 ^ (prefixWord ++ tailWord_1910461).sum := by decide
  have hdescent : baseEnd_1910461 < baseStart_1910461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910478 : List Nat := [4, 1, 1, 1, 3, 1, 3, 3, 5]
def baseStart_1910478 : Nat := 118140960795 + 1910478 * 2 ^ 59
def prefixEnd_1910478 : Nat := 4983230072969 + 3 ^ 40 * 1910478 * 2
def baseEnd_1910478 : Nat := 217998554186773662164195

theorem tailTrace_1910478 : CollatzResearch.WordTrace tailWord_1910478 prefixEnd_1910478 217998554186773662164195 := by
  unfold tailWord_1910478
  simp only [CollatzResearch.WordTrace]
  refine ⟨8710107146583995563842511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46453904781781309673826725 8710107146583995563842511)
  ·
    refine ⟨13065160719875993345763767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8710107146583995563842511 13065160719875993345763767)
    ·
      refine ⟨19597741079813990018645651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13065160719875993345763767 19597741079813990018645651)
      ·
        refine ⟨29396611619720985027968477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19597741079813990018645651 29396611619720985027968477)
        ·
          refine ⟨11023729357395369385488179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29396611619720985027968477 11023729357395369385488179)
          ·
            refine ⟨16535594036093054078232269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11023729357395369385488179 16535594036093054078232269)
            ·
              refine ⟨6200847763534895279337101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16535594036093054078232269 6200847763534895279337101)
              ·
                refine ⟨2325317911325585729751413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6200847763534895279337101 2325317911325585729751413)
                ·
                  refine ⟨217998554186773662164195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2325317911325585729751413 217998554186773662164195)
                  ·
                    rfl

theorem cell22_1910478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 3, 5].length) (baseStart_1910478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1910478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1910478 prefixEnd_1910478 := by exact prefixLift 1910478
  have htrace : WordTrace (prefixWord ++ tailWord_1910478) baseStart_1910478 baseEnd_1910478 := by
    simpa [prefixWord, tailWord_1910478, baseEnd_1910478] using wordTrace_append hprefix tailTrace_1910478
  have hstable : (prefixWord ++ tailWord_1910478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910478).length < 2 ^ (prefixWord ++ tailWord_1910478).sum := by decide
  have hdescent : baseEnd_1910478 < baseStart_1910478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910508 : List Nat := [2, 2, 1, 1, 2, 2, 2, 5, 1, 4]
def baseStart_1910508 : Nat := 118140960795 + 1910508 * 2 ^ 59
def prefixEnd_1910508 : Nat := 4983230072969 + 3 ^ 40 * 1910508 * 2
def baseEnd_1910508 : Nat := 654005932173410908242493

theorem tailTrace_1910508 : CollatzResearch.WordTrace tailWord_1910508 prefixEnd_1910508 654005932173410908242493 := by
  unfold tailWord_1910508
  simp only [CollatzResearch.WordTrace]
  refine ⟨34840975681281639817166089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46454634241708853089554785 34840975681281639817166089)
  ·
    refine ⟨26130731760961229862874567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34840975681281639817166089 26130731760961229862874567)
    ·
      refine ⟨39196097641441844794311851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26130731760961229862874567 39196097641441844794311851)
      ·
        refine ⟨58794146462162767191467777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39196097641441844794311851 58794146462162767191467777)
        ·
          refine ⟨44095609846622075393600833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58794146462162767191467777 44095609846622075393600833)
          ·
            refine ⟨33071707384966556545200625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44095609846622075393600833 33071707384966556545200625)
            ·
              refine ⟨24803780538724917408900469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33071707384966556545200625 24803780538724917408900469)
              ·
                refine ⟨2325354425505461007084419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24803780538724917408900469 2325354425505461007084419)
                ·
                  refine ⟨3488031638258191510626629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2325354425505461007084419 3488031638258191510626629)
                  ·
                    refine ⟨654005932173410908242493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3488031638258191510626629 654005932173410908242493)
                    ·
                      rfl

theorem cell22_1910508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 4].length) (baseStart_1910508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1910508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1910508 prefixEnd_1910508 := by exact prefixLift 1910508
  have htrace : WordTrace (prefixWord ++ tailWord_1910508) baseStart_1910508 baseEnd_1910508 := by
    simpa [prefixWord, tailWord_1910508, baseEnd_1910508] using wordTrace_append hprefix tailTrace_1910508
  have hstable : (prefixWord ++ tailWord_1910508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910508).length < 2 ^ (prefixWord ++ tailWord_1910508).sum := by decide
  have hdescent : baseEnd_1910508 < baseStart_1910508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910516 : List Nat := [2, 6, 1, 1, 1, 2, 1, 4, 1, 3]
def baseStart_1910516 : Nat := 118140960795 + 1910516 * 2 ^ 59
def prefixEnd_1910516 : Nat := 4983230072969 + 3 ^ 40 * 1910516 * 2
def baseEnd_1910516 : Nat := 654008670736901554042469

theorem tailTrace_1910516 : CollatzResearch.WordTrace tailWord_1910516 prefixEnd_1910516 654008670736901554042469 := by
  unfold tailWord_1910516
  simp only [CollatzResearch.WordTrace]
  refine ⟨34841121573267148500311701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46454828764356198000415601 34841121573267148500311701)
  ·
    refine ⟨1633177573746897585952111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 34841121573267148500311701 1633177573746897585952111)
    ·
      refine ⟨2449766360620346378928167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1633177573746897585952111 2449766360620346378928167)
      ·
        refine ⟨3674649540930519568392251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2449766360620346378928167 3674649540930519568392251)
        ·
          refine ⟨5511974311395779352588377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3674649540930519568392251 5511974311395779352588377)
          ·
            refine ⟨4133980733546834514441283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5511974311395779352588377 4133980733546834514441283)
            ·
              refine ⟨6200971100320251771661925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4133980733546834514441283 6200971100320251771661925)
              ·
                refine ⟨1162682081310047207186611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6200971100320251771661925 1162682081310047207186611)
                ·
                  refine ⟨1744023121965070810779917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1162682081310047207186611 1744023121965070810779917)
                  ·
                    refine ⟨654008670736901554042469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1744023121965070810779917 654008670736901554042469)
                    ·
                      rfl

theorem cell22_1910516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_1910516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1910516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1910516 prefixEnd_1910516 := by exact prefixLift 1910516
  have htrace : WordTrace (prefixWord ++ tailWord_1910516) baseStart_1910516 baseEnd_1910516 := by
    simpa [prefixWord, tailWord_1910516, baseEnd_1910516] using wordTrace_append hprefix tailTrace_1910516
  have hstable : (prefixWord ++ tailWord_1910516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910516).length < 2 ^ (prefixWord ++ tailWord_1910516).sum := by decide
  have hdescent : baseEnd_1910516 < baseStart_1910516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910538 : List Nat := [3, 1, 2, 2, 1, 3, 1, 3, 1, 5]
def baseStart_1910538 : Nat := 118140960795 + 1910538 * 2 ^ 59
def prefixEnd_1910538 : Nat := 4983230072969 + 3 ^ 40 * 1910538 * 2
def baseEnd_1910538 : Nat := 654016201786500829992401

theorem tailTrace_1910538 : CollatzResearch.WordTrace tailWord_1910538 prefixEnd_1910538 654016201786500829992401 := by
  unfold tailWord_1910538
  simp only [CollatzResearch.WordTrace]
  refine ⟨17420761388113648689481067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46455363701636396505282845 17420761388113648689481067)
  ·
    refine ⟨26131142082170473034221601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17420761388113648689481067 26131142082170473034221601)
    ·
      refine ⟨19598356561627854775666201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26131142082170473034221601 19598356561627854775666201)
      ·
        refine ⟨14698767421220891081749651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19598356561627854775666201 14698767421220891081749651)
        ·
          refine ⟨22048151131831336622624477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14698767421220891081749651 22048151131831336622624477)
          ·
            refine ⟨8268056674436751233484179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22048151131831336622624477 8268056674436751233484179)
            ·
              refine ⟨12402085011655126850226269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8268056674436751233484179 12402085011655126850226269)
              ·
                refine ⟨4650781879370672568834851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12402085011655126850226269 4650781879370672568834851)
                ·
                  refine ⟨6976172819056008853252277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4650781879370672568834851 6976172819056008853252277)
                  ·
                    refine ⟨654016201786500829992401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6976172819056008853252277 654016201786500829992401)
                    ·
                      rfl

theorem cell22_1910538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 3, 1, 5].length) (baseStart_1910538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1910538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1910538 prefixEnd_1910538 := by exact prefixLift 1910538
  have htrace : WordTrace (prefixWord ++ tailWord_1910538) baseStart_1910538 baseEnd_1910538 := by
    simpa [prefixWord, tailWord_1910538, baseEnd_1910538] using wordTrace_append hprefix tailTrace_1910538
  have hstable : (prefixWord ++ tailWord_1910538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910538).length < 2 ^ (prefixWord ++ tailWord_1910538).sum := by decide
  have hdescent : baseEnd_1910538 < baseStart_1910538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910568 : List Nat := [2, 1, 5, 1, 1, 3, 9]
def baseStart_1910568 : Nat := 118140960795 + 1910568 * 2 ^ 59
def prefixEnd_1910568 : Nat := 4983230072969 + 3 ^ 40 * 1910568 * 2
def baseEnd_1910568 : Nat := 24223202644429287101567

theorem tailTrace_1910568 : CollatzResearch.WordTrace tailWord_1910568 prefixEnd_1910568 24223202644429287101567 := by
  unfold tailWord_1910568
  simp only [CollatzResearch.WordTrace]
  refine ⟨34842069871172954940758179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46456093161563939921010905 34842069871172954940758179)
  ·
    refine ⟨52263104806759432411137269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34842069871172954940758179 52263104806759432411137269)
    ·
      refine ⟨4899666075633696788544119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52263104806759432411137269 4899666075633696788544119)
      ·
        refine ⟨7349499113450545182816179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4899666075633696788544119 7349499113450545182816179)
        ·
          refine ⟨11024248670175817774224269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7349499113450545182816179 11024248670175817774224269)
          ·
            refine ⟨4134093251315931665334101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11024248670175817774224269 4134093251315931665334101)
            ·
              refine ⟨24223202644429287101567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4134093251315931665334101 24223202644429287101567)
              ·
                rfl

theorem cell22_1910568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 9].length) (baseStart_1910568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1910568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1910568 prefixEnd_1910568 := by exact prefixLift 1910568
  have htrace : WordTrace (prefixWord ++ tailWord_1910568) baseStart_1910568 baseEnd_1910568 := by
    simpa [prefixWord, tailWord_1910568, baseEnd_1910568] using wordTrace_append hprefix tailTrace_1910568
  have hstable : (prefixWord ++ tailWord_1910568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910568).length < 2 ^ (prefixWord ++ tailWord_1910568).sum := by decide
  have hdescent : baseEnd_1910568 < baseStart_1910568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910572 : List Nat := [2, 2, 1, 1, 1, 7, 1, 2, 2, 3]
def baseStart_1910572 : Nat := 118140960795 + 1910572 * 2 ^ 59
def prefixEnd_1910572 : Nat := 4983230072969 + 3 ^ 40 * 1910572 * 2
def baseEnd_1910572 : Nat := 654027840681336074642297

theorem tailTrace_1910572 : CollatzResearch.WordTrace tailWord_1910572 prefixEnd_1910572 654027840681336074642297 := by
  unfold tailWord_1910572
  simp only [CollatzResearch.WordTrace]
  refine ⟨34842142817165709282330985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46456190422887612376441313 34842142817165709282330985)
  ·
    refine ⟨26131607112874281961748239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34842142817165709282330985 26131607112874281961748239)
    ·
      refine ⟨39197410669311422942622359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26131607112874281961748239 39197410669311422942622359)
      ·
        refine ⟨58796116003967134413933539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39197410669311422942622359 58796116003967134413933539)
        ·
          refine ⟨88194174005950701620900309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58796116003967134413933539 88194174005950701620900309)
          ·
            refine ⟨2067050953264469569239851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 88194174005950701620900309 2067050953264469569239851)
            ·
              refine ⟨3100576429896704353859777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2067050953264469569239851 3100576429896704353859777)
              ·
                refine ⟨2325432322422528265394833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3100576429896704353859777 2325432322422528265394833)
                ·
                  refine ⟨1744074241816896199046125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2325432322422528265394833 1744074241816896199046125)
                  ·
                    refine ⟨654027840681336074642297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1744074241816896199046125 654027840681336074642297)
                    ·
                      rfl

theorem cell22_1910572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 3].length) (baseStart_1910572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1910572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1910572 prefixEnd_1910572 := by exact prefixLift 1910572
  have htrace : WordTrace (prefixWord ++ tailWord_1910572) baseStart_1910572 baseEnd_1910572 := by
    simpa [prefixWord, tailWord_1910572, baseEnd_1910572] using wordTrace_append hprefix tailTrace_1910572
  have hstable : (prefixWord ++ tailWord_1910572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910572).length < 2 ^ (prefixWord ++ tailWord_1910572).sum := by decide
  have hdescent : baseEnd_1910572 < baseStart_1910572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910589 : List Nat := [1, 4, 1, 4, 1, 2, 3, 1, 2, 3]
def baseStart_1910589 : Nat := 118140960795 + 1910589 * 2 ^ 59
def prefixEnd_1910589 : Nat := 4983230072969 + 3 ^ 40 * 1910589 * 2
def baseEnd_1910589 : Nat := 654033660128753696967245

theorem tailTrace_1910589 : CollatzResearch.WordTrace tailWord_1910589 prefixEnd_1910589 654033660128753696967245 := by
  unfold tailWord_1910589
  simp only [CollatzResearch.WordTrace]
  refine ⟨69684905675269830468030821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46456603783513220312020547 69684905675269830468030821)
  ·
    refine ⟨13065919814113093212755779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69684905675269830468030821 13065919814113093212755779)
    ·
      refine ⟨19598879721169639819133669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13065919814113093212755779 19598879721169639819133669)
      ·
        refine ⟨3674789947719307466087563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19598879721169639819133669 3674789947719307466087563)
        ·
          refine ⟨5512184921578961199131345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3674789947719307466087563 5512184921578961199131345)
          ·
            refine ⟨4134138691184220899348509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5512184921578961199131345 4134138691184220899348509)
            ·
              refine ⟨1550302009194082837255691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4134138691184220899348509 1550302009194082837255691)
              ·
                refine ⟨2325453013791124255883537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1550302009194082837255691 2325453013791124255883537)
                ·
                  refine ⟨1744089760343343191912653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2325453013791124255883537 1744089760343343191912653)
                  ·
                    refine ⟨654033660128753696967245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1744089760343343191912653 654033660128753696967245)
                    ·
                      rfl

theorem cell22_1910589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 3, 1, 2, 3].length) (baseStart_1910589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1910589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1910589 prefixEnd_1910589 := by exact prefixLift 1910589
  have htrace : WordTrace (prefixWord ++ tailWord_1910589) baseStart_1910589 baseEnd_1910589 := by
    simpa [prefixWord, tailWord_1910589, baseEnd_1910589] using wordTrace_append hprefix tailTrace_1910589
  have hstable : (prefixWord ++ tailWord_1910589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910589).length < 2 ^ (prefixWord ++ tailWord_1910589).sum := by decide
  have hdescent : baseEnd_1910589 < baseStart_1910589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910600 : List Nat := [2, 1, 3, 1, 1, 4, 2, 2, 3, 3]
def baseStart_1910600 : Nat := 118140960795 + 1910600 * 2 ^ 59
def prefixEnd_1910600 : Nat := 4983230072969 + 3 ^ 40 * 1910600 * 2
def baseEnd_1910600 : Nat := 654037425653553334942211

theorem tailTrace_1910600 : CollatzResearch.WordTrace tailWord_1910600 prefixEnd_1910600 654037425653553334942211 := by
  unfold tailWord_1910600
  simp only [CollatzResearch.WordTrace]
  refine ⟨34842653439114989673340627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46456871252153319564454169 34842653439114989673340627)
  ·
    refine ⟨52263980158672484510010941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34842653439114989673340627 52263980158672484510010941)
    ·
      refine ⟨19598992559502181691254103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52263980158672484510010941 19598992559502181691254103)
      ·
        refine ⟨29398488839253272536881155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19598992559502181691254103 29398488839253272536881155)
        ·
          refine ⟨44097733258879908805321733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29398488839253272536881155 44097733258879908805321733)
          ·
            refine ⟨8268324986039982900997825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44097733258879908805321733 8268324986039982900997825)
            ·
              refine ⟨6201243739529987175748369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8268324986039982900997825 6201243739529987175748369)
              ·
                refine ⟨4650932804647490381811277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6201243739529987175748369 4650932804647490381811277)
                ·
                  refine ⟨1744099801742808893179229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4650932804647490381811277 1744099801742808893179229)
                  ·
                    refine ⟨654037425653553334942211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1744099801742808893179229 654037425653553334942211)
                    ·
                      rfl

theorem cell22_1910600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 2, 3, 3].length) (baseStart_1910600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1910600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1910600 prefixEnd_1910600 := by exact prefixLift 1910600
  have htrace : WordTrace (prefixWord ++ tailWord_1910600) baseStart_1910600 baseEnd_1910600 := by
    simpa [prefixWord, tailWord_1910600, baseEnd_1910600] using wordTrace_append hprefix tailTrace_1910600
  have hstable : (prefixWord ++ tailWord_1910600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910600).length < 2 ^ (prefixWord ++ tailWord_1910600).sum := by decide
  have hdescent : baseEnd_1910600 < baseStart_1910600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910613 : List Nat := [1, 3, 2, 2, 2, 2, 1, 2, 7]
def baseStart_1910613 : Nat := 118140960795 + 1910613 * 2 ^ 59
def prefixEnd_1910613 : Nat := 4983230072969 + 3 ^ 40 * 1910613 * 2
def baseEnd_1910613 : Nat := 218013958606408544789057

theorem tailTrace_1910613 : CollatzResearch.WordTrace tailWord_1910613 prefixEnd_1910613 218013958606408544789057 := by
  unfold tailWord_1910613
  simp only [CollatzResearch.WordTrace]
  refine ⟨69685781027182882566904493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46457187351455255044602995 69685781027182882566904493)
  ·
    refine ⟨26132167885193580962589185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69685781027182882566904493 26132167885193580962589185)
    ·
      refine ⟨19599125913895185721941889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26132167885193580962589185 19599125913895185721941889)
      ·
        refine ⟨14699344435421389291456417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19599125913895185721941889 14699344435421389291456417)
        ·
          refine ⟨11024508326566041968592313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14699344435421389291456417 11024508326566041968592313)
          ·
            refine ⟨8268381244924531476444235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11024508326566041968592313 8268381244924531476444235)
            ·
              refine ⟨12402571867386797214666353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8268381244924531476444235 12402571867386797214666353)
              ·
                refine ⟨9301928900540097910999765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12402571867386797214666353 9301928900540097910999765)
                ·
                  refine ⟨218013958606408544789057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9301928900540097910999765 218013958606408544789057)
                  ·
                    rfl

theorem cell22_1910613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 2, 7].length) (baseStart_1910613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1910613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1910613 prefixEnd_1910613 := by exact prefixLift 1910613
  have htrace : WordTrace (prefixWord ++ tailWord_1910613) baseStart_1910613 baseEnd_1910613 := by
    simpa [prefixWord, tailWord_1910613, baseEnd_1910613] using wordTrace_append hprefix tailTrace_1910613
  have hstable : (prefixWord ++ tailWord_1910613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910613).length < 2 ^ (prefixWord ++ tailWord_1910613).sum := by decide
  have hdescent : baseEnd_1910613 < baseStart_1910613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910643 : List Nat := [1, 1, 1, 2, 2, 1, 3, 4, 3, 4]
def baseStart_1910643 : Nat := 118140960795 + 1910643 * 2 ^ 59
def prefixEnd_1910643 : Nat := 4983230072969 + 3 ^ 40 * 1910643 * 2
def baseEnd_1910643 : Nat := 654052145432315556117079

theorem tailTrace_1910643 : CollatzResearch.WordTrace tailWord_1910643 prefixEnd_1910643 654052145432315556117079 := by
  unfold tailWord_1910643
  simp only [CollatzResearch.WordTrace]
  refine ⟨69686875217074197690496583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46457916811382798460331055 69686875217074197690496583)
  ·
    refine ⟨104530312825611296535744875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69686875217074197690496583 104530312825611296535744875)
    ·
      refine ⟨156795469238416944803617313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104530312825611296535744875 156795469238416944803617313)
      ·
        refine ⟨117596601928812708602712985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156795469238416944803617313 117596601928812708602712985)
        ·
          refine ⟨88197451446609531452034739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117596601928812708602712985 88197451446609531452034739)
          ·
            refine ⟨132296177169914297178052109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88197451446609531452034739 132296177169914297178052109)
            ·
              refine ⟨49611066438717861441769541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132296177169914297178052109 49611066438717861441769541)
              ·
                refine ⟨9302074957259599020331789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49611066438717861441769541 9302074957259599020331789)
                ·
                  refine ⟨3488278108972349632624421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9302074957259599020331789 3488278108972349632624421)
                  ·
                    refine ⟨654052145432315556117079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3488278108972349632624421 654052145432315556117079)
                    ·
                      rfl

theorem cell22_1910643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4, 3, 4].length) (baseStart_1910643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1910643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1910643 prefixEnd_1910643 := by exact prefixLift 1910643
  have htrace : WordTrace (prefixWord ++ tailWord_1910643) baseStart_1910643 baseEnd_1910643 := by
    simpa [prefixWord, tailWord_1910643, baseEnd_1910643] using wordTrace_append hprefix tailTrace_1910643
  have hstable : (prefixWord ++ tailWord_1910643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910643).length < 2 ^ (prefixWord ++ tailWord_1910643).sum := by decide
  have hdescent : baseEnd_1910643 < baseStart_1910643 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910673 : List Nat := [1, 2, 2, 1, 1, 1, 5, 1, 3, 5]
def baseStart_1910673 : Nat := 118140960795 + 1910673 * 2 ^ 59
def prefixEnd_1910673 : Nat := 4983230072969 + 3 ^ 40 * 1910673 * 2
def baseEnd_1910673 : Nat := 654062415045405477866987

theorem tailTrace_1910673 : CollatzResearch.WordTrace tailWord_1910673 prefixEnd_1910673 654062415045405477866987 := by
  unfold tailWord_1910673
  simp only [CollatzResearch.WordTrace]
  refine ⟨69687969406965512814088673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46458646271310341876059115 69687969406965512814088673)
  ·
    refine ⟨52265977055224134610566505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69687969406965512814088673 52265977055224134610566505)
    ·
      refine ⟨39199482791418100957924879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52265977055224134610566505 39199482791418100957924879)
      ·
        refine ⟨58799224187127151436887319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39199482791418100957924879 58799224187127151436887319)
        ·
          refine ⟨88198836280690727155330979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58799224187127151436887319 88198836280690727155330979)
          ·
            refine ⟨132298254421036090732996469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88198836280690727155330979 132298254421036090732996469)
            ·
              refine ⟨12402961351972133506218419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 132298254421036090732996469 12402961351972133506218419)
              ·
                refine ⟨18604442027958200259327629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12402961351972133506218419 18604442027958200259327629)
                ·
                  refine ⟨6976665760484325097247861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18604442027958200259327629 6976665760484325097247861)
                  ·
                    refine ⟨654062415045405477866987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6976665760484325097247861 654062415045405477866987)
                    ·
                      rfl

theorem cell22_1910673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 5].length) (baseStart_1910673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1910673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1910673 prefixEnd_1910673 := by exact prefixLift 1910673
  have htrace : WordTrace (prefixWord ++ tailWord_1910673) baseStart_1910673 baseEnd_1910673 := by
    simpa [prefixWord, tailWord_1910673, baseEnd_1910673] using wordTrace_append hprefix tailTrace_1910673
  have hstable : (prefixWord ++ tailWord_1910673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910673).length < 2 ^ (prefixWord ++ tailWord_1910673).sum := by decide
  have hdescent : baseEnd_1910673 < baseStart_1910673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910677 : List Nat := [1, 3, 2, 1, 1, 3, 5, 1, 1, 4]
def baseStart_1910677 : Nat := 118140960795 + 1910677 * 2 ^ 59
def prefixEnd_1910677 : Nat := 4983230072969 + 3 ^ 40 * 1910677 * 2
def baseEnd_1910677 : Nat := 654063784327150800766975

theorem tailTrace_1910677 : CollatzResearch.WordTrace tailWord_1910677 prefixEnd_1910677 654063784327150800766975 := by
  unfold tailWord_1910677
  simp only [CollatzResearch.WordTrace]
  refine ⟨69688115298951021497234285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46458743532634014331489523 69688115298951021497234285)
  ·
    refine ⟨26133043237106633061462857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69688115298951021497234285 26133043237106633061462857)
    ·
      refine ⟨19599782427829974796097143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26133043237106633061462857 19599782427829974796097143)
      ·
        refine ⟨29399673641744962194145715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19599782427829974796097143 29399673641744962194145715)
        ·
          refine ⟨44099510462617443291218573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29399673641744962194145715 44099510462617443291218573)
          ·
            refine ⟨16537316423481541234206965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44099510462617443291218573 16537316423481541234206965)
            ·
              refine ⟨1550373414701394490706903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16537316423481541234206965 1550373414701394490706903)
              ·
                refine ⟨2325560122052091736060355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1550373414701394490706903 2325560122052091736060355)
                ·
                  refine ⟨3488340183078137604090533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2325560122052091736060355 3488340183078137604090533)
                  ·
                    refine ⟨654063784327150800766975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3488340183078137604090533 654063784327150800766975)
                    ·
                      rfl

theorem cell22_1910677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 5, 1, 1, 4].length) (baseStart_1910677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1910677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1910677 prefixEnd_1910677 := by exact prefixLift 1910677
  have htrace : WordTrace (prefixWord ++ tailWord_1910677) baseStart_1910677 baseEnd_1910677 := by
    simpa [prefixWord, tailWord_1910677, baseEnd_1910677] using wordTrace_append hprefix tailTrace_1910677
  have hstable : (prefixWord ++ tailWord_1910677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910677).length < 2 ^ (prefixWord ++ tailWord_1910677).sum := by decide
  have hdescent : baseEnd_1910677 < baseStart_1910677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910688 : List Nat := [2, 1, 1, 4, 1, 1, 1, 2, 3, 6]
def baseStart_1910688 : Nat := 118140960795 + 1910688 * 2 ^ 59
def prefixEnd_1910688 : Nat := 4983230072969 + 3 ^ 40 * 1910688 * 2
def baseEnd_1910688 : Nat := 654067549851950438741941

theorem tailTrace_1910688 : CollatzResearch.WordTrace tailWord_1910688 prefixEnd_1910688 654067549851950438741941 := by
  unfold tailWord_1910688
  simp only [CollatzResearch.WordTrace]
  refine ⟨34844258250955585187942359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46459011001274113583923145 34844258250955585187942359)
  ·
    refine ⟨52266387376433377781913539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34844258250955585187942359 52266387376433377781913539)
    ·
      refine ⟨78399581064650066672870309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52266387376433377781913539 78399581064650066672870309)
      ·
        refine ⟨14699921449621887501163183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78399581064650066672870309 14699921449621887501163183)
        ·
          refine ⟨22049882174432831251744775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14699921449621887501163183 22049882174432831251744775)
          ·
            refine ⟨33074823261649246877617163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22049882174432831251744775 33074823261649246877617163)
            ·
              refine ⟨49612234892473870316425745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33074823261649246877617163 49612234892473870316425745)
              ·
                refine ⟨37209176169355402737319309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49612234892473870316425745 37209176169355402737319309)
                ·
                  refine ⟨13953441063508276026494741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37209176169355402737319309 13953441063508276026494741)
                  ·
                    refine ⟨654067549851950438741941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13953441063508276026494741 654067549851950438741941)
                    ·
                      rfl

theorem cell22_1910688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 3, 6].length) (baseStart_1910688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1910688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1910688 prefixEnd_1910688 := by exact prefixLift 1910688
  have htrace : WordTrace (prefixWord ++ tailWord_1910688) baseStart_1910688 baseEnd_1910688 := by
    simpa [prefixWord, tailWord_1910688, baseEnd_1910688] using wordTrace_append hprefix tailTrace_1910688
  have hstable : (prefixWord ++ tailWord_1910688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910688).length < 2 ^ (prefixWord ++ tailWord_1910688).sum := by decide
  have hdescent : baseEnd_1910688 < baseStart_1910688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910692 : List Nat := [2, 3, 1, 2, 1, 4, 1, 4, 4]
def baseStart_1910692 : Nat := 118140960795 + 1910692 * 2 ^ 59
def prefixEnd_1910692 : Nat := 4983230072969 + 3 ^ 40 * 1910692 * 2
def baseEnd_1910692 : Nat := 218022973044565253880643

theorem tailTrace_1910692 : CollatzResearch.WordTrace tailWord_1910692 prefixEnd_1910692 218022973044565253880643 := by
  unfold tailWord_1910692
  simp only [CollatzResearch.WordTrace]
  refine ⟨34844331196948339529515165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46459108262597786039353553 34844331196948339529515165)
  ·
    refine ⟨13066624198855627323568187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34844331196948339529515165 13066624198855627323568187)
    ·
      refine ⟨19599936298283440985352281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13066624198855627323568187 19599936298283440985352281)
      ·
        refine ⟨14699952223712580739014211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19599936298283440985352281 14699952223712580739014211)
        ·
          refine ⟨22049928335568871108521317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14699952223712580739014211 22049928335568871108521317)
          ·
            refine ⟨4134361562919163332847747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22049928335568871108521317 4134361562919163332847747)
            ·
              refine ⟨6201542344378744999271621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4134361562919163332847747 6201542344378744999271621)
              ·
                refine ⟨1162789189571014687363429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6201542344378744999271621 1162789189571014687363429)
                ·
                  refine ⟨218022973044565253880643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1162789189571014687363429 218022973044565253880643)
                  ·
                    rfl

theorem cell22_1910692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 4, 4].length) (baseStart_1910692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1910692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1910692 prefixEnd_1910692 := by exact prefixLift 1910692
  have htrace : WordTrace (prefixWord ++ tailWord_1910692) baseStart_1910692 baseEnd_1910692 := by
    simpa [prefixWord, tailWord_1910692, baseEnd_1910692] using wordTrace_append hprefix tailTrace_1910692
  have hstable : (prefixWord ++ tailWord_1910692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910692).length < 2 ^ (prefixWord ++ tailWord_1910692).sum := by decide
  have hdescent : baseEnd_1910692 < baseStart_1910692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910720 : List Nat := [2, 1, 1, 2, 3, 2, 5, 6]
def baseStart_1910720 : Nat := 118140960795 + 1910720 * 2 ^ 59
def prefixEnd_1910720 : Nat := 4983230072969 + 3 ^ 40 * 1910720 * 2
def baseEnd_1910720 : Nat := 72675389345101446882427

theorem tailTrace_1910720 : CollatzResearch.WordTrace tailWord_1910720 prefixEnd_1910720 72675389345101446882427 := by
  unfold tailWord_1910720
  simp only [CollatzResearch.WordTrace]
  refine ⟨34844841818897619920524807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46459789091863493227366409 34844841818897619920524807)
  ·
    refine ⟨52267262728346429880787211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34844841818897619920524807 52267262728346429880787211)
    ·
      refine ⟨78400894092519644821180817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52267262728346429880787211 78400894092519644821180817)
      ·
        refine ⟨58800670569389733615885613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78400894092519644821180817 58800670569389733615885613)
        ·
          refine ⟨22050251463521150105957105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58800670569389733615885613 22050251463521150105957105)
          ·
            refine ⟨16537688597640862579467829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22050251463521150105957105 16537688597640862579467829)
            ·
              refine ⟨1550408306028830866825109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16537688597640862579467829 1550408306028830866825109)
              ·
                refine ⟨72675389345101446882427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1550408306028830866825109 72675389345101446882427)
                ·
                  rfl

theorem cell22_1910720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 5, 6].length) (baseStart_1910720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1910720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1910720 prefixEnd_1910720 := by exact prefixLift 1910720
  have htrace : WordTrace (prefixWord ++ tailWord_1910720) baseStart_1910720 baseEnd_1910720 := by
    simpa [prefixWord, tailWord_1910720, baseEnd_1910720] using wordTrace_append hprefix tailTrace_1910720
  have hstable : (prefixWord ++ tailWord_1910720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910720).length < 2 ^ (prefixWord ++ tailWord_1910720).sum := by decide
  have hdescent : baseEnd_1910720 < baseStart_1910720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910735 : List Nat := [1, 1, 2, 1, 1, 5, 1, 2, 5, 3]
def baseStart_1910735 : Nat := 118140960795 + 1910735 * 2 ^ 59
def prefixEnd_1910735 : Nat := 4983230072969 + 3 ^ 40 * 1910735 * 2
def baseEnd_1910735 : Nat := 654083638912457982816797

theorem tailTrace_1910735 : CollatzResearch.WordTrace tailWord_1910735 prefixEnd_1910735 654083638912457982816797 := by
  unfold tailWord_1910735
  simp only [CollatzResearch.WordTrace]
  refine ⟨69690230732740897402845659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46460153821827264935230439 69690230732740897402845659)
  ·
    refine ⟨104535346099111346104268489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69690230732740897402845659 104535346099111346104268489)
    ·
      refine ⟨78401509574333509578201367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104535346099111346104268489 78401509574333509578201367)
      ·
        refine ⟨117602264361500264367302051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78401509574333509578201367 117602264361500264367302051)
        ·
          refine ⟨176403396542250396550953077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117602264361500264367302051 176403396542250396550953077)
          ·
            refine ⟨16537818425835974676651851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 176403396542250396550953077 16537818425835974676651851)
            ·
              refine ⟨24806727638753962014977777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16537818425835974676651851 24806727638753962014977777)
              ·
                refine ⟨18605045729065471511233333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24806727638753962014977777 18605045729065471511233333)
                ·
                  refine ⟨1744223037099887954178125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18605045729065471511233333 1744223037099887954178125)
                  ·
                    refine ⟨654083638912457982816797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1744223037099887954178125 654083638912457982816797)
                    ·
                      rfl

theorem cell22_1910735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 5, 3].length) (baseStart_1910735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1910735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1910735 prefixEnd_1910735 := by exact prefixLift 1910735
  have htrace : WordTrace (prefixWord ++ tailWord_1910735) baseStart_1910735 baseEnd_1910735 := by
    simpa [prefixWord, tailWord_1910735, baseEnd_1910735] using wordTrace_append hprefix tailTrace_1910735
  have hstable : (prefixWord ++ tailWord_1910735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910735).length < 2 ^ (prefixWord ++ tailWord_1910735).sum := by decide
  have hdescent : baseEnd_1910735 < baseStart_1910735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910782 : List Nat := [4, 2, 2, 2, 1, 1, 1, 2, 7]
def baseStart_1910782 : Nat := 118140960795 + 1910782 * 2 ^ 59
def prefixEnd_1910782 : Nat := 4983230072969 + 3 ^ 40 * 1910782 * 2
def baseEnd_1910782 : Nat := 218033242657655175630551

theorem tailTrace_1910782 : CollatzResearch.WordTrace tailWord_1910782 prefixEnd_1910782 218033242657655175630551 := by
  unfold tailWord_1910782
  simp only [CollatzResearch.WordTrace]
  refine ⟨8711493120446328053725825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46461296642380416286537733 8711493120446328053725825)
  ·
    refine ⟨6533619840334746040294369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8711493120446328053725825 6533619840334746040294369)
    ·
      refine ⟨4900214880251059530220777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6533619840334746040294369 4900214880251059530220777)
      ·
        refine ⟨3675161160188294647665583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4900214880251059530220777 3675161160188294647665583)
        ·
          refine ⟨5512741740282441971498375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3675161160188294647665583 5512741740282441971498375)
          ·
            refine ⟨8269112610423662957247563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5512741740282441971498375 8269112610423662957247563)
            ·
              refine ⟨12403668915635494435871345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8269112610423662957247563 12403668915635494435871345)
              ·
                refine ⟨9302751686726620826903509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12403668915635494435871345 9302751686726620826903509)
                ·
                  refine ⟨218033242657655175630551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9302751686726620826903509 218033242657655175630551)
                  ·
                    rfl

theorem cell22_1910782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 2, 7].length) (baseStart_1910782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1910782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1910782 prefixEnd_1910782 := by exact prefixLift 1910782
  have htrace : WordTrace (prefixWord ++ tailWord_1910782) baseStart_1910782 baseEnd_1910782 := by
    simpa [prefixWord, tailWord_1910782, baseEnd_1910782] using wordTrace_append hprefix tailTrace_1910782
  have hstable : (prefixWord ++ tailWord_1910782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910782).length < 2 ^ (prefixWord ++ tailWord_1910782).sum := by decide
  have hdescent : baseEnd_1910782 < baseStart_1910782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910872 : List Nat := [2, 1, 2, 2, 1, 6, 1, 7]
def baseStart_1910872 : Nat := 118140960795 + 1910872 * 2 ^ 59
def prefixEnd_1910872 : Nat := 4983230072969 + 3 ^ 40 * 1910872 * 2
def baseEnd_1910872 : Nat := 72681170756915032460153

theorem tailTrace_1910872 : CollatzResearch.WordTrace tailWord_1910872 prefixEnd_1910872 72681170756915032460153 := by
  unfold tailWord_1910872
  simp only [CollatzResearch.WordTrace]
  refine ⟨34847613766622284900291435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46463485022163046533721913 34847613766622284900291435)
  ·
    refine ⟨52271420649933427350437153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34847613766622284900291435 52271420649933427350437153)
    ·
      refine ⟨39203565487450070512827865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52271420649933427350437153 39203565487450070512827865)
      ·
        refine ⟨29402674115587552884620899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39203565487450070512827865 29402674115587552884620899)
        ·
          refine ⟨44104011173381329326931349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29402674115587552884620899 44104011173381329326931349)
          ·
            refine ⟨2067375523752249812199907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 44104011173381329326931349 2067375523752249812199907)
            ·
              refine ⟨3101063285628374718299861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2067375523752249812199907 3101063285628374718299861)
              ·
                refine ⟨72681170756915032460153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3101063285628374718299861 72681170756915032460153)
                ·
                  rfl

theorem cell22_1910872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 7].length) (baseStart_1910872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1910872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1910872 prefixEnd_1910872 := by exact prefixLift 1910872
  have htrace : WordTrace (prefixWord ++ tailWord_1910872) baseStart_1910872 baseEnd_1910872 := by
    simpa [prefixWord, tailWord_1910872, baseEnd_1910872] using wordTrace_append hprefix tailTrace_1910872
  have hstable : (prefixWord ++ tailWord_1910872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910872).length < 2 ^ (prefixWord ++ tailWord_1910872).sum := by decide
  have hdescent : baseEnd_1910872 < baseStart_1910872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910917 : List Nat := [1, 3, 1, 1, 5, 2, 1, 1, 7]
def baseStart_1910917 : Nat := 118140960795 + 1910917 * 2 ^ 59
def prefixEnd_1910917 : Nat := 4983230072969 + 3 ^ 40 * 1910917 * 2
def baseEnd_1910917 : Nat := 218048647077290058255413

theorem tailTrace_1910917 : CollatzResearch.WordTrace tailWord_1910917 prefixEnd_1910917 218048647077290058255413 := by
  unfold tailWord_1910917
  simp only [CollatzResearch.WordTrace]
  refine ⟨69696868818081542485971005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46464579212054361657314003 69696868818081542485971005)
  ·
    refine ⟨26136325806780578432239127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69696868818081542485971005 26136325806780578432239127)
    ·
      refine ⟨39204488710170867648358691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26136325806780578432239127 39204488710170867648358691)
      ·
        refine ⟨58806733065256301472538037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39204488710170867648358691 58806733065256301472538037)
        ·
          refine ⟨5513131224867778263050441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58806733065256301472538037 5513131224867778263050441)
          ·
            refine ⟨4134848418650833697287831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5513131224867778263050441 4134848418650833697287831)
            ·
              refine ⟨6202272627976250545931747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4134848418650833697287831 6202272627976250545931747)
              ·
                refine ⟨9303408941964375818897621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6202272627976250545931747 9303408941964375818897621)
                ·
                  refine ⟨218048647077290058255413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9303408941964375818897621 218048647077290058255413)
                  ·
                    rfl

theorem cell22_1910917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 1, 7].length) (baseStart_1910917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1910917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1910917 prefixEnd_1910917 := by exact prefixLift 1910917
  have htrace : WordTrace (prefixWord ++ tailWord_1910917) baseStart_1910917 baseEnd_1910917 := by
    simpa [prefixWord, tailWord_1910917, baseEnd_1910917] using wordTrace_append hprefix tailTrace_1910917
  have hstable : (prefixWord ++ tailWord_1910917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910917).length < 2 ^ (prefixWord ++ tailWord_1910917).sum := by decide
  have hdescent : baseEnd_1910917 < baseStart_1910917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1910998 : List Nat := [5, 2, 1, 2, 1, 1, 3, 2, 1, 4]
def baseStart_1910998 : Nat := 118140960795 + 1910998 * 2 ^ 59
def prefixEnd_1910998 : Nat := 4983230072969 + 3 ^ 40 * 1910998 * 2
def baseEnd_1910998 : Nat := 654173669187212963490991

theorem tailTrace_1910998 : CollatzResearch.WordTrace tailWord_1910998 prefixEnd_1910998 654173669187212963490991 := by
  unfold tailWord_1910998
  simp only [CollatzResearch.WordTrace]
  refine ⟨4356238945674255832479353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46466548753858728879779765 4356238945674255832479353)
  ·
    refine ⟨3267179209255691874359515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4356238945674255832479353 3267179209255691874359515)
    ·
      refine ⟨4900768813883537811539273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3267179209255691874359515 4900768813883537811539273)
      ·
        refine ⟨3675576610412653358654455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4900768813883537811539273 3675576610412653358654455)
        ·
          refine ⟨5513364915618980037981683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3675576610412653358654455 5513364915618980037981683)
          ·
            refine ⟨8270047373428470056972525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5513364915618980037981683 8270047373428470056972525)
            ·
              refine ⟨3101267765035676271364697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8270047373428470056972525 3101267765035676271364697)
              ·
                refine ⟨2325950823776757203523523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3101267765035676271364697 2325950823776757203523523)
                ·
                  refine ⟨3488926235665135805285285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2325950823776757203523523 3488926235665135805285285)
                  ·
                    refine ⟨654173669187212963490991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3488926235665135805285285 654173669187212963490991)
                    ·
                      rfl

theorem cell22_1910998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_1910998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1910998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1910998 prefixEnd_1910998 := by exact prefixLift 1910998
  have htrace : WordTrace (prefixWord ++ tailWord_1910998) baseStart_1910998 baseEnd_1910998 := by
    simpa [prefixWord, tailWord_1910998, baseEnd_1910998] using wordTrace_append hprefix tailTrace_1910998
  have hstable : (prefixWord ++ tailWord_1910998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1910998).length < 2 ^ (prefixWord ++ tailWord_1910998).sum := by decide
  have hdescent : baseEnd_1910998 < baseStart_1910998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1910998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911009 : List Nat := [1, 2, 3, 1, 3, 1, 4, 1, 2, 4]
def baseStart_1911009 : Nat := 118140960795 + 1911009 * 2 ^ 59
def prefixEnd_1911009 : Nat := 4983230072969 + 3 ^ 40 * 1911009 * 2
def baseEnd_1911009 : Nat := 654177434712012601465957

theorem tailTrace_1911009 : CollatzResearch.WordTrace tailWord_1911009 prefixEnd_1911009 654177434712012601465957 := by
  unfold tailWord_1911009
  simp only [CollatzResearch.WordTrace]
  refine ⟨69700224333748242198320081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46466816222498828132213387 69700224333748242198320081)
  ·
    refine ⟨52275168250311181648740061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69700224333748242198320081 52275168250311181648740061)
    ·
      refine ⟨19603188093866693118277523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52275168250311181648740061 19603188093866693118277523)
      ·
        refine ⟨29404782140800039677416285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19603188093866693118277523 29404782140800039677416285)
        ·
          refine ⟨11026793302800014879031107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29404782140800039677416285 11026793302800014879031107)
          ·
            refine ⟨16540189954200022318546661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11026793302800014879031107 16540189954200022318546661)
            ·
              refine ⟨3101285616412504184727499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16540189954200022318546661 3101285616412504184727499)
              ·
                refine ⟨4651928424618756277091249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3101285616412504184727499 4651928424618756277091249)
                ·
                  refine ⟨3488946318464067207818437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4651928424618756277091249 3488946318464067207818437)
                  ·
                    refine ⟨654177434712012601465957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3488946318464067207818437 654177434712012601465957)
                    ·
                      rfl

theorem cell22_1911009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 1, 2, 4].length) (baseStart_1911009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1911009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1911009 prefixEnd_1911009 := by exact prefixLift 1911009
  have htrace : WordTrace (prefixWord ++ tailWord_1911009) baseStart_1911009 baseEnd_1911009 := by
    simpa [prefixWord, tailWord_1911009, baseEnd_1911009] using wordTrace_append hprefix tailTrace_1911009
  have hstable : (prefixWord ++ tailWord_1911009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911009).length < 2 ^ (prefixWord ++ tailWord_1911009).sum := by decide
  have hdescent : baseEnd_1911009 < baseStart_1911009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911011 : List Nat := [1, 1, 1, 8, 1, 1, 1, 2, 1, 5]
def baseStart_1911011 : Nat := 118140960795 + 1911011 * 2 ^ 59
def prefixEnd_1911011 : Nat := 4983230072969 + 3 ^ 40 * 1911011 * 2
def baseEnd_1911011 : Nat := 654178119352885262915951

theorem tailTrace_1911011 : CollatzResearch.WordTrace tailWord_1911011 prefixEnd_1911011 654178119352885262915951 := by
  unfold tailWord_1911011
  simp only [CollatzResearch.WordTrace]
  refine ⟨69700297279740996539892887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46466864853160664359928591 69700297279740996539892887)
  ·
    refine ⟨104550445919611494809839331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69700297279740996539892887 104550445919611494809839331)
    ·
      refine ⟨156825668879417242214758997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104550445919611494809839331 156825668879417242214758997)
      ·
        refine ⟨1837800807180670807204207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 156825668879417242214758997 1837800807180670807204207)
        ·
          refine ⟨2756701210771006210806311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1837800807180670807204207 2756701210771006210806311)
          ·
            refine ⟨4135051816156509316209467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2756701210771006210806311 4135051816156509316209467)
            ·
              refine ⟨6202577724234763974314201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4135051816156509316209467 6202577724234763974314201)
              ·
                refine ⟨4651933293176072980735651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6202577724234763974314201 4651933293176072980735651)
                ·
                  refine ⟨6977899939764109471103477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4651933293176072980735651 6977899939764109471103477)
                  ·
                    refine ⟨654178119352885262915951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6977899939764109471103477 654178119352885262915951)
                    ·
                      rfl

theorem cell22_1911011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 2, 1, 5].length) (baseStart_1911011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1911011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1911011 prefixEnd_1911011 := by exact prefixLift 1911011
  have htrace : WordTrace (prefixWord ++ tailWord_1911011) baseStart_1911011 baseEnd_1911011 := by
    simpa [prefixWord, tailWord_1911011, baseEnd_1911011] using wordTrace_append hprefix tailTrace_1911011
  have hstable : (prefixWord ++ tailWord_1911011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911011).length < 2 ^ (prefixWord ++ tailWord_1911011).sum := by decide
  have hdescent : baseEnd_1911011 < baseStart_1911011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911039 : List Nat := [1, 1, 2, 2, 1, 4, 2, 3, 3, 3]
def baseStart_1911039 : Nat := 118140960795 + 1911039 * 2 ^ 59
def prefixEnd_1911039 : Nat := 4983230072969 + 3 ^ 40 * 1911039 * 2
def baseEnd_1911039 : Nat := 654187704325102523215865

theorem tailTrace_1911039 : CollatzResearch.WordTrace tailWord_1911039 prefixEnd_1911039 654187704325102523215865 := by
  unfold tailWord_1911039
  simp only [CollatzResearch.WordTrace]
  refine ⟨69701318523639557321912171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46467545682426371547941447 69701318523639557321912171)
  ·
    refine ⟨104551977785459335982868257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69701318523639557321912171 104551977785459335982868257)
    ·
      refine ⟨78413983339094501987151193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104551977785459335982868257 78413983339094501987151193)
      ·
        refine ⟨58810487504320876490363395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78413983339094501987151193 58810487504320876490363395)
        ·
          refine ⟨88215731256481314735545093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58810487504320876490363395 88215731256481314735545093)
          ·
            refine ⟨16540449610590246512914705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88215731256481314735545093 16540449610590246512914705)
            ·
              refine ⟨12405337207942684884686029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16540449610590246512914705 12405337207942684884686029)
              ·
                refine ⟨4652001452978506831757261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12405337207942684884686029 4652001452978506831757261)
                ·
                  refine ⟨1744500544866940061908973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4652001452978506831757261 1744500544866940061908973)
                  ·
                    refine ⟨654187704325102523215865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1744500544866940061908973 654187704325102523215865)
                    ·
                      rfl

theorem cell22_1911039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 3, 3, 3].length) (baseStart_1911039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1911039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1911039 prefixEnd_1911039 := by exact prefixLift 1911039
  have htrace : WordTrace (prefixWord ++ tailWord_1911039) baseStart_1911039 baseEnd_1911039 := by
    simpa [prefixWord, tailWord_1911039, baseEnd_1911039] using wordTrace_append hprefix tailTrace_1911039
  have hstable : (prefixWord ++ tailWord_1911039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911039).length < 2 ^ (prefixWord ++ tailWord_1911039).sum := by decide
  have hdescent : baseEnd_1911039 < baseStart_1911039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911079 : List Nat := [1, 1, 8, 1, 2, 1, 1, 2, 2, 3]
def baseStart_1911079 : Nat := 118140960795 + 1911079 * 2 ^ 59
def prefixEnd_1911079 : Nat := 4983230072969 + 3 ^ 40 * 1911079 * 2
def baseEnd_1911079 : Nat := 654201397142555752215743

theorem tailTrace_1911079 : CollatzResearch.WordTrace tailWord_1911079 prefixEnd_1911079 654201397142555752215743 := by
  unfold tailWord_1911079
  simp only [CollatzResearch.WordTrace]
  refine ⟨69702777443494644153368291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46468518295663096102245527 69702777443494644153368291)
  ·
    refine ⟨104554166165241966230052437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69702777443494644153368291 104554166165241966230052437)
    ·
      refine ⟨1225244134748929291758427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 104554166165241966230052437 1225244134748929291758427)
      ·
        refine ⟨1837866202123393937637641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1225244134748929291758427 1837866202123393937637641)
        ·
          refine ⟨1378399651592545453228231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1837866202123393937637641 1378399651592545453228231)
          ·
            refine ⟨2067599477388818179842347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1378399651592545453228231 2067599477388818179842347)
            ·
              refine ⟨3101399216083227269763521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2067599477388818179842347 3101399216083227269763521)
              ·
                refine ⟨2326049412062420452322641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3101399216083227269763521 2326049412062420452322641)
                ·
                  refine ⟨1744537059046815339241981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2326049412062420452322641 1744537059046815339241981)
                  ·
                    refine ⟨654201397142555752215743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1744537059046815339241981 654201397142555752215743)
                    ·
                      rfl

theorem cell22_1911079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_1911079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1911079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1911079 prefixEnd_1911079 := by exact prefixLift 1911079
  have htrace : WordTrace (prefixWord ++ tailWord_1911079) baseStart_1911079 baseEnd_1911079 := by
    simpa [prefixWord, tailWord_1911079, baseEnd_1911079] using wordTrace_append hprefix tailTrace_1911079
  have hstable : (prefixWord ++ tailWord_1911079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911079).length < 2 ^ (prefixWord ++ tailWord_1911079).sum := by decide
  have hdescent : baseEnd_1911079 < baseStart_1911079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911116 : List Nat := [2, 2, 1, 3, 2, 1, 4, 2, 1, 4]
def baseStart_1911116 : Nat := 118140960795 + 1911116 * 2 ^ 59
def prefixEnd_1911116 : Nat := 4983230072969 + 3 ^ 40 * 1911116 * 2
def baseEnd_1911116 : Nat := 654214062998699989040629

theorem tailTrace_1911116 : CollatzResearch.WordTrace tailWord_1911116 prefixEnd_1911116 654214062998699989040629 := by
  unfold tailWord_1911116
  simp only [CollatzResearch.WordTrace]
  refine ⟨34852063472180299736232601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46469417962907066314976801 34852063472180299736232601)
  ·
    refine ⟨26139047604135224802174451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34852063472180299736232601 26139047604135224802174451)
    ·
      refine ⟨39208571406202837203261677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26139047604135224802174451 39208571406202837203261677)
      ·
        refine ⟨14703214277326063951223129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39208571406202837203261677 14703214277326063951223129)
        ·
          refine ⟨11027410707994547963417347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14703214277326063951223129 11027410707994547963417347)
          ·
            refine ⟨16541116061991821945126021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11027410707994547963417347 16541116061991821945126021)
            ·
              refine ⟨3101459261623466614711129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16541116061991821945126021 3101459261623466614711129)
              ·
                refine ⟨2326094446217599961033347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3101459261623466614711129 2326094446217599961033347)
                ·
                  refine ⟨3489141669326399941550021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2326094446217599961033347 3489141669326399941550021)
                  ·
                    refine ⟨654214062998699989040629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3489141669326399941550021 654214062998699989040629)
                    ·
                      rfl

theorem cell22_1911116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 2, 1, 4].length) (baseStart_1911116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1911116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1911116 prefixEnd_1911116 := by exact prefixLift 1911116
  have htrace : WordTrace (prefixWord ++ tailWord_1911116) baseStart_1911116 baseEnd_1911116 := by
    simpa [prefixWord, tailWord_1911116, baseEnd_1911116] using wordTrace_append hprefix tailTrace_1911116
  have hstable : (prefixWord ++ tailWord_1911116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911116).length < 2 ^ (prefixWord ++ tailWord_1911116).sum := by decide
  have hdescent : baseEnd_1911116 < baseStart_1911116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911148 : List Nat := [2, 2, 1, 1, 7, 1, 1, 1, 6]
def baseStart_1911148 : Nat := 118140960795 + 1911148 * 2 ^ 59
def prefixEnd_1911148 : Nat := 4983230072969 + 3 ^ 40 * 1911148 * 2
def baseEnd_1911148 : Nat := 218075005750887524080177

theorem tailTrace_1911148 : CollatzResearch.WordTrace tailWord_1911148 prefixEnd_1911148 218075005750887524080177 := by
  unfold tailWord_1911148
  simp only [CollatzResearch.WordTrace]
  refine ⟨34852647040122334468815049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46470196053496445958420065 34852647040122334468815049)
  ·
    refine ⟨26139485280091750851611287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34852647040122334468815049 26139485280091750851611287)
    ·
      refine ⟨39209227920137626277416931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26139485280091750851611287 39209227920137626277416931)
      ·
        refine ⟨58813841880206439416125397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39209227920137626277416931 58813841880206439416125397)
        ·
          refine ⟨1378449419067338423815439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 58813841880206439416125397 1378449419067338423815439)
          ·
            refine ⟨2067674128601007635723159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1378449419067338423815439 2067674128601007635723159)
            ·
              refine ⟨3101511192901511453584739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2067674128601007635723159 3101511192901511453584739)
              ·
                refine ⟨4652266789352267180377109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3101511192901511453584739 4652266789352267180377109)
                ·
                  refine ⟨218075005750887524080177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4652266789352267180377109 218075005750887524080177)
                  ·
                    rfl

theorem cell22_1911148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 1, 6].length) (baseStart_1911148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1911148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1911148 prefixEnd_1911148 := by exact prefixLift 1911148
  have htrace : WordTrace (prefixWord ++ tailWord_1911148) baseStart_1911148 baseEnd_1911148 := by
    simpa [prefixWord, tailWord_1911148, baseEnd_1911148] using wordTrace_append hprefix tailTrace_1911148
  have hstable : (prefixWord ++ tailWord_1911148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911148).length < 2 ^ (prefixWord ++ tailWord_1911148).sum := by decide
  have hdescent : baseEnd_1911148 < baseStart_1911148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911163 : List Nat := [1, 1, 1, 1, 1, 7, 4, 1, 2, 3]
def baseStart_1911163 : Nat := 118140960795 + 1911163 * 2 ^ 59
def prefixEnd_1911163 : Nat := 4983230072969 + 3 ^ 40 * 1911163 * 2
def baseEnd_1911163 : Nat := 654230152059207533115485

theorem tailTrace_1911163 : CollatzResearch.WordTrace tailWord_1911163 prefixEnd_1911163 654230152059207533115485 := by
  unfold tailWord_1911163
  simp only [CollatzResearch.WordTrace]
  refine ⟨69705841175190326499426143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46470560783460217666284095 69705841175190326499426143)
  ·
    refine ⟨104558761762785489749139215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69705841175190326499426143 104558761762785489749139215)
    ·
      refine ⟨156838142644178234623708823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104558761762785489749139215 156838142644178234623708823)
      ·
        refine ⟨235257213966267351935563235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156838142644178234623708823 235257213966267351935563235)
        ·
          refine ⟨352885820949401027903344853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235257213966267351935563235 352885820949401027903344853)
          ·
            refine ⟨8270761428501586591484645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 352885820949401027903344853 8270761428501586591484645)
            ·
              refine ⟨1550767767844047485903371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8270761428501586591484645 1550767767844047485903371)
              ·
                refine ⟨2326151651766071228855057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1550767767844047485903371 2326151651766071228855057)
                ·
                  refine ⟨1744613738824553421641293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2326151651766071228855057 1744613738824553421641293)
                  ·
                    refine ⟨654230152059207533115485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1744613738824553421641293 654230152059207533115485)
                    ·
                      rfl

theorem cell22_1911163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 4, 1, 2, 3].length) (baseStart_1911163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1911163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1911163 prefixEnd_1911163 := by exact prefixLift 1911163
  have htrace : WordTrace (prefixWord ++ tailWord_1911163) baseStart_1911163 baseEnd_1911163 := by
    simpa [prefixWord, tailWord_1911163, baseEnd_1911163] using wordTrace_append hprefix tailTrace_1911163
  have hstable : (prefixWord ++ tailWord_1911163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911163).length < 2 ^ (prefixWord ++ tailWord_1911163).sum := by decide
  have hdescent : baseEnd_1911163 < baseStart_1911163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911204 : List Nat := [2, 3, 1, 2, 1, 1, 2, 3, 7]
def baseStart_1911204 : Nat := 118140960795 + 1911204 * 2 ^ 59
def prefixEnd_1911204 : Nat := 4983230072969 + 3 ^ 40 * 1911204 * 2
def baseEnd_1911204 : Nat := 218081395732365697613453

theorem tailTrace_1911204 : CollatzResearch.WordTrace tailWord_1911204 prefixEnd_1911204 218081395732365697613453 := by
  unfold tailWord_1911204
  simp only [CollatzResearch.WordTrace]
  refine ⟨34853668284020895250834333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46471557712027860334445777 34853668284020895250834333)
  ·
    refine ⟨13070125606507835719062875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34853668284020895250834333 13070125606507835719062875)
    ·
      refine ⟨19605188409761753578594313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13070125606507835719062875 19605188409761753578594313)
      ·
        refine ⟨14703891307321315183945735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19605188409761753578594313 14703891307321315183945735)
        ·
          refine ⟨22055836960981972775918603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14703891307321315183945735 22055836960981972775918603)
          ·
            refine ⟨33083755441472959163877905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22055836960981972775918603 33083755441472959163877905)
            ·
              refine ⟨24812816581104719372908429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33083755441472959163877905 24812816581104719372908429)
              ·
                refine ⟨9304806217914269764840661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24812816581104719372908429 9304806217914269764840661)
                ·
                  refine ⟨218081395732365697613453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9304806217914269764840661 218081395732365697613453)
                  ·
                    rfl

theorem cell22_1911204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3, 7].length) (baseStart_1911204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1911204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1911204 prefixEnd_1911204 := by exact prefixLift 1911204
  have htrace : WordTrace (prefixWord ++ tailWord_1911204) baseStart_1911204 baseEnd_1911204 := by
    simpa [prefixWord, tailWord_1911204, baseEnd_1911204] using wordTrace_append hprefix tailTrace_1911204
  have hstable : (prefixWord ++ tailWord_1911204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911204).length < 2 ^ (prefixWord ++ tailWord_1911204).sum := by decide
  have hdescent : baseEnd_1911204 < baseStart_1911204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911300 : List Nat := [2, 3, 2, 3, 1, 1, 3, 3, 4]
def baseStart_1911300 : Nat := 118140960795 + 1911300 * 2 ^ 59
def prefixEnd_1911300 : Nat := 4983230072969 + 3 ^ 40 * 1911300 * 2
def baseEnd_1911300 : Nat := 218092349986328280813355

theorem tailTrace_1911300 : CollatzResearch.WordTrace tailWord_1911300 prefixEnd_1911300 218092349986328280813355 := by
  unfold tailWord_1911300
  simp only [CollatzResearch.WordTrace]
  refine ⟨34855418987846999448581677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46473891983795999264775569 34855418987846999448581677)
  ·
    refine ⟨13070782120442624793218129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34855418987846999448581677 13070782120442624793218129)
    ·
      refine ⟨9803086590331968594913597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13070782120442624793218129 9803086590331968594913597)
      ·
        refine ⟨3676157471374488223092599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9803086590331968594913597 3676157471374488223092599)
        ·
          refine ⟨5514236207061732334638899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3676157471374488223092599 5514236207061732334638899)
          ·
            refine ⟨8271354310592598501958349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5514236207061732334638899 8271354310592598501958349)
            ·
              refine ⟨3101757866472224438234381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8271354310592598501958349 3101757866472224438234381)
              ·
                refine ⟨1163159199927084164337893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3101757866472224438234381 1163159199927084164337893)
                ·
                  refine ⟨218092349986328280813355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1163159199927084164337893 218092349986328280813355)
                  ·
                    rfl

theorem cell22_1911300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 3, 4].length) (baseStart_1911300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1911300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1911300 prefixEnd_1911300 := by exact prefixLift 1911300
  have htrace : WordTrace (prefixWord ++ tailWord_1911300) baseStart_1911300 baseEnd_1911300 := by
    simpa [prefixWord, tailWord_1911300, baseEnd_1911300] using wordTrace_append hprefix tailTrace_1911300
  have hstable : (prefixWord ++ tailWord_1911300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911300).length < 2 ^ (prefixWord ++ tailWord_1911300).sum := by decide
  have hdescent : baseEnd_1911300 < baseStart_1911300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911328 : List Nat := [2, 1, 1, 6, 2, 1, 2, 7]
def baseStart_1911328 : Nat := 118140960795 + 1911328 * 2 ^ 59
def prefixEnd_1911328 : Nat := 4983230072969 + 3 ^ 40 * 1911328 * 2
def baseEnd_1911328 : Nat := 72698514992355789193331

theorem tailTrace_1911328 : CollatzResearch.WordTrace tailWord_1911328 prefixEnd_1911328 72698514992355789193331 := by
  unfold tailWord_1911328
  simp only [CollatzResearch.WordTrace]
  refine ⟨34855929609796279839591319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46474572813061706452788425 34855929609796279839591319)
  ·
    refine ⟨52283894414694419759386979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34855929609796279839591319 52283894414694419759386979)
    ·
      refine ⟨78425841622041629639080469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52283894414694419759386979 78425841622041629639080469)
      ·
        refine ⟨3676211326033201389331897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 78425841622041629639080469 3676211326033201389331897)
        ·
          refine ⟨2757158494524901041998923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3676211326033201389331897 2757158494524901041998923)
          ·
            refine ⟨4135737741787351562998385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2757158494524901041998923 4135737741787351562998385)
            ·
              refine ⟨3101803306340513672248789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4135737741787351562998385 3101803306340513672248789)
              ·
                refine ⟨72698514992355789193331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3101803306340513672248789 72698514992355789193331)
                ·
                  rfl

theorem cell22_1911328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 7].length) (baseStart_1911328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1911328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1911328 prefixEnd_1911328 := by exact prefixLift 1911328
  have htrace : WordTrace (prefixWord ++ tailWord_1911328) baseStart_1911328 baseEnd_1911328 := by
    simpa [prefixWord, tailWord_1911328, baseEnd_1911328] using wordTrace_append hprefix tailTrace_1911328
  have hstable : (prefixWord ++ tailWord_1911328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911328).length < 2 ^ (prefixWord ++ tailWord_1911328).sum := by decide
  have hdescent : baseEnd_1911328 < baseStart_1911328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911332 : List Nat := [2, 3, 1, 5, 1, 1, 1, 3, 2, 3]
def baseStart_1911332 : Nat := 118140960795 + 1911332 * 2 ^ 59
def prefixEnd_1911332 : Nat := 4983230072969 + 3 ^ 40 * 1911332 * 2
def baseEnd_1911332 : Nat := 654288004212947425639967

theorem tailTrace_1911332 : CollatzResearch.WordTrace tailWord_1911332 prefixEnd_1911332 654288004212947425639967 := by
  unfold tailWord_1911332
  simp only [CollatzResearch.WordTrace]
  refine ⟨34856002555789034181164125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46474670074385378908218833 34856002555789034181164125)
  ·
    refine ⟨13071000958420887817936547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34856002555789034181164125 13071000958420887817936547)
    ·
      refine ⟨19606501437631331726904821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13071000958420887817936547 19606501437631331726904821)
      ·
        refine ⟨1838109509777937349397327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19606501437631331726904821 1838109509777937349397327)
        ·
          refine ⟨2757164264666906024095991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1838109509777937349397327 2757164264666906024095991)
          ·
            refine ⟨4135746397000359036143987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2757164264666906024095991 4135746397000359036143987)
            ·
              refine ⟨6203619595500538554215981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4135746397000359036143987 6203619595500538554215981)
              ·
                refine ⟨2326357348312701957830993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6203619595500538554215981 2326357348312701957830993)
                ·
                  refine ⟨1744768011234526468373245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2326357348312701957830993 1744768011234526468373245)
                  ·
                    refine ⟨654288004212947425639967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1744768011234526468373245 654288004212947425639967)
                    ·
                      rfl

theorem cell22_1911332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 3, 2, 3].length) (baseStart_1911332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1911332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1911332 prefixEnd_1911332 := by exact prefixLift 1911332
  have htrace : WordTrace (prefixWord ++ tailWord_1911332) baseStart_1911332 baseEnd_1911332 := by
    simpa [prefixWord, tailWord_1911332, baseEnd_1911332] using wordTrace_append hprefix tailTrace_1911332
  have hstable : (prefixWord ++ tailWord_1911332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911332).length < 2 ^ (prefixWord ++ tailWord_1911332).sum := by decide
  have hdescent : baseEnd_1911332 < baseStart_1911332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911377 : List Nat := [1, 2, 2, 1, 3, 3, 4, 2, 1, 3]
def baseStart_1911377 : Nat := 118140960795 + 1911377 * 2 ^ 59
def prefixEnd_1911377 : Nat := 4983230072969 + 3 ^ 40 * 1911377 * 2
def baseEnd_1911377 : Nat := 654303408632582308264829

theorem tailTrace_1911377 : CollatzResearch.WordTrace tailWord_1911377 prefixEnd_1911377 654303408632582308264829 := by
  unfold tailWord_1911377
  simp only [CollatzResearch.WordTrace]
  refine ⟨69713646396415041047716385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46475764264276694031810923 69713646396415041047716385)
  ·
    refine ⟨52285234797311280785787289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69713646396415041047716385 52285234797311280785787289)
    ·
      refine ⟨39213926097983460589340467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52285234797311280785787289 39213926097983460589340467)
      ·
        refine ⟨58820889146975190884010701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39213926097983460589340467 58820889146975190884010701)
        ·
          refine ⟨22057833430115696581504013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58820889146975190884010701 22057833430115696581504013)
          ·
            refine ⟨8271687536293386218064005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22057833430115696581504013 8271687536293386218064005)
            ·
              refine ⟨1550941413055009915887001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8271687536293386218064005 1550941413055009915887001)
              ·
                refine ⟨1163206059791257436915251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1550941413055009915887001 1163206059791257436915251)
                ·
                  refine ⟨1744809089686886155372877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1163206059791257436915251 1744809089686886155372877)
                  ·
                    refine ⟨654303408632582308264829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1744809089686886155372877 654303408632582308264829)
                    ·
                      rfl

theorem cell22_1911377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 4, 2, 1, 3].length) (baseStart_1911377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1911377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1911377 prefixEnd_1911377 := by exact prefixLift 1911377
  have htrace : WordTrace (prefixWord ++ tailWord_1911377) baseStart_1911377 baseEnd_1911377 := by
    simpa [prefixWord, tailWord_1911377, baseEnd_1911377] using wordTrace_append hprefix tailTrace_1911377
  have hstable : (prefixWord ++ tailWord_1911377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911377).length < 2 ^ (prefixWord ++ tailWord_1911377).sum := by decide
  have hdescent : baseEnd_1911377 < baseStart_1911377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911420 : List Nat := [2, 2, 2, 1, 1, 2, 6, 1, 1, 4]
def baseStart_1911420 : Nat := 118140960795 + 1911420 * 2 ^ 59
def prefixEnd_1911420 : Nat := 4983230072969 + 3 ^ 40 * 1911420 * 2
def baseEnd_1911420 : Nat := 654318128411344529439697

theorem tailTrace_1911420 : CollatzResearch.WordTrace tailWord_1911420 prefixEnd_1911420 654318128411344529439697 := by
  unfold tailWord_1911420
  simp only [CollatzResearch.WordTrace]
  refine ⟨34857607367629629695765857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46476809823506172927687809 34857607367629629695765857)
  ·
    refine ⟨26143205525722222271824393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34857607367629629695765857 26143205525722222271824393)
    ·
      refine ⟨19607404144291666703868295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26143205525722222271824393 19607404144291666703868295)
      ·
        refine ⟨29411106216437500055802443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19607404144291666703868295 29411106216437500055802443)
        ·
          refine ⟨44116659324656250083703665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29411106216437500055802443 44116659324656250083703665)
          ·
            refine ⟨33087494493492187562777749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44116659324656250083703665 33087494493492187562777749)
            ·
              refine ⟨1550976304382446292005207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 33087494493492187562777749 1550976304382446292005207)
              ·
                refine ⟨2326464456573669438007811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1550976304382446292005207 2326464456573669438007811)
                ·
                  refine ⟨3489696684860504157011717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2326464456573669438007811 3489696684860504157011717)
                  ·
                    refine ⟨654318128411344529439697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3489696684860504157011717 654318128411344529439697)
                    ·
                      rfl

theorem cell22_1911420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 6, 1, 1, 4].length) (baseStart_1911420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1911420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1911420 prefixEnd_1911420 := by exact prefixLift 1911420
  have htrace : WordTrace (prefixWord ++ tailWord_1911420) baseStart_1911420 baseEnd_1911420 := by
    simpa [prefixWord, tailWord_1911420, baseEnd_1911420] using wordTrace_append hprefix tailTrace_1911420
  have hstable : (prefixWord ++ tailWord_1911420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911420).length < 2 ^ (prefixWord ++ tailWord_1911420).sum := by decide
  have hdescent : baseEnd_1911420 < baseStart_1911420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911461 : List Nat := [1, 3, 1, 2, 1, 2, 1, 1, 1, 9]
def baseStart_1911461 : Nat := 118140960795 + 1911461 * 2 ^ 59
def prefixEnd_1911461 : Nat := 4983230072969 + 3 ^ 40 * 1911461 * 2
def baseEnd_1911461 : Nat := 654332163549234089164571

theorem tailTrace_1911461 : CollatzResearch.WordTrace tailWord_1911461 prefixEnd_1911461 654332163549234089164571 := by
  unfold tailWord_1911461
  simp only [CollatzResearch.WordTrace]
  refine ⟨69716710128110723393774237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46477806752073815595849491 69716710128110723393774237)
  ·
    refine ⟨26143766298041521272665339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69716710128110723393774237 26143766298041521272665339)
    ·
      refine ⟨39215649447062281908998009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26143766298041521272665339 39215649447062281908998009)
      ·
        refine ⟨29411737085296711431748507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39215649447062281908998009 29411737085296711431748507)
        ·
          refine ⟨44117605627945067147622761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29411737085296711431748507 44117605627945067147622761)
          ·
            refine ⟨33088204220958800360717071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44117605627945067147622761 33088204220958800360717071)
            ·
              refine ⟨49632306331438200541075607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33088204220958800360717071 49632306331438200541075607)
              ·
                refine ⟨74448459497157300811613411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49632306331438200541075607 74448459497157300811613411)
                ·
                  refine ⟨111672689245735951217420117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74448459497157300811613411 111672689245735951217420117)
                  ·
                    refine ⟨654332163549234089164571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 111672689245735951217420117 654332163549234089164571)
                    ·
                      rfl

theorem cell22_1911461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 9].length) (baseStart_1911461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1911461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1911461 prefixEnd_1911461 := by exact prefixLift 1911461
  have htrace : WordTrace (prefixWord ++ tailWord_1911461) baseStart_1911461 baseEnd_1911461 := by
    simpa [prefixWord, tailWord_1911461, baseEnd_1911461] using wordTrace_append hprefix tailTrace_1911461
  have hstable : (prefixWord ++ tailWord_1911461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911461).length < 2 ^ (prefixWord ++ tailWord_1911461).sum := by decide
  have hdescent : baseEnd_1911461 < baseStart_1911461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911553 : List Nat := [1, 2, 4, 1, 1, 1, 1, 5, 6]
def baseStart_1911553 : Nat := 118140960795 + 1911553 * 2 ^ 59
def prefixEnd_1911553 : Nat := 4983230072969 + 3 ^ 40 * 1911553 * 2
def baseEnd_1911553 : Nat := 218121219009792171954763

theorem tailTrace_1911553 : CollatzResearch.WordTrace tailWord_1911553 prefixEnd_1911553 218121219009792171954763 := by
  unfold tailWord_1911553
  simp only [CollatzResearch.WordTrace]
  refine ⟨69720065643777423106123313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46480043762518282070748875 69720065643777423106123313)
  ·
    refine ⟨52290049232833067329592485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69720065643777423106123313 52290049232833067329592485)
    ·
      refine ⟨9804384231156200124298591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52290049232833067329592485 9804384231156200124298591)
      ·
        refine ⟨14706576346734300186447887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9804384231156200124298591 14706576346734300186447887)
        ·
          refine ⟨22059864520101450279671831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14706576346734300186447887 22059864520101450279671831)
          ·
            refine ⟨33089796780152175419507747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22059864520101450279671831 33089796780152175419507747)
            ·
              refine ⟨49634695170228263129261621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33089796780152175419507747 49634695170228263129261621)
              ·
                refine ⟨4653252672208899668368277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49634695170228263129261621 4653252672208899668368277)
                ·
                  refine ⟨218121219009792171954763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4653252672208899668368277 218121219009792171954763)
                  ·
                    rfl

theorem cell22_1911553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 5, 6].length) (baseStart_1911553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1911553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1911553 prefixEnd_1911553 := by exact prefixLift 1911553
  have htrace : WordTrace (prefixWord ++ tailWord_1911553) baseStart_1911553 baseEnd_1911553 := by
    simpa [prefixWord, tailWord_1911553, baseEnd_1911553] using wordTrace_append hprefix tailTrace_1911553
  have hstable : (prefixWord ++ tailWord_1911553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911553).length < 2 ^ (prefixWord ++ tailWord_1911553).sum := by decide
  have hdescent : baseEnd_1911553 < baseStart_1911553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911585 : List Nat := [1, 2, 3, 2, 1, 2, 2, 2, 4, 3]
def baseStart_1911585 : Nat := 118140960795 + 1911585 * 2 ^ 59
def prefixEnd_1911585 : Nat := 4983230072969 + 3 ^ 40 * 1911585 * 2
def baseEnd_1911585 : Nat := 654374611283339099064191

theorem tailTrace_1911585 : CollatzResearch.WordTrace tailWord_1911585 prefixEnd_1911585 654374611283339099064191 := by
  unfold tailWord_1911585
  simp only [CollatzResearch.WordTrace]
  refine ⟨69721232779661492571288209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46480821853107661714192139 69721232779661492571288209)
  ·
    refine ⟨52290924584746119428466157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69721232779661492571288209 52290924584746119428466157)
    ·
      refine ⟨19609096719279794785674809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52290924584746119428466157 19609096719279794785674809)
      ·
        refine ⟨14706822539459846089256107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19609096719279794785674809 14706822539459846089256107)
        ·
          refine ⟨22060233809189769133884161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14706822539459846089256107 22060233809189769133884161)
          ·
            refine ⟨16545175356892326850413121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22060233809189769133884161 16545175356892326850413121)
            ·
              refine ⟨12408881517669245137809841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16545175356892326850413121 12408881517669245137809841)
              ·
                refine ⟨9306661138251933853357381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12408881517669245137809841 9306661138251933853357381)
                ·
                  refine ⟨1744998963422237597504509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9306661138251933853357381 1744998963422237597504509)
                  ·
                    refine ⟨654374611283339099064191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1744998963422237597504509 654374611283339099064191)
                    ·
                      rfl

theorem cell22_1911585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 4, 3].length) (baseStart_1911585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1911585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1911585 prefixEnd_1911585 := by exact prefixLift 1911585
  have htrace : WordTrace (prefixWord ++ tailWord_1911585) baseStart_1911585 baseEnd_1911585 := by
    simpa [prefixWord, tailWord_1911585, baseEnd_1911585] using wordTrace_append hprefix tailTrace_1911585
  have hstable : (prefixWord ++ tailWord_1911585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911585).length < 2 ^ (prefixWord ++ tailWord_1911585).sum := by decide
  have hdescent : baseEnd_1911585 < baseStart_1911585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911660 : List Nat := [2, 2, 1, 1, 4, 1, 2, 4, 5]
def baseStart_1911660 : Nat := 118140960795 + 1911660 * 2 ^ 59
def prefixEnd_1911660 : Nat := 4983230072969 + 3 ^ 40 * 1911660 * 2
def baseEnd_1911660 : Nat := 218133428438687967812987

theorem tailTrace_1911660 : CollatzResearch.WordTrace tailWord_1911660 prefixEnd_1911660 218133428438687967812987 := by
  unfold tailWord_1911660
  simp only [CollatzResearch.WordTrace]
  refine ⟨34861984127194890190134217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46482645502926520253512289 34861984127194890190134217)
  ·
    refine ⟨26146488095396167642600663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34861984127194890190134217 26146488095396167642600663)
    ·
      refine ⟨39219732143094251463900995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26146488095396167642600663 39219732143094251463900995)
      ·
        refine ⟨58829598214641377195851493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39219732143094251463900995 58829598214641377195851493)
        ·
          refine ⟨11030549665245258224222155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58829598214641377195851493 11030549665245258224222155)
          ·
            refine ⟨16545824497867887336333233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11030549665245258224222155 16545824497867887336333233)
            ·
              refine ⟨12409368373400915502249925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16545824497867887336333233 12409368373400915502249925)
              ·
                refine ⟨2326756570012671656671861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12409368373400915502249925 2326756570012671656671861)
                ·
                  refine ⟨218133428438687967812987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2326756570012671656671861 218133428438687967812987)
                  ·
                    rfl

theorem cell22_1911660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 5].length) (baseStart_1911660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1911660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1911660 prefixEnd_1911660 := by exact prefixLift 1911660
  have htrace : WordTrace (prefixWord ++ tailWord_1911660) baseStart_1911660 baseEnd_1911660 := by
    simpa [prefixWord, tailWord_1911660, baseEnd_1911660] using wordTrace_append hprefix tailTrace_1911660
  have hstable : (prefixWord ++ tailWord_1911660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911660).length < 2 ^ (prefixWord ++ tailWord_1911660).sum := by decide
  have hdescent : baseEnd_1911660 < baseStart_1911660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911677 : List Nat := [1, 4, 1, 1, 2, 1, 6, 1, 5]
def baseStart_1911677 : Nat := 118140960795 + 1911677 * 2 ^ 59
def prefixEnd_1911677 : Nat := 4983230072969 + 3 ^ 40 * 1911677 * 2
def baseEnd_1911677 : Nat := 218135368254493841921303

theorem tailTrace_1911677 : CollatzResearch.WordTrace tailWord_1911677 prefixEnd_1911677 218135368254493841921303 := by
  unfold tailWord_1911677
  simp only [CollatzResearch.WordTrace]
  refine ⟨69724588295328192283637285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46483058863552128189091523 69724588295328192283637285)
  ·
    refine ⟨13073360305374036053181991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69724588295328192283637285 13073360305374036053181991)
    ·
      refine ⟨19610040458061054079772987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13073360305374036053181991 19610040458061054079772987)
      ·
        refine ⟨29415060687091581119659481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19610040458061054079772987 29415060687091581119659481)
        ·
          refine ⟨22061295515318685839744611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29415060687091581119659481 22061295515318685839744611)
          ·
            refine ⟨33091943272978028759616917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22061295515318685839744611 33091943272978028759616917)
            ·
              refine ⟨1551184840920845098107043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 33091943272978028759616917 1551184840920845098107043)
              ·
                refine ⟨2326777261381267647160565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1551184840920845098107043 2326777261381267647160565)
                ·
                  refine ⟨218135368254493841921303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2326777261381267647160565 218135368254493841921303)
                  ·
                    rfl

theorem cell22_1911677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 6, 1, 5].length) (baseStart_1911677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1911677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1911677 prefixEnd_1911677 := by exact prefixLift 1911677
  have htrace : WordTrace (prefixWord ++ tailWord_1911677) baseStart_1911677 baseEnd_1911677 := by
    simpa [prefixWord, tailWord_1911677, baseEnd_1911677] using wordTrace_append hprefix tailTrace_1911677
  have hstable : (prefixWord ++ tailWord_1911677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911677).length < 2 ^ (prefixWord ++ tailWord_1911677).sum := by decide
  have hdescent : baseEnd_1911677 < baseStart_1911677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911735 : List Nat := [1, 1, 3, 1, 3, 1, 2, 2, 4, 4]
def baseStart_1911735 : Nat := 118140960795 + 1911735 * 2 ^ 59
def prefixEnd_1911735 : Nat := 4983230072969 + 3 ^ 40 * 1911735 * 2
def baseEnd_1911735 : Nat := 654425959348788707813731

theorem tailTrace_1911735 : CollatzResearch.WordTrace tailWord_1911735 prefixEnd_1911735 654425959348788707813731 := by
  unfold tailWord_1911735
  simp only [CollatzResearch.WordTrace]
  refine ⟨69726703729118068189248659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46484469152745378792832439 69726703729118068189248659)
  ·
    refine ⟨104590055593677102283872989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69726703729118068189248659 104590055593677102283872989)
    ·
      refine ⟨39221270847628913356452371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104590055593677102283872989 39221270847628913356452371)
      ·
        refine ⟨58831906271443370034678557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39221270847628913356452371 58831906271443370034678557)
        ·
          refine ⟨22061964851791263763004459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58831906271443370034678557 22061964851791263763004459)
          ·
            refine ⟨33092947277686895644506689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22061964851791263763004459 33092947277686895644506689)
            ·
              refine ⟨24819710458265171733380017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33092947277686895644506689 24819710458265171733380017)
              ·
                refine ⟨18614782843698878800035013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24819710458265171733380017 18614782843698878800035013)
                ·
                  refine ⟨3490271783193539775006565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18614782843698878800035013 3490271783193539775006565)
                  ·
                    refine ⟨654425959348788707813731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3490271783193539775006565 654425959348788707813731)
                    ·
                      rfl

theorem cell22_1911735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 4, 4].length) (baseStart_1911735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1911735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1911735 prefixEnd_1911735 := by exact prefixLift 1911735
  have htrace : WordTrace (prefixWord ++ tailWord_1911735) baseStart_1911735 baseEnd_1911735 := by
    simpa [prefixWord, tailWord_1911735, baseEnd_1911735] using wordTrace_append hprefix tailTrace_1911735
  have hstable : (prefixWord ++ tailWord_1911735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911735).length < 2 ^ (prefixWord ++ tailWord_1911735).sum := by decide
  have hdescent : baseEnd_1911735 < baseStart_1911735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911737 : List Nat := [1, 2, 1, 4, 2, 3, 2, 1, 1, 5]
def baseStart_1911737 : Nat := 118140960795 + 1911737 * 2 ^ 59
def prefixEnd_1911737 : Nat := 4983230072969 + 3 ^ 40 * 1911737 * 2
def baseEnd_1911737 : Nat := 654426643989661369263725

theorem tailTrace_1911737 : CollatzResearch.WordTrace tailWord_1911737 prefixEnd_1911737 654426643989661369263725 := by
  unfold tailWord_1911737
  simp only [CollatzResearch.WordTrace]
  refine ⟨69726776675110822530821465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46484517783407215020547643 69726776675110822530821465)
  ·
    refine ⟨52295082506333116898116099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69726776675110822530821465 52295082506333116898116099)
    ·
      refine ⟨78442623759499675347174149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52295082506333116898116099 78442623759499675347174149)
      ·
        refine ⟨14707991954906189127595153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78442623759499675347174149 14707991954906189127595153)
        ·
          refine ⟨11030993966179641845696365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14707991954906189127595153 11030993966179641845696365)
          ·
            refine ⟨4136622737317365692136137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11030993966179641845696365 4136622737317365692136137)
            ·
              refine ⟨3102467052988024269102103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4136622737317365692136137 3102467052988024269102103)
              ·
                refine ⟨4653700579482036403653155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3102467052988024269102103 4653700579482036403653155)
                ·
                  refine ⟨6980550869223054605479733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4653700579482036403653155 6980550869223054605479733)
                  ·
                    refine ⟨654426643989661369263725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6980550869223054605479733 654426643989661369263725)
                    ·
                      rfl

theorem cell22_1911737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 1, 1, 5].length) (baseStart_1911737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1911737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1911737 prefixEnd_1911737 := by exact prefixLift 1911737
  have htrace : WordTrace (prefixWord ++ tailWord_1911737) baseStart_1911737 baseEnd_1911737 := by
    simpa [prefixWord, tailWord_1911737, baseEnd_1911737] using wordTrace_append hprefix tailTrace_1911737
  have hstable : (prefixWord ++ tailWord_1911737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911737).length < 2 ^ (prefixWord ++ tailWord_1911737).sum := by decide
  have hdescent : baseEnd_1911737 < baseStart_1911737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911752 : List Nat := [2, 1, 3, 1, 5, 1, 1, 1, 1, 6]
def baseStart_1911752 : Nat := 118140960795 + 1911752 * 2 ^ 59
def prefixEnd_1911752 : Nat := 4983230072969 + 3 ^ 40 * 1911752 * 2
def baseEnd_1911752 : Nat := 654431778796206330138679

theorem tailTrace_1911752 : CollatzResearch.WordTrace tailWord_1911752 prefixEnd_1911752 654431778796206330138679 := by
  unfold tailWord_1911752
  simp only [CollatzResearch.WordTrace]
  refine ⟨34863661885028240046308755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46484882513370986728411673 34863661885028240046308755)
  ·
    refine ⟨52295492827542360069463133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34863661885028240046308755 52295492827542360069463133)
    ·
      refine ⟨19610809810328385026048675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52295492827542360069463133 19610809810328385026048675)
      ·
        refine ⟨29416214715492577539073013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19610809810328385026048675 29416214715492577539073013)
        ·
          refine ⟨2757770129577429144288095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29416214715492577539073013 2757770129577429144288095)
          ·
            refine ⟨4136655194366143716432143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2757770129577429144288095 4136655194366143716432143)
            ·
              refine ⟨6204982791549215574648215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4136655194366143716432143 6204982791549215574648215)
              ·
                refine ⟨9307474187323823361972323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6204982791549215574648215 9307474187323823361972323)
                ·
                  refine ⟨13961211280985735042958485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9307474187323823361972323 13961211280985735042958485)
                  ·
                    refine ⟨654431778796206330138679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13961211280985735042958485 654431778796206330138679)
                    ·
                      rfl

theorem cell22_1911752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 1, 1, 6].length) (baseStart_1911752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1911752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1911752 prefixEnd_1911752 := by exact prefixLift 1911752
  have htrace : WordTrace (prefixWord ++ tailWord_1911752) baseStart_1911752 baseEnd_1911752 := by
    simpa [prefixWord, tailWord_1911752, baseEnd_1911752] using wordTrace_append hprefix tailTrace_1911752
  have hstable : (prefixWord ++ tailWord_1911752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911752).length < 2 ^ (prefixWord ++ tailWord_1911752).sum := by decide
  have hdescent : baseEnd_1911752 < baseStart_1911752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911780 : List Nat := [2, 3, 1, 1, 1, 1, 2, 3, 2, 6]
def baseStart_1911780 : Nat := 118140960795 + 1911780 * 2 ^ 59
def prefixEnd_1911780 : Nat := 4983230072969 + 3 ^ 40 * 1911780 * 2
def baseEnd_1911780 : Nat := 654441363768423590438593

theorem tailTrace_1911780 : CollatzResearch.WordTrace tailWord_1911780 prefixEnd_1911780 654441363768423590438593 := by
  unfold tailWord_1911780
  simp only [CollatzResearch.WordTrace]
  refine ⟨34864172506977520437318397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46485563342636693916424529 34864172506977520437318397)
  ·
    refine ⟨13074064690116570163994399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34864172506977520437318397 13074064690116570163994399)
    ·
      refine ⟨19611097035174855245991599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13074064690116570163994399 19611097035174855245991599)
      ·
        refine ⟨29416645552762282868987399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19611097035174855245991599 29416645552762282868987399)
        ·
          refine ⟨44124968329143424303481099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29416645552762282868987399 44124968329143424303481099)
          ·
            refine ⟨66187452493715136455221649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44124968329143424303481099 66187452493715136455221649)
            ·
              refine ⟨49640589370286352341416237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66187452493715136455221649 49640589370286352341416237)
              ·
                refine ⟨18615221013857382128031089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49640589370286352341416237 18615221013857382128031089)
                ·
                  refine ⟨13961415760393036596023317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18615221013857382128031089 13961415760393036596023317)
                  ·
                    refine ⟨654441363768423590438593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13961415760393036596023317 654441363768423590438593)
                    ·
                      rfl

theorem cell22_1911780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 2, 6].length) (baseStart_1911780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1911780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1911780 prefixEnd_1911780 := by exact prefixLift 1911780
  have htrace : WordTrace (prefixWord ++ tailWord_1911780) baseStart_1911780 baseEnd_1911780 := by
    simpa [prefixWord, tailWord_1911780, baseEnd_1911780] using wordTrace_append hprefix tailTrace_1911780
  have hstable : (prefixWord ++ tailWord_1911780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911780).length < 2 ^ (prefixWord ++ tailWord_1911780).sum := by decide
  have hdescent : baseEnd_1911780 < baseStart_1911780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911816 : List Nat := [2, 1, 3, 2, 1, 3, 3, 3, 1, 3]
def baseStart_1911816 : Nat := 118140960795 + 1911816 * 2 ^ 59
def prefixEnd_1911816 : Nat := 4983230072969 + 3 ^ 40 * 1911816 * 2
def baseEnd_1911816 : Nat := 654453687304131496538483

theorem tailTrace_1911816 : CollatzResearch.WordTrace tailWord_1911816 prefixEnd_1911816 654453687304131496538483 := by
  unfold tailWord_1911816
  simp only [CollatzResearch.WordTrace]
  refine ⟨34864829020912309511473651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46486438694549746015298201 34864829020912309511473651)
  ·
    refine ⟨52297243531368464267210477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34864829020912309511473651 52297243531368464267210477)
    ·
      refine ⟨19611466324263174100203929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52297243531368464267210477 19611466324263174100203929)
      ·
        refine ⟨14708599743197380575152947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19611466324263174100203929 14708599743197380575152947)
        ·
          refine ⟨22062899614796070862729421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14708599743197380575152947 22062899614796070862729421)
          ·
            refine ⟨8273587355548526573523533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22062899614796070862729421 8273587355548526573523533)
            ·
              refine ⟨3102595258330697465071325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8273587355548526573523533 3102595258330697465071325)
              ·
                refine ⟨1163473221874011549401747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3102595258330697465071325 1163473221874011549401747)
                ·
                  refine ⟨1745209832811017324102621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1163473221874011549401747 1745209832811017324102621)
                  ·
                    refine ⟨654453687304131496538483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1745209832811017324102621 654453687304131496538483)
                    ·
                      rfl

theorem cell22_1911816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 3, 1, 3].length) (baseStart_1911816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1911816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1911816 prefixEnd_1911816 := by exact prefixLift 1911816
  have htrace : WordTrace (prefixWord ++ tailWord_1911816) baseStart_1911816 baseEnd_1911816 := by
    simpa [prefixWord, tailWord_1911816, baseEnd_1911816] using wordTrace_append hprefix tailTrace_1911816
  have hstable : (prefixWord ++ tailWord_1911816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911816).length < 2 ^ (prefixWord ++ tailWord_1911816).sum := by decide
  have hdescent : baseEnd_1911816 < baseStart_1911816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911872 : List Nat := [2, 1, 1, 2, 2, 3, 3, 2, 1, 5]
def baseStart_1911872 : Nat := 118140960795 + 1911872 * 2 ^ 59
def prefixEnd_1911872 : Nat := 4983230072969 + 3 ^ 40 * 1911872 * 2
def baseEnd_1911872 : Nat := 654472857248566017138311

theorem tailTrace_1911872 : CollatzResearch.WordTrace tailWord_1911872 prefixEnd_1911872 654472857248566017138311 := by
  unfold tailWord_1911872
  simp only [CollatzResearch.WordTrace]
  refine ⟨34865850264810870293492935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46487800353081160391323913 34865850264810870293492935)
  ·
    refine ⟨52298775397216305440239403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34865850264810870293492935 52298775397216305440239403)
    ·
      refine ⟨78448163095824458160359105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52298775397216305440239403 78448163095824458160359105)
      ·
        refine ⟨58836122321868343620269329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78448163095824458160359105 58836122321868343620269329)
        ·
          refine ⟨44127091741401257715201997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58836122321868343620269329 44127091741401257715201997)
          ·
            refine ⟨16547659403025471643200749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44127091741401257715201997 16547659403025471643200749)
            ·
              refine ⟨6205372276134551866200281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16547659403025471643200749 6205372276134551866200281)
              ·
                refine ⟨4654029207100913899650211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6205372276134551866200281 4654029207100913899650211)
                ·
                  refine ⟨6981043810651370849475317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4654029207100913899650211 6981043810651370849475317)
                  ·
                    refine ⟨654472857248566017138311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6981043810651370849475317 654472857248566017138311)
                    ·
                      rfl

theorem cell22_1911872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 2, 1, 5].length) (baseStart_1911872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1911872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1911872 prefixEnd_1911872 := by exact prefixLift 1911872
  have htrace : WordTrace (prefixWord ++ tailWord_1911872) baseStart_1911872 baseEnd_1911872 := by
    simpa [prefixWord, tailWord_1911872, baseEnd_1911872] using wordTrace_append hprefix tailTrace_1911872
  have hstable : (prefixWord ++ tailWord_1911872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911872).length < 2 ^ (prefixWord ++ tailWord_1911872).sum := by decide
  have hdescent : baseEnd_1911872 < baseStart_1911872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911889 : List Nat := [1, 2, 2, 1, 3, 1, 3, 4, 2, 3]
def baseStart_1911889 : Nat := 118140960795 + 1911889 * 2 ^ 59
def prefixEnd_1911889 : Nat := 4983230072969 + 3 ^ 40 * 1911889 * 2
def baseEnd_1911889 : Nat := 654478676695983639463259

theorem tailTrace_1911889 : CollatzResearch.WordTrace tailWord_1911889 prefixEnd_1911889 654478676695983639463259 := by
  unfold tailWord_1911889
  simp only [CollatzResearch.WordTrace]
  refine ⟨69732320570560152490354721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46488213713706768326903147 69732320570560152490354721)
  ·
    refine ⟨52299240427920114367766041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69732320570560152490354721 52299240427920114367766041)
    ·
      refine ⟨39224430320940085775824531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52299240427920114367766041 39224430320940085775824531)
      ·
        refine ⟨58836645481410128663736797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39224430320940085775824531 58836645481410128663736797)
        ·
          refine ⟨22063742055528798248901299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58836645481410128663736797 22063742055528798248901299)
          ·
            refine ⟨33095613083293197373351949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22063742055528798248901299 33095613083293197373351949)
            ·
              refine ⟨12410854906234949015006981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33095613083293197373351949 12410854906234949015006981)
              ·
                refine ⟨2327035294919052940313809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12410854906234949015006981 2327035294919052940313809)
                ·
                  refine ⟨1745276471189289705235357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2327035294919052940313809 1745276471189289705235357)
                  ·
                    refine ⟨654478676695983639463259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1745276471189289705235357 654478676695983639463259)
                    ·
                      rfl

theorem cell22_1911889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 4, 2, 3].length) (baseStart_1911889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1911889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1911889 prefixEnd_1911889 := by exact prefixLift 1911889
  have htrace : WordTrace (prefixWord ++ tailWord_1911889) baseStart_1911889 baseEnd_1911889 := by
    simpa [prefixWord, tailWord_1911889, baseEnd_1911889] using wordTrace_append hprefix tailTrace_1911889
  have hstable : (prefixWord ++ tailWord_1911889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911889).length < 2 ^ (prefixWord ++ tailWord_1911889).sum := by decide
  have hdescent : baseEnd_1911889 < baseStart_1911889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911906 : List Nat := [3, 3, 2, 2, 1, 2, 2, 1, 1, 5]
def baseStart_1911906 : Nat := 118140960795 + 1911906 * 2 ^ 59
def prefixEnd_1911906 : Nat := 4983230072969 + 3 ^ 40 * 1911906 * 2
def baseEnd_1911906 : Nat := 654484496143401261788207

theorem tailTrace_1911906 : CollatzResearch.WordTrace tailWord_1911906 prefixEnd_1911906 654484496143401261788207 := by
  unfold tailWord_1911906
  simp only [CollatzResearch.WordTrace]
  refine ⟨17433235152874641098430893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46488627074332376262482381 17433235152874641098430893)
  ·
    refine ⟨6537463182327990411911585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17433235152874641098430893 6537463182327990411911585)
    ·
      refine ⟨4903097386745992808933689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6537463182327990411911585 4903097386745992808933689)
      ·
        refine ⟨3677323040059494606700267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4903097386745992808933689 3677323040059494606700267)
        ·
          refine ⟨5515984560089241910050401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3677323040059494606700267 5515984560089241910050401)
          ·
            refine ⟨4136988420066931432537801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5515984560089241910050401 4136988420066931432537801)
            ·
              refine ⟨3102741315050198574403351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4136988420066931432537801 3102741315050198574403351)
              ·
                refine ⟨4654111972575297861605027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3102741315050198574403351 4654111972575297861605027)
                ·
                  refine ⟨6981167958862946792407541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4654111972575297861605027 6981167958862946792407541)
                  ·
                    refine ⟨654484496143401261788207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6981167958862946792407541 654484496143401261788207)
                    ·
                      rfl

theorem cell22_1911906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_1911906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1911906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1911906 prefixEnd_1911906 := by exact prefixLift 1911906
  have htrace : WordTrace (prefixWord ++ tailWord_1911906) baseStart_1911906 baseEnd_1911906 := by
    simpa [prefixWord, tailWord_1911906, baseEnd_1911906] using wordTrace_append hprefix tailTrace_1911906
  have hstable : (prefixWord ++ tailWord_1911906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911906).length < 2 ^ (prefixWord ++ tailWord_1911906).sum := by decide
  have hdescent : baseEnd_1911906 < baseStart_1911906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1911985 : List Nat := [1, 2, 2, 5, 1, 3, 1, 3, 1, 3]
def baseStart_1911985 : Nat := 118140960795 + 1911985 * 2 ^ 59
def prefixEnd_1911985 : Nat := 4983230072969 + 3 ^ 40 * 1911985 * 2
def baseEnd_1911985 : Nat := 654511539457871389062965

theorem tailTrace_1911985 : CollatzResearch.WordTrace tailWord_1911985 prefixEnd_1911985 654511539457871389062965 := by
  unfold tailWord_1911985
  simp only [CollatzResearch.WordTrace]
  refine ⟨69735821978212360885849409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46490547985474907257232939 69735821978212360885849409)
  ·
    refine ⟨52301866483659270664387057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69735821978212360885849409 52301866483659270664387057)
    ·
      refine ⟨39226399862744452998290293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52301866483659270664387057 39226399862744452998290293)
      ·
        refine ⟨3677474987132292468589715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39226399862744452998290293 3677474987132292468589715)
        ·
          refine ⟨5516212480698438702884573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3677474987132292468589715 5516212480698438702884573)
          ·
            refine ⟨2068579680261914513581715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5516212480698438702884573 2068579680261914513581715)
            ·
              refine ⟨3102869520392871770372573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2068579680261914513581715 3102869520392871770372573)
              ·
                refine ⟨1163576070147326913889715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3102869520392871770372573 1163576070147326913889715)
                ·
                  refine ⟨1745364105220990370834573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1163576070147326913889715 1745364105220990370834573)
                  ·
                    refine ⟨654511539457871389062965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1745364105220990370834573 654511539457871389062965)
                    ·
                      rfl

theorem cell22_1911985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 3, 1, 3].length) (baseStart_1911985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1911985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1911985 prefixEnd_1911985 := by exact prefixLift 1911985
  have htrace : WordTrace (prefixWord ++ tailWord_1911985) baseStart_1911985 baseEnd_1911985 := by
    simpa [prefixWord, tailWord_1911985, baseEnd_1911985] using wordTrace_append hprefix tailTrace_1911985
  have hstable : (prefixWord ++ tailWord_1911985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1911985).length < 2 ^ (prefixWord ++ tailWord_1911985).sum := by decide
  have hdescent : baseEnd_1911985 < baseStart_1911985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1911985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912002 : List Nat := [3, 5, 1, 1, 2, 2, 1, 1, 3, 3]
def baseStart_1912002 : Nat := 118140960795 + 1912002 * 2 ^ 59
def prefixEnd_1912002 : Nat := 4983230072969 + 3 ^ 40 * 1912002 * 2
def baseEnd_1912002 : Nat := 654517358905289011387913

theorem tailTrace_1912002 : CollatzResearch.WordTrace tailWord_1912002 prefixEnd_1912002 654517358905289011387913 := by
  unfold tailWord_1912002
  simp only [CollatzResearch.WordTrace]
  refine ⟨17434110504787693197304565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46490961346100515192812173 17434110504787693197304565)
  ·
    refine ⟨1634447859823846237247303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17434110504787693197304565 1634447859823846237247303)
    ·
      refine ⟨2451671789735769355870955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1634447859823846237247303 2451671789735769355870955)
      ·
        refine ⟨3677507684603654033806433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2451671789735769355870955 3677507684603654033806433)
        ·
          refine ⟨2758130763452740525354825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3677507684603654033806433 2758130763452740525354825)
          ·
            refine ⟨2068598072589555394016119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2758130763452740525354825 2068598072589555394016119)
            ·
              refine ⟨3102897108884333091024179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2068598072589555394016119 3102897108884333091024179)
              ·
                refine ⟨4654345663326499636536269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3102897108884333091024179 4654345663326499636536269)
                ·
                  refine ⟨1745379623747437363701101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4654345663326499636536269 1745379623747437363701101)
                  ·
                    refine ⟨654517358905289011387913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1745379623747437363701101 654517358905289011387913)
                    ·
                      rfl

theorem cell22_1912002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_1912002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1912002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1912002 prefixEnd_1912002 := by exact prefixLift 1912002
  have htrace : WordTrace (prefixWord ++ tailWord_1912002) baseStart_1912002 baseEnd_1912002 := by
    simpa [prefixWord, tailWord_1912002, baseEnd_1912002] using wordTrace_append hprefix tailTrace_1912002
  have hstable : (prefixWord ++ tailWord_1912002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912002).length < 2 ^ (prefixWord ++ tailWord_1912002).sum := by decide
  have hdescent : baseEnd_1912002 < baseStart_1912002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912060 : List Nat := [2, 2, 2, 1, 5, 2, 2, 2, 4]
def baseStart_1912060 : Nat := 118140960795 + 1912060 * 2 ^ 59
def prefixEnd_1912060 : Nat := 4983230072969 + 3 ^ 40 * 1912060 * 2
def baseEnd_1912060 : Nat := 218179071163532064479245

theorem tailTrace_1912060 : CollatzResearch.WordTrace tailWord_1912060 prefixEnd_1912060 218179071163532064479245 := by
  unfold tailWord_1912060
  simp only [CollatzResearch.WordTrace]
  refine ⟨34869278726470324347414817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46492371635293765796553089 34869278726470324347414817)
  ·
    refine ⟨26151959044852743260561113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34869278726470324347414817 26151959044852743260561113)
    ·
      refine ⟨19613969283639557445420835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26151959044852743260561113 19613969283639557445420835)
      ·
        refine ⟨29420953925459336168131253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19613969283639557445420835 29420953925459336168131253)
        ·
          refine ⟨2758214430511812765762305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29420953925459336168131253 2758214430511812765762305)
          ·
            refine ⟨2068660822883859574321729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2758214430511812765762305 2068660822883859574321729)
            ·
              refine ⟨1551495617162894680741297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2068660822883859574321729 1551495617162894680741297)
              ·
                refine ⟨1163621712872171010555973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1551495617162894680741297 1163621712872171010555973)
                ·
                  refine ⟨218179071163532064479245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1163621712872171010555973 218179071163532064479245)
                  ·
                    rfl

theorem cell22_1912060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 2, 2, 4].length) (baseStart_1912060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1912060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1912060 prefixEnd_1912060 := by exact prefixLift 1912060
  have htrace : WordTrace (prefixWord ++ tailWord_1912060) baseStart_1912060 baseEnd_1912060 := by
    simpa [prefixWord, tailWord_1912060, baseEnd_1912060] using wordTrace_append hprefix tailTrace_1912060
  have hstable : (prefixWord ++ tailWord_1912060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912060).length < 2 ^ (prefixWord ++ tailWord_1912060).sum := by decide
  have hdescent : baseEnd_1912060 < baseStart_1912060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912116 : List Nat := [2, 5, 1, 1, 1, 1, 3, 1, 7]
def baseStart_1912116 : Nat := 118140960795 + 1912116 * 2 ^ 59
def prefixEnd_1912116 : Nat := 4983230072969 + 3 ^ 40 * 1912116 * 2
def baseEnd_1912116 : Nat := 218185461145010238012521

theorem tailTrace_1912116 : CollatzResearch.WordTrace tailWord_1912116 prefixEnd_1912116 218185461145010238012521 := by
  unfold tailWord_1912116
  simp only [CollatzResearch.WordTrace]
  refine ⟨34870299970368885129434101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46493733293825180172578801 34870299970368885129434101)
  ·
    refine ⟨3269090622222082980884447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34870299970368885129434101 3269090622222082980884447)
    ·
      refine ⟨4903635933333124471326671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3269090622222082980884447 4903635933333124471326671)
      ·
        refine ⟨7355453899999686706990007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4903635933333124471326671 7355453899999686706990007)
        ·
          refine ⟨11033180849999530060485011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7355453899999686706990007 11033180849999530060485011)
          ·
            refine ⟨16549771274999295090727517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11033180849999530060485011 16549771274999295090727517)
            ·
              refine ⟨6206164228124735659022819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16549771274999295090727517 6206164228124735659022819)
              ·
                refine ⟨9309246342187103488534229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6206164228124735659022819 9309246342187103488534229)
                ·
                  refine ⟨218185461145010238012521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9309246342187103488534229 218185461145010238012521)
                  ·
                    rfl

theorem cell22_1912116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_1912116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1912116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1912116 prefixEnd_1912116 := by exact prefixLift 1912116
  have htrace : WordTrace (prefixWord ++ tailWord_1912116) baseStart_1912116 baseEnd_1912116 := by
    simpa [prefixWord, tailWord_1912116, baseEnd_1912116] using wordTrace_append hprefix tailTrace_1912116
  have hstable : (prefixWord ++ tailWord_1912116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912116).length < 2 ^ (prefixWord ++ tailWord_1912116).sum := by decide
  have hdescent : baseEnd_1912116 < baseStart_1912116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912144 : List Nat := [2, 1, 1, 1, 1, 5, 1, 4, 6]
def baseStart_1912144 : Nat := 118140960795 + 1912144 * 2 ^ 59
def prefixEnd_1912144 : Nat := 4983230072969 + 3 ^ 40 * 1912144 * 2
def baseEnd_1912144 : Nat := 218188656135749324779159

theorem tailTrace_1912144 : CollatzResearch.WordTrace tailWord_1912144 prefixEnd_1912144 218188656135749324779159 := by
  unfold tailWord_1912144
  simp only [CollatzResearch.WordTrace]
  refine ⟨34870810592318165520443743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46494414123090887360591657 34870810592318165520443743)
  ·
    refine ⟨52306215888477248280665615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34870810592318165520443743 52306215888477248280665615)
    ·
      refine ⟨78459323832715872420998423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52306215888477248280665615 78459323832715872420998423)
      ·
        refine ⟨117688985749073808631497635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78459323832715872420998423 117688985749073808631497635)
        ·
          refine ⟨176533478623610712947246453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117688985749073808631497635 176533478623610712947246453)
          ·
            refine ⟨16550013620963504338804355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 176533478623610712947246453 16550013620963504338804355)
            ·
              refine ⟨24825020431445256508206533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16550013620963504338804355 24825020431445256508206533)
              ·
                refine ⟨4654691330895985595288725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24825020431445256508206533 4654691330895985595288725)
                ·
                  refine ⟨218188656135749324779159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4654691330895985595288725 218188656135749324779159)
                  ·
                    rfl

theorem cell22_1912144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 4, 6].length) (baseStart_1912144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1912144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1912144 prefixEnd_1912144 := by exact prefixLift 1912144
  have htrace : WordTrace (prefixWord ++ tailWord_1912144) baseStart_1912144 baseEnd_1912144 := by
    simpa [prefixWord, tailWord_1912144, baseEnd_1912144] using wordTrace_append hprefix tailTrace_1912144
  have hstable : (prefixWord ++ tailWord_1912144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912144).length < 2 ^ (prefixWord ++ tailWord_1912144).sum := by decide
  have hdescent : baseEnd_1912144 < baseStart_1912144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912159 : List Nat := [1, 1, 2, 3, 1, 2, 1, 3, 3, 5]
def baseStart_1912159 : Nat := 118140960795 + 1912159 * 2 ^ 59
def prefixEnd_1912159 : Nat := 4983230072969 + 3 ^ 40 * 1912159 * 2
def baseEnd_1912159 : Nat := 654571103213792935212431

theorem tailTrace_1912159 : CollatzResearch.WordTrace tailWord_1912159 prefixEnd_1912159 654571103213792935212431 := by
  unfold tailWord_1912159
  simp only [CollatzResearch.WordTrace]
  refine ⟨69742168279581988602683531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46494778853054659068455687 69742168279581988602683531)
  ·
    refine ⟨104613252419372982904025297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69742168279581988602683531 104613252419372982904025297)
    ·
      refine ⟨78459939314529737178018973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104613252419372982904025297 78459939314529737178018973)
      ·
        refine ⟨29422477242948651441757115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78459939314529737178018973 29422477242948651441757115)
        ·
          refine ⟨44133715864422977162635673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29422477242948651441757115 44133715864422977162635673)
          ·
            refine ⟨33100286898317232871976755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44133715864422977162635673 33100286898317232871976755)
            ·
              refine ⟨49650430347475849307965133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33100286898317232871976755 49650430347475849307965133)
              ·
                refine ⟨18618911380303443490486925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49650430347475849307965133 18618911380303443490486925)
                ·
                  refine ⟨6982091767613791308932597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18618911380303443490486925 6982091767613791308932597)
                  ·
                    refine ⟨654571103213792935212431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6982091767613791308932597 654571103213792935212431)
                    ·
                      rfl

theorem cell22_1912159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 3, 5].length) (baseStart_1912159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1912159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1912159 prefixEnd_1912159 := by exact prefixLift 1912159
  have htrace : WordTrace (prefixWord ++ tailWord_1912159) baseStart_1912159 baseEnd_1912159 := by
    simpa [prefixWord, tailWord_1912159, baseEnd_1912159] using wordTrace_append hprefix tailTrace_1912159
  have hstable : (prefixWord ++ tailWord_1912159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912159).length < 2 ^ (prefixWord ++ tailWord_1912159).sum := by decide
  have hdescent : baseEnd_1912159 < baseStart_1912159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912176 : List Nat := [2, 1, 1, 1, 4, 2, 1, 3, 4, 3]
def baseStart_1912176 : Nat := 118140960795 + 1912176 * 2 ^ 59
def prefixEnd_1912176 : Nat := 4983230072969 + 3 ^ 40 * 1912176 * 2
def baseEnd_1912176 : Nat := 654576922661210557537379

theorem tailTrace_1912176 : CollatzResearch.WordTrace tailWord_1912176 prefixEnd_1912176 654576922661210557537379 := by
  unfold tailWord_1912176
  simp only [CollatzResearch.WordTrace]
  refine ⟨34871394160260200253026191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46495192213680267004034921 34871394160260200253026191)
  ·
    refine ⟨52307091240390300379539287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34871394160260200253026191 52307091240390300379539287)
    ·
      refine ⟨78460636860585450569308931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52307091240390300379539287 78460636860585450569308931)
      ·
        refine ⟨117690955290878175853963397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78460636860585450569308931 117690955290878175853963397)
        ·
          refine ⟨22067054117039657972618137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117690955290878175853963397 22067054117039657972618137)
          ·
            refine ⟨16550290587779743479463603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22067054117039657972618137 16550290587779743479463603)
            ·
              refine ⟨24825435881669615219195405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16550290587779743479463603 24825435881669615219195405)
              ·
                refine ⟨9309538455626105707198277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24825435881669615219195405 9309538455626105707198277)
                ·
                  refine ⟨1745538460429894820099677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9309538455626105707198277 1745538460429894820099677)
                  ·
                    refine ⟨654576922661210557537379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1745538460429894820099677 654576922661210557537379)
                    ·
                      rfl

theorem cell22_1912176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3, 4, 3].length) (baseStart_1912176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1912176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1912176 prefixEnd_1912176 := by exact prefixLift 1912176
  have htrace : WordTrace (prefixWord ++ tailWord_1912176) baseStart_1912176 baseEnd_1912176 := by
    simpa [prefixWord, tailWord_1912176, baseEnd_1912176] using wordTrace_append hprefix tailTrace_1912176
  have hstable : (prefixWord ++ tailWord_1912176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912176).length < 2 ^ (prefixWord ++ tailWord_1912176).sum := by decide
  have hdescent : baseEnd_1912176 < baseStart_1912176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912210 : List Nat := [3, 2, 3, 3, 1, 1, 1, 2, 1, 5]
def baseStart_1912210 : Nat := 118140960795 + 1912210 * 2 ^ 59
def prefixEnd_1912210 : Nat := 4983230072969 + 3 ^ 40 * 1912210 * 2
def baseEnd_1912210 : Nat := 654588561556045802187275

theorem tailTrace_1912210 : CollatzResearch.WordTrace tailWord_1912210 prefixEnd_1912210 654588561556045802187275 := by
  unfold tailWord_1912210
  simp only [CollatzResearch.WordTrace]
  refine ⟨17436007100599306078197521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46496018934931482875193389 17436007100599306078197521)
  ·
    refine ⟨13077005325449479558648141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17436007100599306078197521 13077005325449479558648141)
    ·
      refine ⟨4903876997043554834493053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13077005325449479558648141 4903876997043554834493053)
      ·
        refine ⟨1838953873891333062934895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4903876997043554834493053 1838953873891333062934895)
        ·
          refine ⟨2758430810836999594402343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1838953873891333062934895 2758430810836999594402343)
          ·
            refine ⟨4137646216255499391603515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2758430810836999594402343 4137646216255499391603515)
            ·
              refine ⟨6206469324383249087405273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4137646216255499391603515 6206469324383249087405273)
              ·
                refine ⟨4654851993287436815553955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6206469324383249087405273 4654851993287436815553955)
                ·
                  refine ⟨6982277989931155223330933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4654851993287436815553955 6982277989931155223330933)
                  ·
                    refine ⟨654588561556045802187275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6982277989931155223330933 654588561556045802187275)
                    ·
                      rfl

theorem cell22_1912210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_1912210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1912210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1912210 prefixEnd_1912210 := by exact prefixLift 1912210
  have htrace : WordTrace (prefixWord ++ tailWord_1912210) baseStart_1912210 baseEnd_1912210 := by
    simpa [prefixWord, tailWord_1912210, baseEnd_1912210] using wordTrace_append hprefix tailTrace_1912210
  have hstable : (prefixWord ++ tailWord_1912210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912210).length < 2 ^ (prefixWord ++ tailWord_1912210).sum := by decide
  have hdescent : baseEnd_1912210 < baseStart_1912210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912285 : List Nat := [1, 4, 3, 1, 1, 4, 1, 2, 5]
def baseStart_1912285 : Nat := 118140960795 + 1912285 * 2 ^ 59
def prefixEnd_1912285 : Nat := 4983230072969 + 3 ^ 40 * 1912285 * 2
def baseEnd_1912285 : Nat := 218204745196256868854015

theorem tailTrace_1912285 : CollatzResearch.WordTrace tailWord_1912285 prefixEnd_1912285 218204745196256868854015 := by
  unfold tailWord_1912285
  simp only [CollatzResearch.WordTrace]
  refine ⟨69746763877125512121770309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46497842584750341414513539 69746763877125512121770309)
  ·
    refine ⟨13077518226961033522831933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69746763877125512121770309 13077518226961033522831933)
    ·
      refine ⟨4904069335110387571061975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13077518226961033522831933 4904069335110387571061975)
      ·
        refine ⟨7356104002665581356592963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4904069335110387571061975 7356104002665581356592963)
        ·
          refine ⟨11034156003998372034889445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7356104002665581356592963 11034156003998372034889445)
          ·
            refine ⟨2068904250749694756541771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11034156003998372034889445 2068904250749694756541771)
            ·
              refine ⟨3103356376124542134812657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2068904250749694756541771 3103356376124542134812657)
              ·
                refine ⟨2327517282093406601109493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3103356376124542134812657 2327517282093406601109493)
                ·
                  refine ⟨218204745196256868854015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2327517282093406601109493 218204745196256868854015)
                  ·
                    rfl

theorem cell22_1912285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 2, 5].length) (baseStart_1912285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1912285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1912285 prefixEnd_1912285 := by exact prefixLift 1912285
  have htrace : WordTrace (prefixWord ++ tailWord_1912285) baseStart_1912285 baseEnd_1912285 := by
    simpa [prefixWord, tailWord_1912285, baseEnd_1912285] using wordTrace_append hprefix tailTrace_1912285
  have hstable : (prefixWord ++ tailWord_1912285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912285).length < 2 ^ (prefixWord ++ tailWord_1912285).sum := by decide
  have hdescent : baseEnd_1912285 < baseStart_1912285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912311 : List Nat := [1, 1, 3, 1, 1, 1, 1, 7, 1, 5]
def baseStart_1912311 : Nat := 118140960795 + 1912311 * 2 ^ 59
def prefixEnd_1912311 : Nat := 4983230072969 + 3 ^ 40 * 1912311 * 2
def baseEnd_1912311 : Nat := 654623135920115205411965

theorem tailTrace_1912311 : CollatzResearch.WordTrace tailWord_1912311 prefixEnd_1912311 654623135920115205411965 := by
  unfold tailWord_1912311
  simp only [CollatzResearch.WordTrace]
  refine ⟨69747712175031318562216787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46498474783354212374811191 69747712175031318562216787)
  ·
    refine ⟨104621568262546977843325181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69747712175031318562216787 104621568262546977843325181)
    ·
      refine ⟨39233088098455116691246943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104621568262546977843325181 39233088098455116691246943)
      ·
        refine ⟨58849632147682675036870415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39233088098455116691246943 58849632147682675036870415)
        ·
          refine ⟨88274448221524012555305623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58849632147682675036870415 88274448221524012555305623)
          ·
            refine ⟨132411672332286018832958435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88274448221524012555305623 132411672332286018832958435)
            ·
              refine ⟨198617508498429028249437653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132411672332286018832958435 198617508498429028249437653)
              ·
                refine ⟨4655097855431930349596195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 198617508498429028249437653 4655097855431930349596195)
                ·
                  refine ⟨6982646783147895524394293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4655097855431930349596195 6982646783147895524394293)
                  ·
                    refine ⟨654623135920115205411965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6982646783147895524394293 654623135920115205411965)
                    ·
                      rfl

theorem cell22_1912311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 7, 1, 5].length) (baseStart_1912311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1912311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1912311 prefixEnd_1912311 := by exact prefixLift 1912311
  have htrace : WordTrace (prefixWord ++ tailWord_1912311) baseStart_1912311 baseEnd_1912311 := by
    simpa [prefixWord, tailWord_1912311, baseEnd_1912311] using wordTrace_append hprefix tailTrace_1912311
  have hstable : (prefixWord ++ tailWord_1912311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912311).length < 2 ^ (prefixWord ++ tailWord_1912311).sum := by decide
  have hdescent : baseEnd_1912311 < baseStart_1912311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912328 : List Nat := [2, 1, 3, 2, 1, 1, 3, 2, 4, 3]
def baseStart_1912328 : Nat := 118140960795 + 1912328 * 2 ^ 59
def prefixEnd_1912328 : Nat := 4983230072969 + 3 ^ 40 * 1912328 * 2
def baseEnd_1912328 : Nat := 654628955367532827736913

theorem tailTrace_1912328 : CollatzResearch.WordTrace tailWord_1912328 prefixEnd_1912328 654628955367532827736913 := by
  unfold tailWord_1912328
  simp only [CollatzResearch.WordTrace]
  refine ⟨34874166107984865232792819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46498888143979820310390425 34874166107984865232792819)
  ·
    refine ⟨52311249161977297849189229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34874166107984865232792819 52311249161977297849189229)
    ·
      refine ⟨19616718435741486693445961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52311249161977297849189229 19616718435741486693445961)
      ·
        refine ⟨14712538826806115020084471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19616718435741486693445961 14712538826806115020084471)
        ·
          refine ⟨22068808240209172530126707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14712538826806115020084471 22068808240209172530126707)
          ·
            refine ⟨33103212360313758795190061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22068808240209172530126707 33103212360313758795190061)
            ·
              refine ⟨12413704635117659548196273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33103212360313758795190061 12413704635117659548196273)
              ·
                refine ⟨9310278476338244661147205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12413704635117659548196273 9310278476338244661147205)
                ·
                  refine ⟨1745677214313420873965101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9310278476338244661147205 1745677214313420873965101)
                  ·
                    refine ⟨654628955367532827736913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1745677214313420873965101 654628955367532827736913)
                    ·
                      rfl

theorem cell22_1912328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2, 4, 3].length) (baseStart_1912328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1912328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1912328 prefixEnd_1912328 := by exact prefixLift 1912328
  have htrace : WordTrace (prefixWord ++ tailWord_1912328) baseStart_1912328 baseEnd_1912328 := by
    simpa [prefixWord, tailWord_1912328, baseEnd_1912328] using wordTrace_append hprefix tailTrace_1912328
  have hstable : (prefixWord ++ tailWord_1912328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912328).length < 2 ^ (prefixWord ++ tailWord_1912328).sum := by decide
  have hdescent : baseEnd_1912328 < baseStart_1912328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912330 : List Nat := [3, 1, 2, 2, 2, 2, 3, 3, 4]
def baseStart_1912330 : Nat := 118140960795 + 1912330 * 2 ^ 59
def prefixEnd_1912330 : Nat := 4983230072969 + 3 ^ 40 * 1912330 * 2
def baseEnd_1912330 : Nat := 218209880002801829728969

theorem tailTrace_1912330 : CollatzResearch.WordTrace tailWord_1912330 prefixEnd_1912330 218209880002801829728969 := by
  unfold tailWord_1912330
  simp only [CollatzResearch.WordTrace]
  refine ⟨17437101290490621201789611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46498936774641656538105629 17437101290490621201789611)
  ·
    refine ⟨26155651935735931802684417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17437101290490621201789611 26155651935735931802684417)
    ·
      refine ⟨19616738951801948852013313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26155651935735931802684417 19616738951801948852013313)
      ·
        refine ⟨14712554213851461639009985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19616738951801948852013313 14712554213851461639009985)
        ·
          refine ⟨11034415660388596229257489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14712554213851461639009985 11034415660388596229257489)
          ·
            refine ⟨8275811745291447171943117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11034415660388596229257489 8275811745291447171943117)
            ·
              refine ⟨3103429404484292689478669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8275811745291447171943117 3103429404484292689478669)
              ·
                refine ⟨1163786026681609758554501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3103429404484292689478669 1163786026681609758554501)
                ·
                  refine ⟨218209880002801829728969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1163786026681609758554501 218209880002801829728969)
                  ·
                    rfl

theorem cell22_1912330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 3, 4].length) (baseStart_1912330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1912330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1912330 prefixEnd_1912330 := by exact prefixLift 1912330
  have htrace : WordTrace (prefixWord ++ tailWord_1912330) baseStart_1912330 baseEnd_1912330 := by
    simpa [prefixWord, tailWord_1912330, baseEnd_1912330] using wordTrace_append hprefix tailTrace_1912330
  have hstable : (prefixWord ++ tailWord_1912330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912330).length < 2 ^ (prefixWord ++ tailWord_1912330).sum := by decide
  have hdescent : baseEnd_1912330 < baseStart_1912330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912341 : List Nat := [1, 3, 2, 1, 3, 2, 10]
def baseStart_1912341 : Nat := 118140960795 + 1912341 * 2 ^ 59
def prefixEnd_1912341 : Nat := 4983230072969 + 3 ^ 40 * 1912341 * 2
def baseEnd_1912341 : Nat := 24245681686415004709699

theorem tailTrace_1912341 : CollatzResearch.WordTrace tailWord_1912341 prefixEnd_1912341 24245681686415004709699 := by
  unfold tailWord_1912341
  simp only [CollatzResearch.WordTrace]
  refine ⟨69748806364922633685808877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46499204243281755790539251 69748806364922633685808877)
  ·
    refine ⟨26155802386845987632178329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69748806364922633685808877 26155802386845987632178329)
    ·
      refine ⟨19616851790134490724133747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26155802386845987632178329 19616851790134490724133747)
      ·
        refine ⟨29425277685201736086200621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19616851790134490724133747 29425277685201736086200621)
        ·
          refine ⟨11034479131950651032325233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29425277685201736086200621 11034479131950651032325233)
          ·
            refine ⟨8275859348962988274243925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11034479131950651032325233 8275859348962988274243925)
            ·
              refine ⟨24245681686415004709699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8275859348962988274243925 24245681686415004709699)
              ·
                rfl

theorem cell22_1912341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 10].length) (baseStart_1912341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1912341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1912341 prefixEnd_1912341 := by exact prefixLift 1912341
  have htrace : WordTrace (prefixWord ++ tailWord_1912341) baseStart_1912341 baseEnd_1912341 := by
    simpa [prefixWord, tailWord_1912341, baseEnd_1912341] using wordTrace_append hprefix tailTrace_1912341
  have hstable : (prefixWord ++ tailWord_1912341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912341).length < 2 ^ (prefixWord ++ tailWord_1912341).sum := by decide
  have hdescent : baseEnd_1912341 < baseStart_1912341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912407 : List Nat := [1, 1, 3, 2, 2, 4, 1, 4, 1, 3]
def baseStart_1912407 : Nat := 118140960795 + 1912407 * 2 ^ 59
def prefixEnd_1912407 : Nat := 4983230072969 + 3 ^ 40 * 1912407 * 2
def baseEnd_1912407 : Nat := 654655998682002955011671

theorem tailTrace_1912407 : CollatzResearch.WordTrace tailWord_1912407 prefixEnd_1912407 654655998682002955011671 := by
  unfold tailWord_1912407
  simp only [CollatzResearch.WordTrace]
  refine ⟨69751213582683526957711475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46500809055122351305140983 69751213582683526957711475)
  ·
    refine ⟨104626820374025290436567213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69751213582683526957711475 104626820374025290436567213)
    ·
      refine ⟨39235057640259483913712705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104626820374025290436567213 39235057640259483913712705)
      ·
        refine ⟨29426293230194612935284529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39235057640259483913712705 29426293230194612935284529)
        ·
          refine ⟨22069719922645959701463397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29426293230194612935284529 22069719922645959701463397)
          ·
            refine ⟨4138072485496117444024387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22069719922645959701463397 4138072485496117444024387)
            ·
              refine ⟨6207108728244176166036581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4138072485496117444024387 6207108728244176166036581)
              ·
                refine ⟨1163832886545783031131859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6207108728244176166036581 1163832886545783031131859)
                ·
                  refine ⟨1745749329818674546697789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1163832886545783031131859 1745749329818674546697789)
                  ·
                    refine ⟨654655998682002955011671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1745749329818674546697789 654655998682002955011671)
                    ·
                      rfl

theorem cell22_1912407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 4, 1, 3].length) (baseStart_1912407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1912407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1912407 prefixEnd_1912407 := by exact prefixLift 1912407
  have htrace : WordTrace (prefixWord ++ tailWord_1912407) baseStart_1912407 baseEnd_1912407 := by
    simpa [prefixWord, tailWord_1912407, baseEnd_1912407] using wordTrace_append hprefix tailTrace_1912407
  have hstable : (prefixWord ++ tailWord_1912407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912407).length < 2 ^ (prefixWord ++ tailWord_1912407).sum := by decide
  have hdescent : baseEnd_1912407 < baseStart_1912407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912480 : List Nat := [2, 1, 1, 4, 3, 1, 3, 1, 1, 5]
def baseStart_1912480 : Nat := 118140960795 + 1912480 * 2 ^ 59
def prefixEnd_1912480 : Nat := 4983230072969 + 3 ^ 40 * 1912480 * 2
def baseEnd_1912480 : Nat := 654680988073855097936447

theorem tailTrace_1912480 : CollatzResearch.WordTrace tailWord_1912480 prefixEnd_1912480 654680988073855097936447 := by
  unfold tailWord_1912480
  simp only [CollatzResearch.WordTrace]
  refine ⟨34876938055709530212559447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46502584074279373616745929 34876938055709530212559447)
  ·
    refine ⟨52315407083564295318839171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34876938055709530212559447 52315407083564295318839171)
    ·
      refine ⟨78473110625346442978258757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52315407083564295318839171 78473110625346442978258757)
      ·
        refine ⟨14713708242252458058423517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78473110625346442978258757 14713708242252458058423517)
        ·
          refine ⟨5517640590844671771908819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14713708242252458058423517 5517640590844671771908819)
          ·
            refine ⟨8276460886267007657863229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5517640590844671771908819 8276460886267007657863229)
            ·
              refine ⟨3103672832350127871698711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8276460886267007657863229 3103672832350127871698711)
              ·
                refine ⟨4655509248525191807548067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3103672832350127871698711 4655509248525191807548067)
                ·
                  refine ⟨6983263872787787711322101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4655509248525191807548067 6983263872787787711322101)
                  ·
                    refine ⟨654680988073855097936447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6983263872787787711322101 654680988073855097936447)
                    ·
                      rfl

theorem cell22_1912480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 1, 1, 5].length) (baseStart_1912480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1912480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1912480 prefixEnd_1912480 := by exact prefixLift 1912480
  have htrace : WordTrace (prefixWord ++ tailWord_1912480) baseStart_1912480 baseEnd_1912480 := by
    simpa [prefixWord, tailWord_1912480, baseEnd_1912480] using wordTrace_append hprefix tailTrace_1912480
  have hstable : (prefixWord ++ tailWord_1912480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912480).length < 2 ^ (prefixWord ++ tailWord_1912480).sum := by decide
  have hdescent : baseEnd_1912480 < baseStart_1912480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912510 : List Nat := [4, 2, 1, 1, 2, 4, 8]
def baseStart_1912510 : Nat := 118140960795 + 1912510 * 2 ^ 59
def prefixEnd_1912510 : Nat := 4983230072969 + 3 ^ 40 * 1912510 * 2
def baseEnd_1912510 : Nat := 24247824358775741469865

theorem tailTrace_1912510 : CollatzResearch.WordTrace tailWord_1912510 prefixEnd_1912510 24247824358775741469865 := by
  unfold tailWord_1912510
  simp only [CollatzResearch.WordTrace]
  refine ⟨8719371287663796943588873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46503313534206917032473989 8719371287663796943588873)
  ·
    refine ⟨6539528465747847707691655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8719371287663796943588873 6539528465747847707691655)
    ·
      refine ⟨9809292698621771561537483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6539528465747847707691655 9809292698621771561537483)
      ·
        refine ⟨14713939047932657342306225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9809292698621771561537483 14713939047932657342306225)
        ·
          refine ⟨11035454285949493006729669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14713939047932657342306225 11035454285949493006729669)
          ·
            refine ⟨2069147678615529938761813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11035454285949493006729669 2069147678615529938761813)
            ·
              refine ⟨24247824358775741469865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2069147678615529938761813 24247824358775741469865)
              ·
                rfl

theorem cell22_1912510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 8].length) (baseStart_1912510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1912510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1912510 prefixEnd_1912510 := by exact prefixLift 1912510
  have htrace : WordTrace (prefixWord ++ tailWord_1912510) baseStart_1912510 baseEnd_1912510 := by
    simpa [prefixWord, tailWord_1912510, baseEnd_1912510] using wordTrace_append hprefix tailTrace_1912510
  have hstable : (prefixWord ++ tailWord_1912510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912510).length < 2 ^ (prefixWord ++ tailWord_1912510).sum := by decide
  have hdescent : baseEnd_1912510 < baseStart_1912510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912553 : List Nat := [1, 2, 1, 1, 1, 2, 3, 2, 4, 5]
def baseStart_1912553 : Nat := 118140960795 + 1912553 * 2 ^ 59
def prefixEnd_1912553 : Nat := 4983230072969 + 3 ^ 40 * 1912553 * 2
def baseEnd_1912553 : Nat := 654705977465707240861223

theorem tailTrace_1912553 : CollatzResearch.WordTrace tailWord_1912553 prefixEnd_1912553 654705977465707240861223 := by
  unfold tailWord_1912553
  simp only [CollatzResearch.WordTrace]
  refine ⟨69756538640154593892526313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46504359093436395928350875 69756538640154593892526313)
  ·
    refine ⟨52317403980115945419394735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69756538640154593892526313 52317403980115945419394735)
    ·
      refine ⟨78476105970173918129092103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52317403980115945419394735 78476105970173918129092103)
      ·
        refine ⟨117714158955260877193638155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78476105970173918129092103 117714158955260877193638155)
        ·
          refine ⟨176571238432891315790457233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117714158955260877193638155 176571238432891315790457233)
          ·
            refine ⟨132428428824668486842842925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176571238432891315790457233 132428428824668486842842925)
            ·
              refine ⟨49660660809250682566066097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132428428824668486842842925 49660660809250682566066097)
              ·
                refine ⟨37245495606938011924549573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49660660809250682566066097 37245495606938011924549573)
                ·
                  refine ⟨6983530426300877235853045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37245495606938011924549573 6983530426300877235853045)
                  ·
                    refine ⟨654705977465707240861223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6983530426300877235853045 654705977465707240861223)
                    ·
                      rfl

theorem cell22_1912553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 4, 5].length) (baseStart_1912553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1912553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1912553 prefixEnd_1912553 := by exact prefixLift 1912553
  have htrace : WordTrace (prefixWord ++ tailWord_1912553) baseStart_1912553 baseEnd_1912553 := by
    simpa [prefixWord, tailWord_1912553, baseEnd_1912553] using wordTrace_append hprefix tailTrace_1912553
  have hstable : (prefixWord ++ tailWord_1912553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912553).length < 2 ^ (prefixWord ++ tailWord_1912553).sum := by decide
  have hdescent : baseEnd_1912553 < baseStart_1912553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912632 : List Nat := [2, 1, 2, 1, 3, 4, 1, 1, 4, 3]
def baseStart_1912632 : Nat := 118140960795 + 1912632 * 2 ^ 59
def prefixEnd_1912632 : Nat := 4983230072969 + 3 ^ 40 * 1912632 * 2
def baseEnd_1912632 : Nat := 654733020780177368135981

theorem tailTrace_1912632 : CollatzResearch.WordTrace tailWord_1912632 prefixEnd_1912632 654733020780177368135981 := by
  unfold tailWord_1912632
  simp only [CollatzResearch.WordTrace]
  refine ⟨34879710003434195192326075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46506280004578926923101433 34879710003434195192326075)
  ·
    refine ⟨52319565005151292788489113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34879710003434195192326075 52319565005151292788489113)
    ·
      refine ⟨39239673753863469591366835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52319565005151292788489113 39239673753863469591366835)
      ·
        refine ⟨58859510630795204387050253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39239673753863469591366835 58859510630795204387050253)
        ·
          refine ⟨22072316486548201645143845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58859510630795204387050253 22072316486548201645143845)
          ·
            refine ⟨4138559341227787808464471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22072316486548201645143845 4138559341227787808464471)
            ·
              refine ⟨6207839011841681712696707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4138559341227787808464471 6207839011841681712696707)
              ·
                refine ⟨9311758517762522569045061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6207839011841681712696707 9311758517762522569045061)
                ·
                  refine ⟨1745954722080472981695949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9311758517762522569045061 1745954722080472981695949)
                  ·
                    refine ⟨654733020780177368135981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1745954722080472981695949 654733020780177368135981)
                    ·
                      rfl

theorem cell22_1912632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 1, 4, 3].length) (baseStart_1912632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1912632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1912632 prefixEnd_1912632 := by exact prefixLift 1912632
  have htrace : WordTrace (prefixWord ++ tailWord_1912632) baseStart_1912632 baseEnd_1912632 := by
    simpa [prefixWord, tailWord_1912632, baseEnd_1912632] using wordTrace_append hprefix tailTrace_1912632
  have hstable : (prefixWord ++ tailWord_1912632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912632).length < 2 ^ (prefixWord ++ tailWord_1912632).sum := by decide
  have hdescent : baseEnd_1912632 < baseStart_1912632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912649 : List Nat := [1, 2, 1, 1, 2, 4, 5, 1, 2, 3]
def baseStart_1912649 : Nat := 118140960795 + 1912649 * 2 ^ 59
def prefixEnd_1912649 : Nat := 4983230072969 + 3 ^ 40 * 1912649 * 2
def baseEnd_1912649 : Nat := 654738840227594990460929

theorem tailTrace_1912649 : CollatzResearch.WordTrace tailWord_1912649 prefixEnd_1912649 654738840227594990460929 := by
  unfold tailWord_1912649
  simp only [CollatzResearch.WordTrace]
  refine ⟨69760040047806802288021001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46506693365204534858680667 69760040047806802288021001)
  ·
    refine ⟨52320030035855101716015751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69760040047806802288021001 52320030035855101716015751)
    ·
      refine ⟨78480045053782652574023627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52320030035855101716015751 78480045053782652574023627)
      ·
        refine ⟨117720067580673978861035441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78480045053782652574023627 117720067580673978861035441)
        ·
          refine ⟨88290050685505484145776581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117720067580673978861035441 88290050685505484145776581)
          ·
            refine ⟨16554384503532278277333109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88290050685505484145776581 16554384503532278277333109)
            ·
              refine ⟨1551973547206151088499979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16554384503532278277333109 1551973547206151088499979)
              ·
                refine ⟨2327960320809226632749969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1551973547206151088499979 2327960320809226632749969)
                ·
                  refine ⟨1745970240606919974562477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2327960320809226632749969 1745970240606919974562477)
                  ·
                    refine ⟨654738840227594990460929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1745970240606919974562477 654738840227594990460929)
                    ·
                      rfl

theorem cell22_1912649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 5, 1, 2, 3].length) (baseStart_1912649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1912649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1912649 prefixEnd_1912649 := by exact prefixLift 1912649
  have htrace : WordTrace (prefixWord ++ tailWord_1912649) baseStart_1912649 baseEnd_1912649 := by
    simpa [prefixWord, tailWord_1912649, baseEnd_1912649] using wordTrace_append hprefix tailTrace_1912649
  have hstable : (prefixWord ++ tailWord_1912649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912649).length < 2 ^ (prefixWord ++ tailWord_1912649).sum := by decide
  have hdescent : baseEnd_1912649 < baseStart_1912649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912668 : List Nat := [2, 2, 4, 2, 3, 1, 1, 3, 4]
def baseStart_1912668 : Nat := 118140960795 + 1912668 * 2 ^ 59
def prefixEnd_1912668 : Nat := 4983230072969 + 3 ^ 40 * 1912668 * 2
def baseEnd_1912668 : Nat := 218248448105295091411957

theorem tailTrace_1912668 : CollatzResearch.WordTrace tailWord_1912668 prefixEnd_1912668 218248448105295091411957 := by
  unfold tailWord_1912668
  simp only [CollatzResearch.WordTrace]
  refine ⟨34880366517368984266481329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46507155356491979021975105 34880366517368984266481329)
  ·
    refine ⟨26160274888026738199860997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34880366517368984266481329 26160274888026738199860997)
    ·
      refine ⟨4905051541505013412473937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26160274888026738199860997 4905051541505013412473937)
      ·
        refine ⟨3678788656128760059355453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4905051541505013412473937 3678788656128760059355453)
        ·
          refine ⟨1379545746048285022258295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3678788656128760059355453 1379545746048285022258295)
          ·
            refine ⟨2069318619072427533387443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1379545746048285022258295 2069318619072427533387443)
            ·
              refine ⟨3103977928608641300081165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2069318619072427533387443 3103977928608641300081165)
              ·
                refine ⟨1163991723228240487530437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3103977928608641300081165 1163991723228240487530437)
                ·
                  refine ⟨218248448105295091411957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1163991723228240487530437 218248448105295091411957)
                  ·
                    rfl

theorem cell22_1912668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 3, 4].length) (baseStart_1912668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1912668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1912668 prefixEnd_1912668 := by exact prefixLift 1912668
  have htrace : WordTrace (prefixWord ++ tailWord_1912668) baseStart_1912668 baseEnd_1912668 := by
    simpa [prefixWord, tailWord_1912668, baseEnd_1912668] using wordTrace_append hprefix tailTrace_1912668
  have hstable : (prefixWord ++ tailWord_1912668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912668).length < 2 ^ (prefixWord ++ tailWord_1912668).sum := by decide
  have hdescent : baseEnd_1912668 < baseStart_1912668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912707 : List Nat := [1, 1, 1, 3, 4, 3, 1, 3, 5]
def baseStart_1912707 : Nat := 118140960795 + 1912707 * 2 ^ 59
def prefixEnd_1912707 : Nat := 4983230072969 + 3 ^ 40 * 1912707 * 2
def baseEnd_1912707 : Nat := 218252898270967390836917

theorem tailTrace_1912707 : CollatzResearch.WordTrace tailWord_1912707 prefixEnd_1912707 218252898270967390836917 := by
  unfold tailWord_1912707
  simp only [CollatzResearch.WordTrace]
  refine ⟨69762155481596678193632375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46508103654397785462421583 69762155481596678193632375)
  ·
    refine ⟨104643233222395017290448563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69762155481596678193632375 104643233222395017290448563)
    ·
      refine ⟨156964849833592525935672845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104643233222395017290448563 156964849833592525935672845)
      ·
        refine ⟨58861818687597197225877317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156964849833592525935672845 58861818687597197225877317)
        ·
          refine ⟨11036591003924474479851997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58861818687597197225877317 11036591003924474479851997)
          ·
            refine ⟨4138721626471677929944499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11036591003924474479851997 4138721626471677929944499)
            ·
              refine ⟨6208082439707516894916749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4138721626471677929944499 6208082439707516894916749)
              ·
                refine ⟨2328030914890318835593781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6208082439707516894916749 2328030914890318835593781)
                ·
                  refine ⟨218252898270967390836917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2328030914890318835593781 218252898270967390836917)
                  ·
                    rfl

theorem cell22_1912707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 3, 5].length) (baseStart_1912707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1912707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1912707 prefixEnd_1912707 := by exact prefixLift 1912707
  have htrace : WordTrace (prefixWord ++ tailWord_1912707) baseStart_1912707 baseEnd_1912707 := by
    simpa [prefixWord, tailWord_1912707, baseEnd_1912707] using wordTrace_append hprefix tailTrace_1912707
  have hstable : (prefixWord ++ tailWord_1912707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912707).length < 2 ^ (prefixWord ++ tailWord_1912707).sum := by decide
  have hdescent : baseEnd_1912707 < baseStart_1912707 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912756 : List Nat := [2, 5, 2, 1, 2, 1, 1, 1, 2, 5]
def baseStart_1912756 : Nat := 118140960795 + 1912756 * 2 ^ 59
def prefixEnd_1912756 : Nat := 4983230072969 + 3 ^ 40 * 1912756 * 2
def baseEnd_1912756 : Nat := 654775468514282378035601

theorem tailTrace_1912756 : CollatzResearch.WordTrace tailWord_1912756 prefixEnd_1912756 654775468514282378035601 := by
  unfold tailWord_1912756
  simp only [CollatzResearch.WordTrace]
  refine ⟨34881971329209579781083061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46509295105612773041444081 34881971329209579781083061)
  ·
    refine ⟨3270184812113398104476537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34881971329209579781083061 3270184812113398104476537)
    ·
      refine ⟨2452638609085048578357403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3270184812113398104476537 2452638609085048578357403)
      ·
        refine ⟨3678957913627572867536105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2452638609085048578357403 3678957913627572867536105)
        ·
          refine ⟨2759218435220679650652079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3678957913627572867536105 2759218435220679650652079)
          ·
            refine ⟨4138827652831019475978119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2759218435220679650652079 4138827652831019475978119)
            ·
              refine ⟨6208241479246529213967179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4138827652831019475978119 6208241479246529213967179)
              ·
                refine ⟨9312362218869793820950769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6208241479246529213967179 9312362218869793820950769)
                ·
                  refine ⟨6984271664152345365713077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9312362218869793820950769 6984271664152345365713077)
                  ·
                    refine ⟨654775468514282378035601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6984271664152345365713077 654775468514282378035601)
                    ·
                      rfl

theorem cell22_1912756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_1912756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1912756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1912756 prefixEnd_1912756 := by exact prefixLift 1912756
  have htrace : WordTrace (prefixWord ++ tailWord_1912756) baseStart_1912756 baseEnd_1912756 := by
    simpa [prefixWord, tailWord_1912756, baseEnd_1912756] using wordTrace_append hprefix tailTrace_1912756
  have hstable : (prefixWord ++ tailWord_1912756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912756).length < 2 ^ (prefixWord ++ tailWord_1912756).sum := by decide
  have hdescent : baseEnd_1912756 < baseStart_1912756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912767 : List Nat := [1, 1, 2, 2, 2, 1, 6, 1, 1, 5]
def baseStart_1912767 : Nat := 118140960795 + 1912767 * 2 ^ 59
def prefixEnd_1912767 : Nat := 4983230072969 + 3 ^ 40 * 1912767 * 2
def baseEnd_1912767 : Nat := 654779234039082016010567

theorem tailTrace_1912767 : CollatzResearch.WordTrace tailWord_1912767 prefixEnd_1912767 654779234039082016010567 := by
  unfold tailWord_1912767
  simp only [CollatzResearch.WordTrace]
  refine ⟨69764343861379308440816555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46509562574252872293877703 69764343861379308440816555)
  ·
    refine ⟨104646515792068962661224833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69764343861379308440816555 104646515792068962661224833)
    ·
      refine ⟨78484886844051721995918625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104646515792068962661224833 78484886844051721995918625)
      ·
        refine ⟨58863665133038791496938969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78484886844051721995918625 58863665133038791496938969)
        ·
          refine ⟨44147748849779093622704227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58863665133038791496938969 44147748849779093622704227)
          ·
            refine ⟨66221623274668640434056341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44147748849779093622704227 66221623274668640434056341)
            ·
              refine ⟨3104138591000092520346391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 66221623274668640434056341 3104138591000092520346391)
              ·
                refine ⟨4656207886500138780519587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3104138591000092520346391 4656207886500138780519587)
                ·
                  refine ⟨6984311829750208170779381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4656207886500138780519587 6984311829750208170779381)
                  ·
                    refine ⟨654779234039082016010567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6984311829750208170779381 654779234039082016010567)
                    ·
                      rfl

theorem cell22_1912767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 1, 1, 5].length) (baseStart_1912767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1912767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1912767 prefixEnd_1912767 := by exact prefixLift 1912767
  have htrace : WordTrace (prefixWord ++ tailWord_1912767) baseStart_1912767 baseEnd_1912767 := by
    simpa [prefixWord, tailWord_1912767, baseEnd_1912767] using wordTrace_append hprefix tailTrace_1912767
  have hstable : (prefixWord ++ tailWord_1912767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912767).length < 2 ^ (prefixWord ++ tailWord_1912767).sum := by decide
  have hdescent : baseEnd_1912767 < baseStart_1912767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912782 : List Nat := [4, 1, 1, 1, 2, 2, 3, 1, 1, 6]
def baseStart_1912782 : Nat := 118140960795 + 1912782 * 2 ^ 59
def prefixEnd_1912782 : Nat := 4983230072969 + 3 ^ 40 * 1912782 * 2
def baseEnd_1912782 : Nat := 654784368845626976885521

theorem tailTrace_1912782 : CollatzResearch.WordTrace tailWord_1912782 prefixEnd_1912782 654784368845626976885521 := by
  unfold tailWord_1912782
  simp only [CollatzResearch.WordTrace]
  refine ⟨8720611369540620750326575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46509927304216644001741733 8720611369540620750326575)
  ·
    refine ⟨13080917054310931125489863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8720611369540620750326575 13080917054310931125489863)
    ·
      refine ⟨19621375581466396688234795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13080917054310931125489863 19621375581466396688234795)
      ·
        refine ⟨29432063372199595032352193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19621375581466396688234795 29432063372199595032352193)
        ·
          refine ⟨22074047529149696274264145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29432063372199595032352193 22074047529149696274264145)
          ·
            refine ⟨16555535646862272205698109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22074047529149696274264145 16555535646862272205698109)
            ·
              refine ⟨6208325867573352077136791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16555535646862272205698109 6208325867573352077136791)
              ·
                refine ⟨9312488801360028115705187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6208325867573352077136791 9312488801360028115705187)
                ·
                  refine ⟨13968733202040042173557781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9312488801360028115705187 13968733202040042173557781)
                  ·
                    refine ⟨654784368845626976885521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13968733202040042173557781 654784368845626976885521)
                    ·
                      rfl

theorem cell22_1912782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 1, 1, 6].length) (baseStart_1912782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1912782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1912782 prefixEnd_1912782 := by exact prefixLift 1912782
  have htrace : WordTrace (prefixWord ++ tailWord_1912782) baseStart_1912782 baseEnd_1912782 := by
    simpa [prefixWord, tailWord_1912782, baseEnd_1912782] using wordTrace_append hprefix tailTrace_1912782
  have hstable : (prefixWord ++ tailWord_1912782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912782).length < 2 ^ (prefixWord ++ tailWord_1912782).sum := by decide
  have hdescent : baseEnd_1912782 < baseStart_1912782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912829 : List Nat := [1, 4, 1, 1, 1, 2, 4, 2, 3, 3]
def baseStart_1912829 : Nat := 118140960795 + 1912829 * 2 ^ 59
def prefixEnd_1912829 : Nat := 4983230072969 + 3 ^ 40 * 1912829 * 2
def baseEnd_1912829 : Nat := 654800457906134520960377

theorem tailTrace_1912829 : CollatzResearch.WordTrace tailWord_1912829 prefixEnd_1912829 654800457906134520960377 := by
  unfold tailWord_1912829
  simp only [CollatzResearch.WordTrace]
  refine ⟨69766605187154693029573541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46511070124769795353049027 69766605187154693029573541)
  ·
    refine ⟨13081238472591504943045039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69766605187154693029573541 13081238472591504943045039)
    ·
      refine ⟨19621857708887257414567559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13081238472591504943045039 19621857708887257414567559)
      ·
        refine ⟨29432786563330886121851339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19621857708887257414567559 29432786563330886121851339)
        ·
          refine ⟨44149179844996329182777009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29432786563330886121851339 44149179844996329182777009)
          ·
            refine ⟨33111884883747246887082757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44149179844996329182777009 33111884883747246887082757)
            ·
              refine ⟨6208478415702608791328017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33111884883747246887082757 6208478415702608791328017)
              ·
                refine ⟨4656358811776956593496013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6208478415702608791328017 4656358811776956593496013)
                ·
                  refine ⟨1746134554416358722561005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4656358811776956593496013 1746134554416358722561005)
                  ·
                    refine ⟨654800457906134520960377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1746134554416358722561005 654800457906134520960377)
                    ·
                      rfl

theorem cell22_1912829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 2, 3, 3].length) (baseStart_1912829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1912829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1912829 prefixEnd_1912829 := by exact prefixLift 1912829
  have htrace : WordTrace (prefixWord ++ tailWord_1912829) baseStart_1912829 baseEnd_1912829 := by
    simpa [prefixWord, tailWord_1912829, baseEnd_1912829] using wordTrace_append hprefix tailTrace_1912829
  have hstable : (prefixWord ++ tailWord_1912829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912829).length < 2 ^ (prefixWord ++ tailWord_1912829).sum := by decide
  have hdescent : baseEnd_1912829 < baseStart_1912829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912863 : List Nat := [1, 1, 2, 4, 1, 2, 5, 2, 1, 3]
def baseStart_1912863 : Nat := 118140960795 + 1912863 * 2 ^ 59
def prefixEnd_1912863 : Nat := 4983230072969 + 3 ^ 40 * 1912863 * 2
def baseEnd_1912863 : Nat := 654812096800969765610273

theorem tailTrace_1912863 : CollatzResearch.WordTrace tailWord_1912863 prefixEnd_1912863 654812096800969765610273 := by
  unfold tailWord_1912863
  simp only [CollatzResearch.WordTrace]
  refine ⟨69767845269031516836311243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46511896846021011224207495 69767845269031516836311243)
  ·
    refine ⟨104651767903547275254466865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69767845269031516836311243 104651767903547275254466865)
    ·
      refine ⟨78488825927660456440850149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104651767903547275254466865 78488825927660456440850149)
      ·
        refine ⟨14716654861436335582659403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78488825927660456440850149 14716654861436335582659403)
        ·
          refine ⟨22074982292154503373989105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14716654861436335582659403 22074982292154503373989105)
          ·
            refine ⟨16556236719115877530491829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22074982292154503373989105 16556236719115877530491829)
            ·
              refine ⟨1552147192417113518483609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16556236719115877530491829 1552147192417113518483609)
              ·
                refine ⟨1164110394312835138862707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1552147192417113518483609 1164110394312835138862707)
                ·
                  refine ⟨1746165591469252708294061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1164110394312835138862707 1746165591469252708294061)
                  ·
                    refine ⟨654812096800969765610273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1746165591469252708294061 654812096800969765610273)
                    ·
                      rfl

theorem cell22_1912863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 5, 2, 1, 3].length) (baseStart_1912863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1912863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1912863 prefixEnd_1912863 := by exact prefixLift 1912863
  have htrace : WordTrace (prefixWord ++ tailWord_1912863) baseStart_1912863 baseEnd_1912863 := by
    simpa [prefixWord, tailWord_1912863, baseEnd_1912863] using wordTrace_append hprefix tailTrace_1912863
  have hstable : (prefixWord ++ tailWord_1912863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912863).length < 2 ^ (prefixWord ++ tailWord_1912863).sum := by decide
  have hdescent : baseEnd_1912863 < baseStart_1912863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912887 : List Nat := [1, 1, 3, 1, 2, 2, 2, 4, 6]
def baseStart_1912887 : Nat := 118140960795 + 1912887 * 2 ^ 59
def prefixEnd_1912887 : Nat := 4983230072969 + 3 ^ 40 * 1912887 * 2
def baseEnd_1912887 : Nat := 218273437497147234336733

theorem tailTrace_1912887 : CollatzResearch.WordTrace tailWord_1912887 prefixEnd_1912887 218273437497147234336733 := by
  unfold tailWord_1912887
  simp only [CollatzResearch.WordTrace]
  refine ⟨69768720620944568935184915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46512480413963045956789943 69768720620944568935184915)
  ·
    refine ⟨104653080931416853402777373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69768720620944568935184915 104653080931416853402777373)
    ·
      refine ⟨39244905349281320026041515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104653080931416853402777373 39244905349281320026041515)
      ·
        refine ⟨58867358023921980039062273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39244905349281320026041515 58867358023921980039062273)
        ·
          refine ⟨44150518517941485029296705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58867358023921980039062273 44150518517941485029296705)
          ·
            refine ⟨33112888888456113771972529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44150518517941485029296705 33112888888456113771972529)
            ·
              refine ⟨24834666666342085328979397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33112888888456113771972529 24834666666342085328979397)
              ·
                refine ⟨4656499999939140999183637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24834666666342085328979397 4656499999939140999183637)
                ·
                  refine ⟨218273437497147234336733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4656499999939140999183637 218273437497147234336733)
                  ·
                    rfl

theorem cell22_1912887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 4, 6].length) (baseStart_1912887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1912887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1912887 prefixEnd_1912887 := by exact prefixLift 1912887
  have htrace : WordTrace (prefixWord ++ tailWord_1912887) baseStart_1912887 baseEnd_1912887 := by
    simpa [prefixWord, tailWord_1912887, baseEnd_1912887] using wordTrace_append hprefix tailTrace_1912887
  have hstable : (prefixWord ++ tailWord_1912887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912887).length < 2 ^ (prefixWord ++ tailWord_1912887).sum := by decide
  have hdescent : baseEnd_1912887 < baseStart_1912887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912919 : List Nat := [1, 1, 3, 2, 2, 1, 2, 3, 4, 3]
def baseStart_1912919 : Nat := 118140960795 + 1912919 * 2 ^ 59
def prefixEnd_1912919 : Nat := 4983230072969 + 3 ^ 40 * 1912919 * 2
def baseEnd_1912919 : Nat := 654831266745404286210101

theorem tailTrace_1912919 : CollatzResearch.WordTrace tailWord_1912919 prefixEnd_1912919 654831266745404286210101 := by
  unfold tailWord_1912919
  simp only [CollatzResearch.WordTrace]
  refine ⟨69769887756828638400349811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46513258504552425600233207 69769887756828638400349811)
  ·
    refine ⟨104654831635242957600524717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69769887756828638400349811 104654831635242957600524717)
    ·
      refine ⟨39245561863216109100196769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104654831635242957600524717 39245561863216109100196769)
      ·
        refine ⟨29434171397412081825147577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39245561863216109100196769 29434171397412081825147577)
        ·
          refine ⟨22075628548059061368860683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29434171397412081825147577 22075628548059061368860683)
          ·
            refine ⟨33113442822088592053291025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22075628548059061368860683 33113442822088592053291025)
            ·
              refine ⟨24835082116566444039968269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33113442822088592053291025 24835082116566444039968269)
              ·
                refine ⟨9313155793712416514988101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24835082116566444039968269 9313155793712416514988101)
                ·
                  refine ⟨1746216711321078096560269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9313155793712416514988101 1746216711321078096560269)
                  ·
                    refine ⟨654831266745404286210101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1746216711321078096560269 654831266745404286210101)
                    ·
                      rfl

theorem cell22_1912919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3, 4, 3].length) (baseStart_1912919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1912919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1912919 prefixEnd_1912919 := by exact prefixLift 1912919
  have htrace : WordTrace (prefixWord ++ tailWord_1912919) baseStart_1912919 baseEnd_1912919 := by
    simpa [prefixWord, tailWord_1912919, baseEnd_1912919] using wordTrace_append hprefix tailTrace_1912919
  have hstable : (prefixWord ++ tailWord_1912919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912919).length < 2 ^ (prefixWord ++ tailWord_1912919).sum := by decide
  have hdescent : baseEnd_1912919 < baseStart_1912919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912951 : List Nat := [1, 1, 3, 1, 1, 7, 1, 1, 2, 4]
def baseStart_1912951 : Nat := 118140960795 + 1912951 * 2 ^ 59
def prefixEnd_1912951 : Nat := 4983230072969 + 3 ^ 40 * 1912951 * 2
def baseEnd_1912951 : Nat := 654842220999366869410003

theorem tailTrace_1912951 : CollatzResearch.WordTrace tailWord_1912951 prefixEnd_1912951 654842220999366869410003 := by
  unfold tailWord_1912951
  simp only [CollatzResearch.WordTrace]
  refine ⟨69771054892712707865514707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46514036595141805243676471 69771054892712707865514707)
  ·
    refine ⟨104656582339069061798272061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69771054892712707865514707 104656582339069061798272061)
    ·
      refine ⟨39246218377150898174352023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104656582339069061798272061 39246218377150898174352023)
      ·
        refine ⟨58869327565726347261528035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39246218377150898174352023 58869327565726347261528035)
        ·
          refine ⟨88303991348589520892292053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58869327565726347261528035 88303991348589520892292053)
          ·
            refine ⟨2069624797232566895913095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 88303991348589520892292053 2069624797232566895913095)
            ·
              refine ⟨3104437195848850343869643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2069624797232566895913095 3104437195848850343869643)
              ·
                refine ⟨4656655793773275515804465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3104437195848850343869643 4656655793773275515804465)
                ·
                  refine ⟨3492491845329956636853349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4656655793773275515804465 3492491845329956636853349)
                  ·
                    refine ⟨654842220999366869410003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3492491845329956636853349 654842220999366869410003)
                    ·
                      rfl

theorem cell22_1912951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 1, 2, 4].length) (baseStart_1912951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1912951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1912951 prefixEnd_1912951 := by exact prefixLift 1912951
  have htrace : WordTrace (prefixWord ++ tailWord_1912951) baseStart_1912951 baseEnd_1912951 := by
    simpa [prefixWord, tailWord_1912951, baseEnd_1912951] using wordTrace_append hprefix tailTrace_1912951
  have hstable : (prefixWord ++ tailWord_1912951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912951).length < 2 ^ (prefixWord ++ tailWord_1912951).sum := by decide
  have hdescent : baseEnd_1912951 < baseStart_1912951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1912981 : List Nat := [1, 3, 2, 1, 1, 1, 6, 1, 3, 3]
def baseStart_1912981 : Nat := 118140960795 + 1912981 * 2 ^ 59
def prefixEnd_1912981 : Nat := 4983230072969 + 3 ^ 40 * 1912981 * 2
def baseEnd_1912981 : Nat := 654852490612456791159911

theorem tailTrace_1912981 : CollatzResearch.WordTrace tailWord_1912981 prefixEnd_1912981 654852490612456791159911 := by
  unfold tailWord_1912981
  simp only [CollatzResearch.WordTrace]
  refine ⟨69772149082604022989106797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46514766055069348659404531 69772149082604022989106797)
  ·
    refine ⟨26164555905976508620915049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69772149082604022989106797 26164555905976508620915049)
    ·
      refine ⟨19623416929482381465686287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26164555905976508620915049 19623416929482381465686287)
      ·
        refine ⟨29435125394223572198529431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19623416929482381465686287 29435125394223572198529431)
        ·
          refine ⟨44152688091335358297794147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29435125394223572198529431 44152688091335358297794147)
          ·
            refine ⟨66229032137003037446691221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44152688091335358297794147 66229032137003037446691221)
            ·
              refine ⟨3104485881422017380313651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 66229032137003037446691221 3104485881422017380313651)
              ·
                refine ⟨4656728822133026070470477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3104485881422017380313651 4656728822133026070470477)
                ·
                  refine ⟨1746273308299884776426429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4656728822133026070470477 1746273308299884776426429)
                  ·
                    refine ⟨654852490612456791159911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1746273308299884776426429 654852490612456791159911)
                    ·
                      rfl

theorem cell22_1912981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 1, 3, 3].length) (baseStart_1912981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1912981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1912981 prefixEnd_1912981 := by exact prefixLift 1912981
  have htrace : WordTrace (prefixWord ++ tailWord_1912981) baseStart_1912981 baseEnd_1912981 := by
    simpa [prefixWord, tailWord_1912981, baseEnd_1912981] using wordTrace_append hprefix tailTrace_1912981
  have hstable : (prefixWord ++ tailWord_1912981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1912981).length < 2 ^ (prefixWord ++ tailWord_1912981).sum := by decide
  have hdescent : baseEnd_1912981 < baseStart_1912981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1912981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913015 : List Nat := [1, 1, 3, 1, 4, 4, 1, 3, 1, 3]
def baseStart_1913015 : Nat := 118140960795 + 1913015 * 2 ^ 59
def prefixEnd_1913015 : Nat := 4983230072969 + 3 ^ 40 * 1913015 * 2
def baseEnd_1913015 : Nat := 654864129507292035809807

theorem tailTrace_1913015 : CollatzResearch.WordTrace tailWord_1913015 prefixEnd_1913015 654864129507292035809807 := by
  unfold tailWord_1913015
  simp only [CollatzResearch.WordTrace]
  refine ⟨69773389164480846795844499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46515592776320564530562999 69773389164480846795844499)
  ·
    refine ⟨104660083746721270193766749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69773389164480846795844499 104660083746721270193766749)
    ·
      refine ⟨39247531405020476322662531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104660083746721270193766749 39247531405020476322662531)
      ·
        refine ⟨58871297107530714483993797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39247531405020476322662531 58871297107530714483993797)
        ·
          refine ⟨11038368207662008965748837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58871297107530714483993797 11038368207662008965748837)
          ·
            refine ⟨2069694038936626681077907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11038368207662008965748837 2069694038936626681077907)
            ·
              refine ⟨3104541058404940021616861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2069694038936626681077907 3104541058404940021616861)
              ·
                refine ⟨1164202896901852508106323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3104541058404940021616861 1164202896901852508106323)
                ·
                  refine ⟨1746304345352778762159485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1164202896901852508106323 1746304345352778762159485)
                  ·
                    refine ⟨654864129507292035809807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1746304345352778762159485 654864129507292035809807)
                    ·
                      rfl

theorem cell22_1913015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 3, 1, 3].length) (baseStart_1913015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1913015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1913015 prefixEnd_1913015 := by exact prefixLift 1913015
  have htrace : WordTrace (prefixWord ++ tailWord_1913015) baseStart_1913015 baseEnd_1913015 := by
    simpa [prefixWord, tailWord_1913015, baseEnd_1913015] using wordTrace_append hprefix tailTrace_1913015
  have hstable : (prefixWord ++ tailWord_1913015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913015).length < 2 ^ (prefixWord ++ tailWord_1913015).sum := by decide
  have hdescent : baseEnd_1913015 < baseStart_1913015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913045 : List Nat := [1, 3, 2, 4, 2, 2, 2, 1, 5]
def baseStart_1913045 : Nat := 118140960795 + 1913045 * 2 ^ 59
def prefixEnd_1913045 : Nat := 4983230072969 + 3 ^ 40 * 1913045 * 2
def baseEnd_1913045 : Nat := 218291466373460652519905

theorem tailTrace_1913045 : CollatzResearch.WordTrace tailWord_1913045 prefixEnd_1913045 218291466373460652519905 := by
  unfold tailWord_1913045
  simp only [CollatzResearch.WordTrace]
  refine ⟨69774483354372161919436589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46516322236248107946291059 69774483354372161919436589)
  ·
    refine ⟨26165431257889560719788721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69774483354372161919436589 26165431257889560719788721)
    ·
      refine ⟨19624073443417170539841541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26165431257889560719788721 19624073443417170539841541)
      ·
        refine ⟨3679513770640719476220289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19624073443417170539841541 3679513770640719476220289)
        ·
          refine ⟨2759635327980539607165217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3679513770640719476220289 2759635327980539607165217)
          ·
            refine ⟨2069726495985404705373913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2759635327980539607165217 2069726495985404705373913)
            ·
              refine ⟨1552294871989053529030435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2069726495985404705373913 1552294871989053529030435)
              ·
                refine ⟨2328442307983580293545653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1552294871989053529030435 2328442307983580293545653)
                ·
                  refine ⟨218291466373460652519905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2328442307983580293545653 218291466373460652519905)
                  ·
                    rfl

theorem cell22_1913045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 2, 1, 5].length) (baseStart_1913045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1913045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1913045 prefixEnd_1913045 := by exact prefixLift 1913045
  have htrace : WordTrace (prefixWord ++ tailWord_1913045) baseStart_1913045 baseEnd_1913045 := by
    simpa [prefixWord, tailWord_1913045, baseEnd_1913045] using wordTrace_append hprefix tailTrace_1913045
  have hstable : (prefixWord ++ tailWord_1913045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913045).length < 2 ^ (prefixWord ++ tailWord_1913045).sum := by decide
  have hdescent : baseEnd_1913045 < baseStart_1913045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913071 : List Nat := [1, 1, 2, 1, 6, 2, 1, 2, 1, 5]
def baseStart_1913071 : Nat := 118140960795 + 1913071 * 2 ^ 59
def prefixEnd_1913071 : Nat := 4983230072969 + 3 ^ 40 * 1913071 * 2
def baseEnd_1913071 : Nat := 654883299451726556409635

theorem tailTrace_1913071 : CollatzResearch.WordTrace tailWord_1913071 prefixEnd_1913071 654883299451726556409635 := by
  unfold tailWord_1913071
  simp only [CollatzResearch.WordTrace]
  refine ⟨69775431652277968359883067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46516954434851978906588711 69775431652277968359883067)
  ·
    refine ⟨104663147478416952539824601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69775431652277968359883067 104663147478416952539824601)
    ·
      refine ⟨78497360608812714404868451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104663147478416952539824601 78497360608812714404868451)
      ·
        refine ⟨117746040913219071607302677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78497360608812714404868451 117746040913219071607302677)
        ·
          refine ⟨5519345667807143981592313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 117746040913219071607302677 5519345667807143981592313)
          ·
            refine ⟨4139509250855357986194235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5519345667807143981592313 4139509250855357986194235)
            ·
              refine ⟨6209263876283036979291353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4139509250855357986194235 6209263876283036979291353)
              ·
                refine ⟨4656947907212277734468515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6209263876283036979291353 4656947907212277734468515)
                ·
                  refine ⟨6985421860818416601702773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4656947907212277734468515 6985421860818416601702773)
                  ·
                    refine ⟨654883299451726556409635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6985421860818416601702773 654883299451726556409635)
                    ·
                      rfl

theorem cell22_1913071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 2, 1, 5].length) (baseStart_1913071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1913071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1913071 prefixEnd_1913071 := by exact prefixLift 1913071
  have htrace : WordTrace (prefixWord ++ tailWord_1913071) baseStart_1913071 baseEnd_1913071 := by
    simpa [prefixWord, tailWord_1913071, baseEnd_1913071] using wordTrace_append hprefix tailTrace_1913071
  have hstable : (prefixWord ++ tailWord_1913071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913071).length < 2 ^ (prefixWord ++ tailWord_1913071).sum := by decide
  have hdescent : baseEnd_1913071 < baseStart_1913071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913084 : List Nat := [2, 2, 2, 1, 4, 11]
def baseStart_1913084 : Nat := 118140960795 + 1913084 * 2 ^ 59
def prefixEnd_1913084 : Nat := 4983230072969 + 3 ^ 40 * 1913084 * 2
def baseEnd_1913084 : Nat := 8085033945893813034995

theorem tailTrace_1913084 : CollatzResearch.WordTrace tailWord_1913084 prefixEnd_1913084 8085033945893813034995 := by
  unfold tailWord_1913084
  simp only [CollatzResearch.WordTrace]
  refine ⟨34887952900615435790053153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46517270534153914386737537 34887952900615435790053153)
  ·
    refine ⟨26165964675461576842539865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34887952900615435790053153 26165964675461576842539865)
    ·
      refine ⟨19624473506596182631904899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26165964675461576842539865 19624473506596182631904899)
      ·
        refine ⟨29436710259894273947857349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19624473506596182631904899 29436710259894273947857349)
        ·
          refine ⟨5519383173730176365223253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29436710259894273947857349 5519383173730176365223253)
          ·
            refine ⟨8085033945893813034995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 5519383173730176365223253 8085033945893813034995)
            ·
              rfl

theorem cell22_1913084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 11].length) (baseStart_1913084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1913084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1913084 prefixEnd_1913084 := by exact prefixLift 1913084
  have htrace : WordTrace (prefixWord ++ tailWord_1913084) baseStart_1913084 baseEnd_1913084 := by
    simpa [prefixWord, tailWord_1913084, baseEnd_1913084] using wordTrace_append hprefix tailTrace_1913084
  have hstable : (prefixWord ++ tailWord_1913084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913084).length < 2 ^ (prefixWord ++ tailWord_1913084).sum := by decide
  have hdescent : baseEnd_1913084 < baseStart_1913084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913090 : List Nat := [3, 4, 1, 1, 2, 2, 1, 4, 4]
def baseStart_1913090 : Nat := 118140960795 + 1913090 * 2 ^ 59
def prefixEnd_1913090 : Nat := 4983230072969 + 3 ^ 40 * 1913090 * 2
def baseEnd_1913090 : Nat := 218296601180005613394859

theorem tailTrace_1913090 : CollatzResearch.WordTrace tailWord_1913090 prefixEnd_1913090 218296601180005613394859 := by
  unfold tailWord_1913090
  simp only [CollatzResearch.WordTrace]
  refine ⟨17444031159802283651206181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46517416426139423069883149 17444031159802283651206181)
  ·
    refine ⟨3270755842462928184601159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17444031159802283651206181 3270755842462928184601159)
    ·
      refine ⟨4906133763694392276901739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3270755842462928184601159 4906133763694392276901739)
      ·
        refine ⟨7359200645541588415352609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4906133763694392276901739 7359200645541588415352609)
        ·
          refine ⟨5519400484156191311514457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7359200645541588415352609 5519400484156191311514457)
          ·
            refine ⟨4139550363117143483635843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5519400484156191311514457 4139550363117143483635843)
            ·
              refine ⟨6209325544675715225453765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4139550363117143483635843 6209325544675715225453765)
              ·
                refine ⟨1164248539626696604772581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6209325544675715225453765 1164248539626696604772581)
                ·
                  refine ⟨218296601180005613394859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1164248539626696604772581 218296601180005613394859)
                  ·
                    rfl

theorem cell22_1913090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_1913090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1913090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1913090 prefixEnd_1913090 := by exact prefixLift 1913090
  have htrace : WordTrace (prefixWord ++ tailWord_1913090) baseStart_1913090 baseEnd_1913090 := by
    simpa [prefixWord, tailWord_1913090, baseEnd_1913090] using wordTrace_append hprefix tailTrace_1913090
  have hstable : (prefixWord ++ tailWord_1913090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913090).length < 2 ^ (prefixWord ++ tailWord_1913090).sum := by decide
  have hdescent : baseEnd_1913090 < baseStart_1913090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913146 : List Nat := [3, 1, 1, 1, 4, 3, 1, 1, 7]
def baseStart_1913146 : Nat := 118140960795 + 1913146 * 2 ^ 59
def prefixEnd_1913146 : Nat := 4983230072969 + 3 ^ 40 * 1913146 * 2
def baseEnd_1913146 : Nat := 218302991161483786928135

theorem tailTrace_1913146 : CollatzResearch.WordTrace tailWord_1913146 prefixEnd_1913146 218302991161483786928135 := by
  unfold tailWord_1913146
  simp only [CollatzResearch.WordTrace]
  refine ⟨17444541781751564042215823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46518778084670837445908861 17444541781751564042215823)
  ·
    refine ⟨26166812672627346063323735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17444541781751564042215823 26166812672627346063323735)
    ·
      refine ⟨39250219008941019094985603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26166812672627346063323735 39250219008941019094985603)
      ·
        refine ⟨58875328513411528642478405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39250219008941019094985603 58875328513411528642478405)
        ·
          refine ⟨11039124096264661620464701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58875328513411528642478405 11039124096264661620464701)
          ·
            refine ⟨4139671536099248107674263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11039124096264661620464701 4139671536099248107674263)
            ·
              refine ⟨6209507304148872161511395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4139671536099248107674263 6209507304148872161511395)
              ·
                refine ⟨9314260956223308242267093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6209507304148872161511395 9314260956223308242267093)
                ·
                  refine ⟨218302991161483786928135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9314260956223308242267093 218302991161483786928135)
                  ·
                    rfl

theorem cell22_1913146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 1, 7].length) (baseStart_1913146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1913146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1913146 prefixEnd_1913146 := by exact prefixLift 1913146
  have htrace : WordTrace (prefixWord ++ tailWord_1913146) baseStart_1913146 baseEnd_1913146 := by
    simpa [prefixWord, tailWord_1913146, baseEnd_1913146] using wordTrace_append hprefix tailTrace_1913146
  have hstable : (prefixWord ++ tailWord_1913146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913146).length < 2 ^ (prefixWord ++ tailWord_1913146).sum := by decide
  have hdescent : baseEnd_1913146 < baseStart_1913146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913150 : List Nat := [4, 2, 1, 2, 1, 3, 2, 1, 3, 3]
def baseStart_1913150 : Nat := 118140960795 + 1913150 * 2 ^ 59
def prefixEnd_1913150 : Nat := 4983230072969 + 3 ^ 40 * 1913150 * 2
def baseEnd_1913150 : Nat := 654910342766196683684393

theorem tailTrace_1913150 : CollatzResearch.WordTrace tailWord_1913150 prefixEnd_1913150 654910342766196683684393 := by
  unfold tailWord_1913150
  simp only [CollatzResearch.WordTrace]
  refine ⟨8722289127373970606501113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46518875345994509901339269 8722289127373970606501113)
  ·
    refine ⟨6541716845530477954875835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8722289127373970606501113 6541716845530477954875835)
    ·
      refine ⟨9812575268295716932313753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6541716845530477954875835 9812575268295716932313753)
      ·
        refine ⟨7359431451221787699235315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9812575268295716932313753 7359431451221787699235315)
        ·
          refine ⟨11039147176832681548852973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7359431451221787699235315 11039147176832681548852973)
          ·
            refine ⟨4139680191312255580819865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11039147176832681548852973 4139680191312255580819865)
            ·
              refine ⟨3104760143484191685614899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4139680191312255580819865 3104760143484191685614899)
              ·
                refine ⟨4657140215226287528422349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3104760143484191685614899 4657140215226287528422349)
                ·
                  refine ⟨1746427580709857823158381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4657140215226287528422349 1746427580709857823158381)
                  ·
                    refine ⟨654910342766196683684393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1746427580709857823158381 654910342766196683684393)
                    ·
                      rfl

theorem cell22_1913150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 1, 3, 3].length) (baseStart_1913150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1913150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1913150 prefixEnd_1913150 := by exact prefixLift 1913150
  have htrace : WordTrace (prefixWord ++ tailWord_1913150) baseStart_1913150 baseEnd_1913150 := by
    simpa [prefixWord, tailWord_1913150, baseEnd_1913150] using wordTrace_append hprefix tailTrace_1913150
  have hstable : (prefixWord ++ tailWord_1913150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913150).length < 2 ^ (prefixWord ++ tailWord_1913150).sum := by decide
  have hdescent : baseEnd_1913150 < baseStart_1913150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913184 : List Nat := [2, 1, 1, 3, 6, 1, 1, 3, 1, 3]
def baseStart_1913184 : Nat := 118140960795 + 1913184 * 2 ^ 59
def prefixEnd_1913184 : Nat := 4983230072969 + 3 ^ 40 * 1913184 * 2
def baseEnd_1913184 : Nat := 654921981661031928334289

theorem tailTrace_1913184 : CollatzResearch.WordTrace tailWord_1913184 prefixEnd_1913184 654921981661031928334289 := by
  unfold tailWord_1913184
  simp only [CollatzResearch.WordTrace]
  refine ⟨34889776550434294329373303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46519702067245725772497737 34889776550434294329373303)
  ·
    refine ⟨52334664825651441494059955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34889776550434294329373303 52334664825651441494059955)
    ·
      refine ⟨78501997238477162241089933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52334664825651441494059955 78501997238477162241089933)
      ·
        refine ⟨29438248964428935840408725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78501997238477162241089933 29438248964428935840408725)
        ·
          refine ⟨1379917920207606367519159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 29438248964428935840408725 1379917920207606367519159)
          ·
            refine ⟨2069876880311409551278739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1379917920207606367519159 2069876880311409551278739)
            ·
              refine ⟨3104815320467114326918109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2069876880311409551278739 3104815320467114326918109)
              ·
                refine ⟨1164305745175167872594291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3104815320467114326918109 1164305745175167872594291)
                ·
                  refine ⟨1746458617762751808891437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1164305745175167872594291 1746458617762751808891437)
                  ·
                    refine ⟨654921981661031928334289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1746458617762751808891437 654921981661031928334289)
                    ·
                      rfl

theorem cell22_1913184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 3, 1, 3].length) (baseStart_1913184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1913184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1913184 prefixEnd_1913184 := by exact prefixLift 1913184
  have htrace : WordTrace (prefixWord ++ tailWord_1913184) baseStart_1913184 baseEnd_1913184 := by
    simpa [prefixWord, tailWord_1913184, baseEnd_1913184] using wordTrace_append hprefix tailTrace_1913184
  have hstable : (prefixWord ++ tailWord_1913184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913184).length < 2 ^ (prefixWord ++ tailWord_1913184).sum := by decide
  have hdescent : baseEnd_1913184 < baseStart_1913184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913221 : List Nat := [1, 3, 1, 1, 3, 1, 1, 1, 6, 4]
def baseStart_1913221 : Nat := 118140960795 + 1913221 * 2 ^ 59
def prefixEnd_1913221 : Nat := 4983230072969 + 3 ^ 40 * 1913221 * 2
def baseEnd_1913221 : Nat := 654934647517176165159175

theorem tailTrace_1913221 : CollatzResearch.WordTrace tailWord_1913221 prefixEnd_1913221 654934647517176165159175 := by
  unfold tailWord_1913221
  simp only [CollatzResearch.WordTrace]
  refine ⟨69780902601734543977843517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46520601734489695985229011 69780902601734543977843517)
  ·
    refine ⟨26167838475650453991691319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69780902601734543977843517 26167838475650453991691319)
    ·
      refine ⟨39251757713475680987536979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26167838475650453991691319 39251757713475680987536979)
      ·
        refine ⟨58877636570213521481305469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39251757713475680987536979 58877636570213521481305469)
        ·
          refine ⟨22079113713830070555489551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58877636570213521481305469 22079113713830070555489551)
          ·
            refine ⟨33118670570745105833234327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22079113713830070555489551 33118670570745105833234327)
            ·
              refine ⟨49678005856117658749851491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33118670570745105833234327 49678005856117658749851491)
              ·
                refine ⟨74517008784176488124777237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49678005856117658749851491 74517008784176488124777237)
                ·
                  refine ⟨3492984786758272880848933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 74517008784176488124777237 3492984786758272880848933)
                  ·
                    refine ⟨654934647517176165159175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3492984786758272880848933 654934647517176165159175)
                    ·
                      rfl

theorem cell22_1913221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 6, 4].length) (baseStart_1913221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1913221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1913221 prefixEnd_1913221 := by exact prefixLift 1913221
  have htrace : WordTrace (prefixWord ++ tailWord_1913221) baseStart_1913221 baseEnd_1913221 := by
    simpa [prefixWord, tailWord_1913221, baseEnd_1913221] using wordTrace_append hprefix tailTrace_1913221
  have hstable : (prefixWord ++ tailWord_1913221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913221).length < 2 ^ (prefixWord ++ tailWord_1913221).sum := by decide
  have hdescent : baseEnd_1913221 < baseStart_1913221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913266 : List Nat := [3, 2, 1, 1, 1, 1, 3, 1, 1, 8]
def baseStart_1913266 : Nat := 118140960795 + 1913266 * 2 ^ 59
def prefixEnd_1913266 : Nat := 4983230072969 + 3 ^ 40 * 1913266 * 2
def baseEnd_1913266 : Nat := 654950051936811047784037

theorem tailTrace_1913266 : CollatzResearch.WordTrace tailWord_1913266 prefixEnd_1913266 654950051936811047784037 := by
  unfold tailWord_1913266
  simp only [CollatzResearch.WordTrace]
  refine ⟨17445635971642879165807913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46521695924381011108821101 17445635971642879165807913)
  ·
    refine ⟨13084226978732159374355935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17445635971642879165807913 13084226978732159374355935)
    ·
      refine ⟨19626340468098239061533903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13084226978732159374355935 19626340468098239061533903)
      ·
        refine ⟨29439510702147358592300855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19626340468098239061533903 29439510702147358592300855)
        ·
          refine ⟨44159266053221037888451283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29439510702147358592300855 44159266053221037888451283)
          ·
            refine ⟨66238899079831556832676925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44159266053221037888451283 66238899079831556832676925)
            ·
              refine ⟨24839587154936833812253847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66238899079831556832676925 24839587154936833812253847)
              ·
                refine ⟨37259380732405250718380771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24839587154936833812253847 37259380732405250718380771)
                ·
                  refine ⟨55889071098607876077571157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37259380732405250718380771 55889071098607876077571157)
                  ·
                    refine ⟨654950051936811047784037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 55889071098607876077571157 654950051936811047784037)
                    ·
                      rfl

theorem cell22_1913266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 1, 8].length) (baseStart_1913266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1913266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1913266 prefixEnd_1913266 := by exact prefixLift 1913266
  have htrace : WordTrace (prefixWord ++ tailWord_1913266) baseStart_1913266 baseEnd_1913266 := by
    simpa [prefixWord, tailWord_1913266, baseEnd_1913266] using wordTrace_append hprefix tailTrace_1913266
  have hstable : (prefixWord ++ tailWord_1913266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913266).length < 2 ^ (prefixWord ++ tailWord_1913266).sum := by decide
  have hdescent : baseEnd_1913266 < baseStart_1913266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913296 : List Nat := [2, 1, 1, 1, 1, 2, 2, 1, 6, 5]
def baseStart_1913296 : Nat := 118140960795 + 1913296 * 2 ^ 59
def prefixEnd_1913296 : Nat := 4983230072969 + 3 ^ 40 * 1913296 * 2
def baseEnd_1913296 : Nat := 654960321549900969533945

theorem tailTrace_1913296 : CollatzResearch.WordTrace tailWord_1913296 prefixEnd_1913296 654960321549900969533945 := by
  unfold tailWord_1913296
  simp only [CollatzResearch.WordTrace]
  refine ⟨34891819038231415893411871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46522425384308554524549161 34891819038231415893411871)
  ·
    refine ⟨52337728557347123840117807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34891819038231415893411871 52337728557347123840117807)
    ·
      refine ⟨78506592836020685760176711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52337728557347123840117807 78506592836020685760176711)
      ·
        refine ⟨117759889254031028640265067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78506592836020685760176711 117759889254031028640265067)
        ·
          refine ⟨176639833881046542960397601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117759889254031028640265067 176639833881046542960397601)
          ·
            refine ⟨132479875410784907220298201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176639833881046542960397601 132479875410784907220298201)
            ·
              refine ⟨99359906558088680415223651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132479875410784907220298201 99359906558088680415223651)
              ·
                refine ⟨149039859837133020622835477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99359906558088680415223651 149039859837133020622835477)
                ·
                  refine ⟨6986243429865610341695413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 149039859837133020622835477 6986243429865610341695413)
                  ·
                    refine ⟨654960321549900969533945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6986243429865610341695413 654960321549900969533945)
                    ·
                      rfl

theorem cell22_1913296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 6, 5].length) (baseStart_1913296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1913296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1913296 prefixEnd_1913296 := by exact prefixLift 1913296
  have htrace : WordTrace (prefixWord ++ tailWord_1913296) baseStart_1913296 baseEnd_1913296 := by
    simpa [prefixWord, tailWord_1913296, baseEnd_1913296] using wordTrace_append hprefix tailTrace_1913296
  have hstable : (prefixWord ++ tailWord_1913296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913296).length < 2 ^ (prefixWord ++ tailWord_1913296).sum := by decide
  have hdescent : baseEnd_1913296 < baseStart_1913296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913345 : List Nat := [1, 2, 4, 1, 3, 1, 1, 4, 1, 4]
def baseStart_1913345 : Nat := 118140960795 + 1913345 * 2 ^ 59
def prefixEnd_1913345 : Nat := 4983230072969 + 3 ^ 40 * 1913345 * 2
def baseEnd_1913345 : Nat := 654977095251281175058795

theorem tailTrace_1913345 : CollatzResearch.WordTrace tailWord_1913345 prefixEnd_1913345 654977095251281175058795 := by
  unfold tailWord_1913345
  simp only [CollatzResearch.WordTrace]
  refine ⟨69785425253285313155357489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46523616835523542103571659 69785425253285313155357489)
  ·
    refine ⟨52339068939963984866518117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69785425253285313155357489 52339068939963984866518117)
    ·
      refine ⟨9813575426243247162472147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52339068939963984866518117 9813575426243247162472147)
      ·
        refine ⟨14720363139364870743708221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9813575426243247162472147 14720363139364870743708221)
        ·
          refine ⟨5520136177261826528890583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14720363139364870743708221 5520136177261826528890583)
          ·
            refine ⟨8280204265892739793335875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5520136177261826528890583 8280204265892739793335875)
            ·
              refine ⟨12420306398839109690003813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8280204265892739793335875 12420306398839109690003813)
              ·
                refine ⟨2328807449782333066875715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12420306398839109690003813 2328807449782333066875715)
                ·
                  refine ⟨3493211174673499600313573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2328807449782333066875715 3493211174673499600313573)
                  ·
                    refine ⟨654977095251281175058795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3493211174673499600313573 654977095251281175058795)
                    ·
                      rfl

theorem cell22_1913345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_1913345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1913345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1913345 prefixEnd_1913345 := by exact prefixLift 1913345
  have htrace : WordTrace (prefixWord ++ tailWord_1913345) baseStart_1913345 baseEnd_1913345 := by
    simpa [prefixWord, tailWord_1913345, baseEnd_1913345] using wordTrace_append hprefix tailTrace_1913345
  have hstable : (prefixWord ++ tailWord_1913345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913345).length < 2 ^ (prefixWord ++ tailWord_1913345).sum := by decide
  have hdescent : baseEnd_1913345 < baseStart_1913345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913375 : List Nat := [1, 1, 2, 4, 1, 1, 1, 6, 2, 3]
def baseStart_1913375 : Nat := 118140960795 + 1913375 * 2 ^ 59
def prefixEnd_1913375 : Nat := 4983230072969 + 3 ^ 40 * 1913375 * 2
def baseEnd_1913375 : Nat := 654987364864371096808703

theorem tailTrace_1913375 : CollatzResearch.WordTrace tailWord_1913375 prefixEnd_1913375 654987364864371096808703 := by
  unfold tailWord_1913375
  simp only [CollatzResearch.WordTrace]
  refine ⟨69786519443176628278949579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46524346295451085519299719 69786519443176628278949579)
  ·
    refine ⟨104679779164764942418424369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69786519443176628278949579 104679779164764942418424369)
    ·
      refine ⟨78509834373573706813818277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104679779164764942418424369 78509834373573706813818277)
      ·
        refine ⟨14720593945045070027590927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78509834373573706813818277 14720593945045070027590927)
        ·
          refine ⟨22080890917567605041386391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14720593945045070027590927 22080890917567605041386391)
          ·
            refine ⟨33121336376351407562079587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22080890917567605041386391 33121336376351407562079587)
            ·
              refine ⟨49682004564527111343119381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33121336376351407562079587 49682004564527111343119381)
              ·
                refine ⟨2328843963962208344208721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 49682004564527111343119381 2328843963962208344208721)
                ·
                  refine ⟨1746632972971656258156541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2328843963962208344208721 1746632972971656258156541)
                  ·
                    refine ⟨654987364864371096808703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1746632972971656258156541 654987364864371096808703)
                    ·
                      rfl

theorem cell22_1913375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 6, 2, 3].length) (baseStart_1913375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1913375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1913375 prefixEnd_1913375 := by exact prefixLift 1913375
  have htrace : WordTrace (prefixWord ++ tailWord_1913375) baseStart_1913375 baseEnd_1913375 := by
    simpa [prefixWord, tailWord_1913375, baseEnd_1913375] using wordTrace_append hprefix tailTrace_1913375
  have hstable : (prefixWord ++ tailWord_1913375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913375).length < 2 ^ (prefixWord ++ tailWord_1913375).sum := by decide
  have hdescent : baseEnd_1913375 < baseStart_1913375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913377 : List Nat := [1, 2, 3, 2, 2, 1, 5, 2, 4]
def baseStart_1913377 : Nat := 118140960795 + 1913377 * 2 ^ 59
def prefixEnd_1913377 : Nat := 4983230072969 + 3 ^ 40 * 1913377 * 2
def baseEnd_1913377 : Nat := 218329349835081252752899

theorem tailTrace_1913377 : CollatzResearch.WordTrace tailWord_1913377 prefixEnd_1913377 218329349835081252752899 := by
  unfold tailWord_1913377
  simp only [CollatzResearch.WordTrace]
  refine ⟨69786592389169382620522385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46524394926112921747014923 69786592389169382620522385)
  ·
    refine ⟨52339944291877036965391789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69786592389169382620522385 52339944291877036965391789)
    ·
      refine ⟨19627479109453888862021921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52339944291877036965391789 19627479109453888862021921)
      ·
        refine ⟨14720609332090416646516441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19627479109453888862021921 14720609332090416646516441)
        ·
          refine ⟨11040456999067812484887331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14720609332090416646516441 11040456999067812484887331)
          ·
            refine ⟨16560685498601718727330997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11040456999067812484887331 16560685498601718727330997)
            ·
              refine ⟨1552564265493911130687281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16560685498601718727330997 1552564265493911130687281)
              ·
                refine ⟨1164423199120433348015461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1552564265493911130687281 1164423199120433348015461)
                ·
                  refine ⟨218329349835081252752899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1164423199120433348015461 218329349835081252752899)
                  ·
                    rfl

theorem cell22_1913377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 5, 2, 4].length) (baseStart_1913377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1913377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1913377 prefixEnd_1913377 := by exact prefixLift 1913377
  have htrace : WordTrace (prefixWord ++ tailWord_1913377) baseStart_1913377 baseEnd_1913377 := by
    simpa [prefixWord, tailWord_1913377, baseEnd_1913377] using wordTrace_append hprefix tailTrace_1913377
  have hstable : (prefixWord ++ tailWord_1913377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913377).length < 2 ^ (prefixWord ++ tailWord_1913377).sum := by decide
  have hdescent : baseEnd_1913377 < baseStart_1913377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913392 : List Nat := [2, 1, 1, 1, 2, 3, 6, 1, 2, 3]
def baseStart_1913392 : Nat := 118140960795 + 1913392 * 2 ^ 59
def prefixEnd_1913392 : Nat := 4983230072969 + 3 ^ 40 * 1913392 * 2
def baseEnd_1913392 : Nat := 654993184311788719133651

theorem tailTrace_1913392 : CollatzResearch.WordTrace tailWord_1913392 prefixEnd_1913392 654993184311788719133651 := by
  unfold tailWord_1913392
  simp only [CollatzResearch.WordTrace]
  refine ⟨34893569742057520091159215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46524759656076693454878953 34893569742057520091159215)
  ·
    refine ⟨52340354613086280136738823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34893569742057520091159215 52340354613086280136738823)
    ·
      refine ⟨78510531919629420205108235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52340354613086280136738823 78510531919629420205108235)
      ·
        refine ⟨117765797879444130307662353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78510531919629420205108235 117765797879444130307662353)
        ·
          refine ⟨88324348409583097730746765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117765797879444130307662353 88324348409583097730746765)
          ·
            refine ⟨33121630653593661649030037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88324348409583097730746765 33121630653593661649030037)
            ·
              refine ⟨1552576436887202889798283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 33121630653593661649030037 1552576436887202889798283)
              ·
                refine ⟨2328864655330804334697425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1552576436887202889798283 2328864655330804334697425)
                ·
                  refine ⟨1746648491498103251023069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2328864655330804334697425 1746648491498103251023069)
                  ·
                    refine ⟨654993184311788719133651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1746648491498103251023069 654993184311788719133651)
                    ·
                      rfl

theorem cell22_1913392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 6, 1, 2, 3].length) (baseStart_1913392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1913392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1913392 prefixEnd_1913392 := by exact prefixLift 1913392
  have htrace : WordTrace (prefixWord ++ tailWord_1913392) baseStart_1913392 baseEnd_1913392 := by
    simpa [prefixWord, tailWord_1913392, baseEnd_1913392] using wordTrace_append hprefix tailTrace_1913392
  have hstable : (prefixWord ++ tailWord_1913392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913392).length < 2 ^ (prefixWord ++ tailWord_1913392).sum := by decide
  have hdescent : baseEnd_1913392 < baseStart_1913392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913396 : List Nat := [2, 5, 1, 3, 1, 2, 1, 2, 1, 4]
def baseStart_1913396 : Nat := 118140960795 + 1913396 * 2 ^ 59
def prefixEnd_1913396 : Nat := 4983230072969 + 3 ^ 40 * 1913396 * 2
def baseEnd_1913396 : Nat := 654994553593534042033639

theorem tailTrace_1913396 : CollatzResearch.WordTrace tailWord_1913396 prefixEnd_1913396 654994553593534042033639 := by
  unfold tailWord_1913396
  simp only [CollatzResearch.WordTrace]
  refine ⟨34893642688050274432732021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46524856917400365910309361 34893642688050274432732021)
  ·
    refine ⟨3271279002004713228068627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34893642688050274432732021 3271279002004713228068627)
    ·
      refine ⟨4906918503007069842102941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3271279002004713228068627 4906918503007069842102941)
      ·
        refine ⟨1840094438627651190788603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4906918503007069842102941 1840094438627651190788603)
        ·
          refine ⟨2760141657941476786182905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1840094438627651190788603 2760141657941476786182905)
          ·
            refine ⟨2070106243456107589637179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2760141657941476786182905 2070106243456107589637179)
            ·
              refine ⟨3105159365184161384455769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2070106243456107589637179 3105159365184161384455769)
              ·
                refine ⟨2328869523888121038341827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3105159365184161384455769 2328869523888121038341827)
                ·
                  refine ⟨3493304285832181557512741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2328869523888121038341827 3493304285832181557512741)
                  ·
                    refine ⟨654994553593534042033639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3493304285832181557512741 654994553593534042033639)
                    ·
                      rfl

theorem cell22_1913396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_1913396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1913396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1913396 prefixEnd_1913396 := by exact prefixLift 1913396
  have htrace : WordTrace (prefixWord ++ tailWord_1913396) baseStart_1913396 baseEnd_1913396 := by
    simpa [prefixWord, tailWord_1913396, baseEnd_1913396] using wordTrace_append hprefix tailTrace_1913396
  have hstable : (prefixWord ++ tailWord_1913396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913396).length < 2 ^ (prefixWord ++ tailWord_1913396).sum := by decide
  have hdescent : baseEnd_1913396 < baseStart_1913396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913450 : List Nat := [3, 1, 3, 2, 1, 1, 1, 5, 5]
def baseStart_1913450 : Nat := 118140960795 + 1913450 * 2 ^ 59
def prefixEnd_1913450 : Nat := 4983230072969 + 3 ^ 40 * 1913450 * 2
def baseEnd_1913450 : Nat := 218337679632365300394491

theorem tailTrace_1913450 : CollatzResearch.WordTrace tailWord_1913450 prefixEnd_1913450 218337679632365300394491 := by
  unfold tailWord_1913450
  simp only [CollatzResearch.WordTrace]
  refine ⟨17447313729476229021982451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46526169945269944058619869 17447313729476229021982451)
  ·
    refine ⟨26170970594214343532973677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17447313729476229021982451 26170970594214343532973677)
    ·
      refine ⟨9814113972830378824865129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26170970594214343532973677 9814113972830378824865129)
      ·
        refine ⟨7360585479622784118648847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9814113972830378824865129 7360585479622784118648847)
        ·
          refine ⟨11040878219434176177973271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7360585479622784118648847 11040878219434176177973271)
          ·
            refine ⟨16561317329151264266959907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11040878219434176177973271 16561317329151264266959907)
            ·
              refine ⟨24841975993726896400439861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16561317329151264266959907 24841975993726896400439861)
              ·
                refine ⟨2328935249411896537541237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24841975993726896400439861 2328935249411896537541237)
                ·
                  refine ⟨218337679632365300394491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2328935249411896537541237 218337679632365300394491)
                  ·
                    rfl

theorem cell22_1913450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 5, 5].length) (baseStart_1913450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1913450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1913450 prefixEnd_1913450 := by exact prefixLift 1913450
  have htrace : WordTrace (prefixWord ++ tailWord_1913450) baseStart_1913450 baseEnd_1913450 := by
    simpa [prefixWord, tailWord_1913450, baseEnd_1913450] using wordTrace_append hprefix tailTrace_1913450
  have hstable : (prefixWord ++ tailWord_1913450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913450).length < 2 ^ (prefixWord ++ tailWord_1913450).sum := by decide
  have hdescent : baseEnd_1913450 < baseStart_1913450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913493 : List Nat := [1, 3, 2, 1, 1, 1, 1, 1, 2, 9]
def baseStart_1913493 : Nat := 118140960795 + 1913493 * 2 ^ 59
def prefixEnd_1913493 : Nat := 4983230072969 + 3 ^ 40 * 1913493 * 2
def baseEnd_1913493 : Nat := 655027758675858122358341

theorem tailTrace_1913493 : CollatzResearch.WordTrace tailWord_1913493 prefixEnd_1913493 655027758675858122358341 := by
  unfold tailWord_1913493
  simp only [CollatzResearch.WordTrace]
  refine ⟨69790823256749134431745133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46527215504499422954496755 69790823256749134431745133)
  ·
    refine ⟨26171558721280925411904425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69790823256749134431745133 26171558721280925411904425)
    ·
      refine ⟨19628669040960694058928319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26171558721280925411904425 19628669040960694058928319)
      ·
        refine ⟨29443003561441041088392479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19628669040960694058928319 29443003561441041088392479)
        ·
          refine ⟨44164505342161561632588719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29443003561441041088392479 44164505342161561632588719)
          ·
            refine ⟨66246758013242342448883079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44164505342161561632588719 66246758013242342448883079)
            ·
              refine ⟨99370137019863513673324619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66246758013242342448883079 99370137019863513673324619)
              ·
                refine ⟨149055205529795270509986929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99370137019863513673324619 149055205529795270509986929)
                ·
                  refine ⟨111791404147346452882490197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 149055205529795270509986929 111791404147346452882490197)
                  ·
                    refine ⟨655027758675858122358341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 111791404147346452882490197 655027758675858122358341)
                    ·
                      rfl

theorem cell22_1913493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 9].length) (baseStart_1913493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1913493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1913493 prefixEnd_1913493 := by exact prefixLift 1913493
  have htrace : WordTrace (prefixWord ++ tailWord_1913493) baseStart_1913493 baseEnd_1913493 := by
    simpa [prefixWord, tailWord_1913493, baseEnd_1913493] using wordTrace_append hprefix tailTrace_1913493
  have hstable : (prefixWord ++ tailWord_1913493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913493).length < 2 ^ (prefixWord ++ tailWord_1913493).sum := by decide
  have hdescent : baseEnd_1913493 < baseStart_1913493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913495 : List Nat := [1, 1, 3, 3, 2, 1, 4, 1, 6]
def baseStart_1913495 : Nat := 118140960795 + 1913495 * 2 ^ 59
def prefixEnd_1913495 : Nat := 4983230072969 + 3 ^ 40 * 1913495 * 2
def baseEnd_1913495 : Nat := 218342814438910261269445

theorem tailTrace_1913495 : CollatzResearch.WordTrace tailWord_1913495 prefixEnd_1913495 218342814438910261269445 := by
  unfold tailWord_1913495
  simp only [CollatzResearch.WordTrace]
  refine ⟨69790896202741888773317939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46527264135161259182211959 69790896202741888773317939)
  ·
    refine ⟨104686344304112833159976909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69790896202741888773317939 104686344304112833159976909)
    ·
      refine ⟨39257379114042312434991341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104686344304112833159976909 39257379114042312434991341)
      ·
        refine ⟨14721517167765867163121753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39257379114042312434991341 14721517167765867163121753)
        ·
          refine ⟨11041137875824400372341315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14721517167765867163121753 11041137875824400372341315)
          ·
            refine ⟨16561706813736600558511973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11041137875824400372341315 16561706813736600558511973)
            ·
              refine ⟨3105320027575612604720995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16561706813736600558511973 3105320027575612604720995)
              ·
                refine ⟨4657980041363418907081493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3105320027575612604720995 4657980041363418907081493)
                ·
                  refine ⟨218342814438910261269445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4657980041363418907081493 218342814438910261269445)
                  ·
                    rfl

theorem cell22_1913495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 1, 6].length) (baseStart_1913495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1913495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1913495 prefixEnd_1913495 := by exact prefixLift 1913495
  have htrace : WordTrace (prefixWord ++ tailWord_1913495) baseStart_1913495 baseEnd_1913495 := by
    simpa [prefixWord, tailWord_1913495, baseEnd_1913495] using wordTrace_append hprefix tailTrace_1913495
  have hstable : (prefixWord ++ tailWord_1913495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913495).length < 2 ^ (prefixWord ++ tailWord_1913495).sum := by decide
  have hdescent : baseEnd_1913495 < baseStart_1913495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913540 : List Nat := [2, 3, 3, 1, 1, 2, 10]
def baseStart_1913540 : Nat := 118140960795 + 1913540 * 2 ^ 59
def prefixEnd_1913540 : Nat := 4983230072969 + 3 ^ 40 * 1913540 * 2
def baseEnd_1913540 : Nat := 24260883249495024682711

theorem tailTrace_1913540 : CollatzResearch.WordTrace tailWord_1913540 prefixEnd_1913540 24260883249495024682711 := by
  unfold tailWord_1913540
  simp only [CollatzResearch.WordTrace]
  refine ⟨34896268743789430729353037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46528358325052574305804049 34896268743789430729353037)
  ·
    refine ⟨13086100778921036523507389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34896268743789430729353037 13086100778921036523507389)
    ·
      refine ⟨4907287792095388696315271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13086100778921036523507389 4907287792095388696315271)
      ·
        refine ⟨7360931688143083044472907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4907287792095388696315271 7360931688143083044472907)
        ·
          refine ⟨11041397532214624566709361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7360931688143083044472907 11041397532214624566709361)
          ·
            refine ⟨8281048149160968425032021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11041397532214624566709361 8281048149160968425032021)
            ·
              refine ⟨24260883249495024682711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8281048149160968425032021 24260883249495024682711)
              ·
                rfl

theorem cell22_1913540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 10].length) (baseStart_1913540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1913540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1913540 prefixEnd_1913540 := by exact prefixLift 1913540
  have htrace : WordTrace (prefixWord ++ tailWord_1913540) baseStart_1913540 baseEnd_1913540 := by
    simpa [prefixWord, tailWord_1913540, baseEnd_1913540] using wordTrace_append hprefix tailTrace_1913540
  have hstable : (prefixWord ++ tailWord_1913540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913540).length < 2 ^ (prefixWord ++ tailWord_1913540).sum := by decide
  have hdescent : baseEnd_1913540 < baseStart_1913540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913615 : List Nat := [1, 1, 2, 1, 1, 1, 5, 1, 5, 4]
def baseStart_1913615 : Nat := 118140960795 + 1913615 * 2 ^ 59
def prefixEnd_1913615 : Nat := 4983230072969 + 3 ^ 40 * 1913615 * 2
def baseEnd_1913615 : Nat := 655069521769090470807967

theorem tailTrace_1913615 : CollatzResearch.WordTrace tailWord_1913615 prefixEnd_1913615 655069521769090470807967 := by
  unfold tailWord_1913615
  simp only [CollatzResearch.WordTrace]
  refine ⟨69795272962307149267686299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46530181974871432845124199 69795272962307149267686299)
  ·
    refine ⟨104692909443460723901529449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69795272962307149267686299 104692909443460723901529449)
    ·
      refine ⟨78519682082595542926147087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104692909443460723901529449 78519682082595542926147087)
      ·
        refine ⟨117779523123893314389220631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78519682082595542926147087 117779523123893314389220631)
        ·
          refine ⟨176669284685839971583830947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117779523123893314389220631 176669284685839971583830947)
          ·
            refine ⟨265003927028759957375746421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176669284685839971583830947 265003927028759957375746421)
            ·
              refine ⟨24844118158946246003976227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 265003927028759957375746421 24844118158946246003976227)
              ·
                refine ⟨37266177238419369005964341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24844118158946246003976227 37266177238419369005964341)
                ·
                  refine ⟨3493704116101815844309157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37266177238419369005964341 3493704116101815844309157)
                  ·
                    refine ⟨655069521769090470807967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3493704116101815844309157 655069521769090470807967)
                    ·
                      rfl

theorem cell22_1913615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 5, 4].length) (baseStart_1913615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1913615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1913615 prefixEnd_1913615 := by exact prefixLift 1913615
  have htrace : WordTrace (prefixWord ++ tailWord_1913615) baseStart_1913615 baseEnd_1913615 := by
    simpa [prefixWord, tailWord_1913615, baseEnd_1913615] using wordTrace_append hprefix tailTrace_1913615
  have hstable : (prefixWord ++ tailWord_1913615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913615).length < 2 ^ (prefixWord ++ tailWord_1913615).sum := by decide
  have hdescent : baseEnd_1913615 < baseStart_1913615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913632 : List Nat := [2, 1, 1, 5, 1, 2, 2, 1, 3, 4]
def baseStart_1913632 : Nat := 118140960795 + 1913632 * 2 ^ 59
def prefixEnd_1913632 : Nat := 4983230072969 + 3 ^ 40 * 1913632 * 2
def baseEnd_1913632 : Nat := 655075341216508093132915

theorem tailTrace_1913632 : CollatzResearch.WordTrace tailWord_1913632 prefixEnd_1913632 655075341216508093132915 := by
  unfold tailWord_1913632
  simp only [CollatzResearch.WordTrace]
  refine ⟨34897946501622780585527575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46530595335497040780703433 34897946501622780585527575)
  ·
    refine ⟨52346919752434170878291363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34897946501622780585527575 52346919752434170878291363)
    ·
      refine ⟨78520379628651256317437045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52346919752434170878291363 78520379628651256317437045)
      ·
        refine ⟨7361285590186055279759723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78520379628651256317437045 7361285590186055279759723)
        ·
          refine ⟨11041928385279082919639585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7361285590186055279759723 11041928385279082919639585)
          ·
            refine ⟨8281446288959312189729689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11041928385279082919639585 8281446288959312189729689)
            ·
              refine ⟨6211084716719484142297267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8281446288959312189729689 6211084716719484142297267)
              ·
                refine ⟨9316627075079226213445901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6211084716719484142297267 9316627075079226213445901)
                ·
                  refine ⟨3493735153154709830042213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9316627075079226213445901 3493735153154709830042213)
                  ·
                    refine ⟨655075341216508093132915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3493735153154709830042213 655075341216508093132915)
                    ·
                      rfl

theorem cell22_1913632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 1, 3, 4].length) (baseStart_1913632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1913632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1913632 prefixEnd_1913632 := by exact prefixLift 1913632
  have htrace : WordTrace (prefixWord ++ tailWord_1913632) baseStart_1913632 baseEnd_1913632 := by
    simpa [prefixWord, tailWord_1913632, baseEnd_1913632] using wordTrace_append hprefix tailTrace_1913632
  have hstable : (prefixWord ++ tailWord_1913632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913632).length < 2 ^ (prefixWord ++ tailWord_1913632).sum := by decide
  have hdescent : baseEnd_1913632 < baseStart_1913632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913698 : List Nat := [3, 3, 2, 1, 3, 2, 1, 3, 4]
def baseStart_1913698 : Nat := 118140960795 + 1913698 * 2 ^ 59
def prefixEnd_1913698 : Nat := 4983230072969 + 3 ^ 40 * 1913698 * 2
def baseEnd_1913698 : Nat := 218365978121768640327571

theorem tailTrace_1913698 : CollatzResearch.WordTrace tailWord_1913698 prefixEnd_1913698 218365978121768640327571 := by
  unfold tailWord_1913698
  simp only [CollatzResearch.WordTrace]
  refine ⟨17449575055251613610739437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46532200147337636295305165 17449575055251613610739437)
  ·
    refine ⟨6543590645719355104027289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17449575055251613610739437 6543590645719355104027289)
    ·
      refine ⟨4907692984289516328020467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6543590645719355104027289 4907692984289516328020467)
      ·
        refine ⟨7361539476434274492030701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4907692984289516328020467 7361539476434274492030701)
        ·
          refine ⟨2760577303662852934511513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7361539476434274492030701 2760577303662852934511513)
          ·
            refine ⟨2070432977747139700883635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2760577303662852934511513 2070432977747139700883635)
            ·
              refine ⟨3105649466620709551325453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2070432977747139700883635 3105649466620709551325453)
              ·
                refine ⟨1164618549982766081747045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3105649466620709551325453 1164618549982766081747045)
                ·
                  refine ⟨218365978121768640327571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1164618549982766081747045 218365978121768640327571)
                  ·
                    rfl

theorem cell22_1913698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 3, 4].length) (baseStart_1913698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1913698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1913698 prefixEnd_1913698 := by exact prefixLift 1913698
  have htrace : WordTrace (prefixWord ++ tailWord_1913698) baseStart_1913698 baseEnd_1913698 := by
    simpa [prefixWord, tailWord_1913698, baseEnd_1913698] using wordTrace_append hprefix tailTrace_1913698
  have hstable : (prefixWord ++ tailWord_1913698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913698).length < 2 ^ (prefixWord ++ tailWord_1913698).sum := by decide
  have hdescent : baseEnd_1913698 < baseStart_1913698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913705 : List Nat := [1, 2, 1, 1, 1, 3, 1, 1, 3, 8]
def baseStart_1913705 : Nat := 118140960795 + 1913705 * 2 ^ 59
def prefixEnd_1913705 : Nat := 4983230072969 + 3 ^ 40 * 1913705 * 2
def baseEnd_1913705 : Nat := 655100330608360236057691

theorem tailTrace_1913705 : CollatzResearch.WordTrace tailWord_1913705 prefixEnd_1913705 655100330608360236057691 := by
  unfold tailWord_1913705
  simp only [CollatzResearch.WordTrace]
  refine ⟨69798555531981094638462569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46532370354654063092308379 69798555531981094638462569)
  ·
    refine ⟨52348916648985820978846927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69798555531981094638462569 52348916648985820978846927)
    ·
      refine ⟨78523374973478731468270391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52348916648985820978846927 78523374973478731468270391)
      ·
        refine ⟨117785062460218097202405587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78523374973478731468270391 117785062460218097202405587)
        ·
          refine ⟨176677593690327145803608381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117785062460218097202405587 176677593690327145803608381)
          ·
            refine ⟨66254097633872679676353143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176677593690327145803608381 66254097633872679676353143)
            ·
              refine ⟨99381146450809019514529715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66254097633872679676353143 99381146450809019514529715)
              ·
                refine ⟨149071719676213529271794573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99381146450809019514529715 149071719676213529271794573)
                ·
                  refine ⟨55901894878580073476922965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 149071719676213529271794573 55901894878580073476922965)
                  ·
                    refine ⟨655100330608360236057691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 55901894878580073476922965 655100330608360236057691)
                    ·
                      rfl

theorem cell22_1913705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 8].length) (baseStart_1913705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1913705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1913705 prefixEnd_1913705 := by exact prefixLift 1913705
  have htrace : WordTrace (prefixWord ++ tailWord_1913705) baseStart_1913705 baseEnd_1913705 := by
    simpa [prefixWord, tailWord_1913705, baseEnd_1913705] using wordTrace_append hprefix tailTrace_1913705
  have hstable : (prefixWord ++ tailWord_1913705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913705).length < 2 ^ (prefixWord ++ tailWord_1913705).sum := by decide
  have hdescent : baseEnd_1913705 < baseStart_1913705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913707 : List Nat := [1, 1, 1, 1, 2, 2, 4, 2, 5, 3]
def baseStart_1913707 : Nat := 118140960795 + 1913707 * 2 ^ 59
def prefixEnd_1913707 : Nat := 4983230072969 + 3 ^ 40 * 1913707 * 2
def baseEnd_1913707 : Nat := 655101015249232897507685

theorem tailTrace_1913707 : CollatzResearch.WordTrace tailWord_1913707 prefixEnd_1913707 655101015249232897507685 := by
  unfold tailWord_1913707
  simp only [CollatzResearch.WordTrace]
  refine ⟨69798628477973848980035375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46532418985315899320023583 69798628477973848980035375)
  ·
    refine ⟨104697942716960773470053063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69798628477973848980035375 104697942716960773470053063)
    ·
      refine ⟨157046914075441160205079595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104697942716960773470053063 157046914075441160205079595)
      ·
        refine ⟨235570371113161740307619393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157046914075441160205079595 235570371113161740307619393)
        ·
          refine ⟨176677778334871305230714545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235570371113161740307619393 176677778334871305230714545)
          ·
            refine ⟨132508333751153478923035909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176677778334871305230714545 132508333751153478923035909)
            ·
              refine ⟨24845312578341277298069233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 132508333751153478923035909 24845312578341277298069233)
              ·
                refine ⟨18633984433755957973551925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24845312578341277298069233 18633984433755957973551925)
                ·
                  refine ⟨1746936040664621060020493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18633984433755957973551925 1746936040664621060020493)
                  ·
                    refine ⟨655101015249232897507685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1746936040664621060020493 655101015249232897507685)
                    ·
                      rfl

theorem cell22_1913707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 5, 3].length) (baseStart_1913707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1913707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1913707 prefixEnd_1913707 := by exact prefixLift 1913707
  have htrace : WordTrace (prefixWord ++ tailWord_1913707) baseStart_1913707 baseEnd_1913707 := by
    simpa [prefixWord, tailWord_1913707, baseEnd_1913707] using wordTrace_append hprefix tailTrace_1913707
  have hstable : (prefixWord ++ tailWord_1913707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913707).length < 2 ^ (prefixWord ++ tailWord_1913707).sum := by decide
  have hdescent : baseEnd_1913707 < baseStart_1913707 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913726 : List Nat := [4, 2, 3, 1, 2, 1, 2, 7]
def baseStart_1913726 : Nat := 118140960795 + 1913726 * 2 ^ 59
def prefixEnd_1913726 : Nat := 4983230072969 + 3 ^ 40 * 1913726 * 2
def baseEnd_1913726 : Nat := 72789724370835909031403

theorem tailTrace_1913726 : CollatzResearch.WordTrace tailWord_1913726 prefixEnd_1913726 72789724370835909031403 := by
  unfold tailWord_1913726
  simp only [CollatzResearch.WordTrace]
  refine ⟨8724915183113126903122129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46532880976603343483318021 8724915183113126903122129)
  ·
    refine ⟨6543686387334845177341597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8724915183113126903122129 6543686387334845177341597)
    ·
      refine ⟨2453882395250566941503099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6543686387334845177341597 2453882395250566941503099)
      ·
        refine ⟨3680823592875850412254649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2453882395250566941503099 3680823592875850412254649)
        ·
          refine ⟨2760617694656887809190987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3680823592875850412254649 2760617694656887809190987)
          ·
            refine ⟨4140926541985331713786481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2760617694656887809190987 4140926541985331713786481)
            ·
              refine ⟨3105694906488998785339861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4140926541985331713786481 3105694906488998785339861)
              ·
                refine ⟨72789724370835909031403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3105694906488998785339861 72789724370835909031403)
                ·
                  rfl

theorem cell22_1913726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 7].length) (baseStart_1913726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1913726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1913726 prefixEnd_1913726 := by exact prefixLift 1913726
  have htrace : WordTrace (prefixWord ++ tailWord_1913726) baseStart_1913726 baseEnd_1913726 := by
    simpa [prefixWord, tailWord_1913726, baseEnd_1913726] using wordTrace_append hprefix tailTrace_1913726
  have hstable : (prefixWord ++ tailWord_1913726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913726).length < 2 ^ (prefixWord ++ tailWord_1913726).sum := by decide
  have hdescent : baseEnd_1913726 < baseStart_1913726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913730 : List Nat := [3, 4, 2, 2, 1, 1, 1, 3, 2, 3]
def baseStart_1913730 : Nat := 118140960795 + 1913730 * 2 ^ 59
def prefixEnd_1913730 : Nat := 4983230072969 + 3 ^ 40 * 1913730 * 2
def baseEnd_1913730 : Nat := 655108888619268504182615

theorem tailTrace_1913730 : CollatzResearch.WordTrace tailWord_1913730 prefixEnd_1913730 655108888619268504182615 := by
  unfold tailWord_1913730
  simp only [CollatzResearch.WordTrace]
  refine ⟨17449866839222630977030661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46532978237927015938748429 17449866839222630977030661)
  ·
    refine ⟨3271850032354243308193249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17449866839222630977030661 3271850032354243308193249)
    ·
      refine ⟨2453887524265682481144937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3271850032354243308193249 2453887524265682481144937)
      ·
        refine ⟨1840415643199261860858703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2453887524265682481144937 1840415643199261860858703)
        ·
          refine ⟨2760623464798892791288055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1840415643199261860858703 2760623464798892791288055)
          ·
            refine ⟨4140935197198339186932083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2760623464798892791288055 4140935197198339186932083)
            ·
              refine ⟨6211402795797508780398125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4140935197198339186932083 6211402795797508780398125)
              ·
                refine ⟨2329276048424065792649297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6211402795797508780398125 2329276048424065792649297)
                ·
                  refine ⟨1746957036318049344486973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2329276048424065792649297 1746957036318049344486973)
                  ·
                    refine ⟨655108888619268504182615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1746957036318049344486973 655108888619268504182615)
                    ·
                      rfl

theorem cell22_1913730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_1913730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1913730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1913730 prefixEnd_1913730 := by exact prefixLift 1913730
  have htrace : WordTrace (prefixWord ++ tailWord_1913730) baseStart_1913730 baseEnd_1913730 := by
    simpa [prefixWord, tailWord_1913730, baseEnd_1913730] using wordTrace_append hprefix tailTrace_1913730
  have hstable : (prefixWord ++ tailWord_1913730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913730).length < 2 ^ (prefixWord ++ tailWord_1913730).sum := by decide
  have hdescent : baseEnd_1913730 < baseStart_1913730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913816 : List Nat := [2, 1, 2, 2, 2, 4, 2, 3, 4]
def baseStart_1913816 : Nat := 118140960795 + 1913816 * 2 ^ 59
def prefixEnd_1913816 : Nat := 4983230072969 + 3 ^ 40 * 1913816 * 2
def baseEnd_1913816 : Nat := 218379442725597648844117

theorem tailTrace_1913816 : CollatzResearch.WordTrace tailWord_1913816 prefixEnd_1913816 218379442725597648844117 := by
  unfold tailWord_1913816
  simp only [CollatzResearch.WordTrace]
  refine ⟨34901302017289480297876651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46535069356385973730502201 34901302017289480297876651)
  ·
    refine ⟨52351953025934220446814977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34901302017289480297876651 52351953025934220446814977)
    ·
      refine ⟨39263964769450665335111233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52351953025934220446814977 39263964769450665335111233)
      ·
        refine ⟨29447973577087999001333425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39263964769450665335111233 29447973577087999001333425)
        ·
          refine ⟨22085980182815999251000069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29447973577087999001333425 22085980182815999251000069)
          ·
            refine ⟨4141121284277999859562513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22085980182815999251000069 4141121284277999859562513)
            ·
              refine ⟨3105840963208499894671885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4141121284277999859562513 3105840963208499894671885)
              ·
                refine ⟨1164690361203187460501957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3105840963208499894671885 1164690361203187460501957)
                ·
                  refine ⟨218379442725597648844117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1164690361203187460501957 218379442725597648844117)
                  ·
                    rfl

theorem cell22_1913816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 3, 4].length) (baseStart_1913816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1913816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1913816 prefixEnd_1913816 := by exact prefixLift 1913816
  have htrace : WordTrace (prefixWord ++ tailWord_1913816) baseStart_1913816 baseEnd_1913816 := by
    simpa [prefixWord, tailWord_1913816, baseEnd_1913816] using wordTrace_append hprefix tailTrace_1913816
  have hstable : (prefixWord ++ tailWord_1913816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913816).length < 2 ^ (prefixWord ++ tailWord_1913816).sum := by decide
  have hdescent : baseEnd_1913816 < baseStart_1913816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913818 : List Nat := [3, 1, 1, 2, 4, 3, 2, 1, 1, 4]
def baseStart_1913818 : Nat := 118140960795 + 1913818 * 2 ^ 59
def prefixEnd_1913818 : Nat := 4983230072969 + 3 ^ 40 * 1913818 * 2
def baseEnd_1913818 : Nat := 655139012817665607982345

theorem tailTrace_1913818 : CollatzResearch.WordTrace tailWord_1913818 prefixEnd_1913818 655139012817665607982345 := by
  unfold tailWord_1913818
  simp only [CollatzResearch.WordTrace]
  refine ⟨17450669245142928734331527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46535117987047809958217405 17450669245142928734331527)
  ·
    refine ⟨26176003867714393101497291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17450669245142928734331527 26176003867714393101497291)
    ·
      refine ⟨39264005801571589652245937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26176003867714393101497291 39264005801571589652245937)
      ·
        refine ⟨29448004351178692239184453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39264005801571589652245937 29448004351178692239184453)
        ·
          refine ⟨5521500815846004794847085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29448004351178692239184453 5521500815846004794847085)
          ·
            refine ⟨2070562805942251798067657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5521500815846004794847085 2070562805942251798067657)
            ·
              refine ⟨1552922104456688848550743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2070562805942251798067657 1552922104456688848550743)
              ·
                refine ⟨2329383156685033272826115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1552922104456688848550743 2329383156685033272826115)
                ·
                  refine ⟨3494074735027549909239173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2329383156685033272826115 3494074735027549909239173)
                  ·
                    refine ⟨655139012817665607982345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3494074735027549909239173 655139012817665607982345)
                    ·
                      rfl

theorem cell22_1913818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 2, 1, 1, 4].length) (baseStart_1913818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1913818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1913818 prefixEnd_1913818 := by exact prefixLift 1913818
  have htrace : WordTrace (prefixWord ++ tailWord_1913818) baseStart_1913818 baseEnd_1913818 := by
    simpa [prefixWord, tailWord_1913818, baseEnd_1913818] using wordTrace_append hprefix tailTrace_1913818
  have hstable : (prefixWord ++ tailWord_1913818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913818).length < 2 ^ (prefixWord ++ tailWord_1913818).sum := by decide
  have hdescent : baseEnd_1913818 < baseStart_1913818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913827 : List Nat := [1, 1, 1, 6, 1, 1, 11]
def baseStart_1913827 : Nat := 118140960795 + 1913827 * 2 ^ 59
def prefixEnd_1913827 : Nat := 4983230072969 + 3 ^ 40 * 1913827 * 2
def baseEnd_1913827 : Nat := 24264521988947873500271

theorem tailTrace_1913827 : CollatzResearch.WordTrace tailWord_1913827 prefixEnd_1913827 24264521988947873500271 := by
  unfold tailWord_1913827
  simp only [CollatzResearch.WordTrace]
  refine ⟨69803005237539109474403735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46535336825026072982935823 69803005237539109474403735)
  ·
    refine ⟨104704507856308664211605603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69803005237539109474403735 104704507856308664211605603)
    ·
      refine ⟨157056761784462996317408405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104704507856308664211605603 157056761784462996317408405)
      ·
        refine ⟨7362035708646702952378519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 157056761784462996317408405 7362035708646702952378519)
        ·
          refine ⟨11043053562970054428567779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7362035708646702952378519 11043053562970054428567779)
          ·
            refine ⟨16564580344455081642851669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11043053562970054428567779 16564580344455081642851669)
            ·
              refine ⟨24264521988947873500271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 16564580344455081642851669 24264521988947873500271)
              ·
                rfl

theorem cell22_1913827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 11].length) (baseStart_1913827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1913827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1913827 prefixEnd_1913827 := by exact prefixLift 1913827
  have htrace : WordTrace (prefixWord ++ tailWord_1913827) baseStart_1913827 baseEnd_1913827 := by
    simpa [prefixWord, tailWord_1913827, baseEnd_1913827] using wordTrace_append hprefix tailTrace_1913827
  have hstable : (prefixWord ++ tailWord_1913827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913827).length < 2 ^ (prefixWord ++ tailWord_1913827).sum := by decide
  have hdescent : baseEnd_1913827 < baseStart_1913827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913831 : List Nat := [1, 1, 5, 2, 2, 2, 1, 1, 4, 3]
def baseStart_1913831 : Nat := 118140960795 + 1913831 * 2 ^ 59
def prefixEnd_1913831 : Nat := 4983230072969 + 3 ^ 40 * 1913831 * 2
def baseEnd_1913831 : Nat := 655143462983337907407305

theorem tailTrace_1913831 : CollatzResearch.WordTrace tailWord_1913831 prefixEnd_1913831 655143462983337907407305 := by
  unfold tailWord_1913831
  simp only [CollatzResearch.WordTrace]
  refine ⟨69803151129524618157549347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46535434086349745438366231 69803151129524618157549347)
  ·
    refine ⟨104704726694286927236324021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69803151129524618157549347 104704726694286927236324021)
    ·
      refine ⟨9816068127589399428405377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 104704726694286927236324021 9816068127589399428405377)
      ·
        refine ⟨7362051095692049571304033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9816068127589399428405377 7362051095692049571304033)
        ·
          refine ⟨5521538321769037178478025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7362051095692049571304033 5521538321769037178478025)
          ·
            refine ⟨4141153741326777883858519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5521538321769037178478025 4141153741326777883858519)
            ·
              refine ⟨6211730611990166825787779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4141153741326777883858519 6211730611990166825787779)
              ·
                refine ⟨9317595917985250238681669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6211730611990166825787779 9317595917985250238681669)
                ·
                  refine ⟨1747049234622234419752813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9317595917985250238681669 1747049234622234419752813)
                  ·
                    refine ⟨655143462983337907407305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1747049234622234419752813 655143462983337907407305)
                    ·
                      rfl

theorem cell22_1913831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 1, 4, 3].length) (baseStart_1913831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1913831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1913831 prefixEnd_1913831 := by exact prefixLift 1913831
  have htrace : WordTrace (prefixWord ++ tailWord_1913831) baseStart_1913831 baseEnd_1913831 := by
    simpa [prefixWord, tailWord_1913831, baseEnd_1913831] using wordTrace_append hprefix tailTrace_1913831
  have hstable : (prefixWord ++ tailWord_1913831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913831).length < 2 ^ (prefixWord ++ tailWord_1913831).sum := by decide
  have hdescent : baseEnd_1913831 < baseStart_1913831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913889 : List Nat := [1, 2, 3, 2, 3, 1, 2, 1, 7]
def baseStart_1913889 : Nat := 118140960795 + 1913889 * 2 ^ 59
def prefixEnd_1913889 : Nat := 4983230072969 + 3 ^ 40 * 1913889 * 2
def baseEnd_1913889 : Nat := 218387772522881696485709

theorem tailTrace_1913889 : CollatzResearch.WordTrace tailWord_1913889 prefixEnd_1913889 218387772522881696485709 := by
  unfold tailWord_1913889
  simp only [CollatzResearch.WordTrace]
  refine ⟨69805266563314494063160721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46536844375542996042107147 69805266563314494063160721)
  ·
    refine ⟨52353949922485870547370541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69805266563314494063160721 52353949922485870547370541)
    ·
      refine ⟨19632731220932201455263953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52353949922485870547370541 19632731220932201455263953)
      ·
        refine ⟨14724548415699151091447965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19632731220932201455263953 14724548415699151091447965)
        ·
          refine ⟨5521705655887181659292987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14724548415699151091447965 5521705655887181659292987)
          ·
            refine ⟨8282558483830772488939481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5521705655887181659292987 8282558483830772488939481)
            ·
              refine ⟨6211918862873079366704611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8282558483830772488939481 6211918862873079366704611)
              ·
                refine ⟨9317878294309619050056917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6211918862873079366704611 9317878294309619050056917)
                ·
                  refine ⟨218387772522881696485709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9317878294309619050056917 218387772522881696485709)
                  ·
                    rfl

theorem cell22_1913889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 1, 7].length) (baseStart_1913889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1913889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1913889 prefixEnd_1913889 := by exact prefixLift 1913889
  have htrace : WordTrace (prefixWord ++ tailWord_1913889) baseStart_1913889 baseEnd_1913889 := by
    simpa [prefixWord, tailWord_1913889, baseEnd_1913889] using wordTrace_append hprefix tailTrace_1913889
  have hstable : (prefixWord ++ tailWord_1913889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913889).length < 2 ^ (prefixWord ++ tailWord_1913889).sum := by decide
  have hdescent : baseEnd_1913889 < baseStart_1913889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913951 : List Nat := [1, 1, 2, 3, 1, 1, 5, 4, 4]
def baseStart_1913951 : Nat := 118140960795 + 1913951 * 2 ^ 59
def prefixEnd_1913951 : Nat := 4983230072969 + 3 ^ 40 * 1913951 * 2
def baseEnd_1913951 : Nat := 218394847145232531468979

theorem tailTrace_1913951 : CollatzResearch.WordTrace tailWord_1913951 prefixEnd_1913951 218394847145232531468979 := by
  unfold tailWord_1913951
  simp only [CollatzResearch.WordTrace]
  refine ⟨69807527889089878651917707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46538351926059919101278471 69807527889089878651917707)
  ·
    refine ⟨104711291833634817977876561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69807527889089878651917707 104711291833634817977876561)
    ·
      refine ⟨78533468875226113483407421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104711291833634817977876561 78533468875226113483407421)
      ·
        refine ⟨29450050828209792556277783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78533468875226113483407421 29450050828209792556277783)
        ·
          refine ⟨44175076242314688834416675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29450050828209792556277783 44175076242314688834416675)
          ·
            refine ⟨66262614363472033251625013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44175076242314688834416675 66262614363472033251625013)
            ·
              refine ⟨6212120096575503117339845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66262614363472033251625013 6212120096575503117339845)
              ·
                refine ⟨1164772518107906834501221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6212120096575503117339845 1164772518107906834501221)
                ·
                  refine ⟨218394847145232531468979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1164772518107906834501221 218394847145232531468979)
                  ·
                    rfl

theorem cell22_1913951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 4, 4].length) (baseStart_1913951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1913951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1913951 prefixEnd_1913951 := by exact prefixLift 1913951
  have htrace : WordTrace (prefixWord ++ tailWord_1913951) baseStart_1913951 baseEnd_1913951 := by
    simpa [prefixWord, tailWord_1913951, baseEnd_1913951] using wordTrace_append hprefix tailTrace_1913951
  have hstable : (prefixWord ++ tailWord_1913951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913951).length < 2 ^ (prefixWord ++ tailWord_1913951).sum := by decide
  have hdescent : baseEnd_1913951 < baseStart_1913951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913964 : List Nat := [2, 2, 1, 1, 3, 2, 2, 2, 1, 6]
def baseStart_1913964 : Nat := 118140960795 + 1913964 * 2 ^ 59
def prefixEnd_1913964 : Nat := 4983230072969 + 3 ^ 40 * 1913964 * 2
def baseEnd_1913964 : Nat := 655188991601369893831897

theorem tailTrace_1913964 : CollatzResearch.WordTrace tailWord_1913964 prefixEnd_1913964 655188991601369893831897 := by
  unfold tailWord_1913964
  simp only [CollatzResearch.WordTrace]
  refine ⟨34904001019021390936070473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46538668025361854581427297 34904001019021390936070473)
  ·
    refine ⟨26178000764266043202052855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34904001019021390936070473 26178000764266043202052855)
    ·
      refine ⟨39267001146399064803079283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26178000764266043202052855 39267001146399064803079283)
      ·
        refine ⟨58900501719598597204618925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39267001146399064803079283 58900501719598597204618925)
        ·
          refine ⟨22087688144849473951732097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58900501719598597204618925 22087688144849473951732097)
          ·
            refine ⟨16565766108637105463799073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22087688144849473951732097 16565766108637105463799073)
            ·
              refine ⟨12424324581477829097849305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16565766108637105463799073 12424324581477829097849305)
              ·
                refine ⟨9318243436108371823386979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12424324581477829097849305 9318243436108371823386979)
                ·
                  refine ⟨13977365154162557735080469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9318243436108371823386979 13977365154162557735080469)
                  ·
                    refine ⟨655188991601369893831897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13977365154162557735080469 655188991601369893831897)
                    ·
                      rfl

theorem cell22_1913964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 6].length) (baseStart_1913964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1913964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1913964 prefixEnd_1913964 := by exact prefixLift 1913964
  have htrace : WordTrace (prefixWord ++ tailWord_1913964) baseStart_1913964 baseEnd_1913964 := by
    simpa [prefixWord, tailWord_1913964, baseEnd_1913964] using wordTrace_append hprefix tailTrace_1913964
  have hstable : (prefixWord ++ tailWord_1913964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913964).length < 2 ^ (prefixWord ++ tailWord_1913964).sum := by decide
  have hdescent : baseEnd_1913964 < baseStart_1913964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1913966 : List Nat := [4, 1, 2, 2, 1, 2, 1, 3, 1, 5]
def baseStart_1913966 : Nat := 118140960795 + 1913966 * 2 ^ 59
def prefixEnd_1913966 : Nat := 4983230072969 + 3 ^ 40 * 1913966 * 2
def baseEnd_1913966 : Nat := 655189676242242555281891

theorem tailTrace_1913966 : CollatzResearch.WordTrace tailWord_1913966 prefixEnd_1913966 655189676242242555281891 := by
  unfold tailWord_1913966
  simp only [CollatzResearch.WordTrace]
  refine ⟨8726009373004442026714219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46538716656023690809142501 8726009373004442026714219)
  ·
    refine ⟨13089014059506663040071329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8726009373004442026714219 13089014059506663040071329)
    ·
      refine ⟨9816760544629997280053497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13089014059506663040071329 9816760544629997280053497)
      ·
        refine ⟨7362570408472497960040123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9816760544629997280053497 7362570408472497960040123)
        ·
          refine ⟨11043855612708746940060185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7362570408472497960040123 11043855612708746940060185)
          ·
            refine ⟨8282891709531560205045139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11043855612708746940060185 8282891709531560205045139)
            ·
              refine ⟨12424337564297340307567709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8282891709531560205045139 12424337564297340307567709)
              ·
                refine ⟨4659126586611502615337891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12424337564297340307567709 4659126586611502615337891)
                ·
                  refine ⟨6988689879917253923006837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4659126586611502615337891 6988689879917253923006837)
                  ·
                    refine ⟨655189676242242555281891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6988689879917253923006837 655189676242242555281891)
                    ·
                      rfl

theorem cell22_1913966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_1913966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1913966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1913966 prefixEnd_1913966 := by exact prefixLift 1913966
  have htrace : WordTrace (prefixWord ++ tailWord_1913966) baseStart_1913966 baseEnd_1913966 := by
    simpa [prefixWord, tailWord_1913966, baseEnd_1913966] using wordTrace_append hprefix tailTrace_1913966
  have hstable : (prefixWord ++ tailWord_1913966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1913966).length < 2 ^ (prefixWord ++ tailWord_1913966).sum := by decide
  have hdescent : baseEnd_1913966 < baseStart_1913966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1913966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914045 : List Nat := [1, 4, 1, 2, 1, 1, 5, 3, 1, 3]
def baseStart_1914045 : Nat := 118140960795 + 1914045 * 2 ^ 59
def prefixEnd_1914045 : Nat := 4983230072969 + 3 ^ 40 * 1914045 * 2
def baseEnd_1914045 : Nat := 655216719556712682556649

theorem tailTrace_1914045 : CollatzResearch.WordTrace tailWord_1914045 prefixEnd_1914045 655216719556712682556649 := by
  unfold tailWord_1914045
  simp only [CollatzResearch.WordTrace]
  refine ⟨69810956350749332705839589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46540637567166221803893059 69810956350749332705839589)
  ·
    refine ⟨13089554315765499882344923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69810956350749332705839589 13089554315765499882344923)
    ·
      refine ⟨19634331473648249823517385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13089554315765499882344923 19634331473648249823517385)
      ·
        refine ⟨14725748605236187367638039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19634331473648249823517385 14725748605236187367638039)
        ·
          refine ⟨22088622907854281051457059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14725748605236187367638039 22088622907854281051457059)
          ·
            refine ⟨33132934361781421577185589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22088622907854281051457059 33132934361781421577185589)
            ·
              refine ⟨3106212596417008272861149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33132934361781421577185589 3106212596417008272861149)
              ·
                refine ⟨1164829723656378102322931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3106212596417008272861149 1164829723656378102322931)
                ·
                  refine ⟨1747244585484567153484397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1164829723656378102322931 1747244585484567153484397)
                  ·
                    refine ⟨655216719556712682556649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1747244585484567153484397 655216719556712682556649)
                    ·
                      rfl

theorem cell22_1914045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 3, 1, 3].length) (baseStart_1914045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1914045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1914045 prefixEnd_1914045 := by exact prefixLift 1914045
  have htrace : WordTrace (prefixWord ++ tailWord_1914045) baseStart_1914045 baseEnd_1914045 := by
    simpa [prefixWord, tailWord_1914045, baseEnd_1914045] using wordTrace_append hprefix tailTrace_1914045
  have hstable : (prefixWord ++ tailWord_1914045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914045).length < 2 ^ (prefixWord ++ tailWord_1914045).sum := by decide
  have hdescent : baseEnd_1914045 < baseStart_1914045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914062 : List Nat := [4, 1, 1, 1, 6, 1, 1, 1, 3, 3]
def baseStart_1914062 : Nat := 118140960795 + 1914062 * 2 ^ 59
def prefixEnd_1914062 : Nat := 4983230072969 + 3 ^ 40 * 1914062 * 2
def baseEnd_1914062 : Nat := 655222539004130304881597

theorem tailTrace_1914062 : CollatzResearch.WordTrace tailWord_1914062 prefixEnd_1914062 655222539004130304881597 := by
  unfold tailWord_1914062
  simp only [CollatzResearch.WordTrace]
  refine ⟨8726447048960968076151055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46541050927791829739472293 8726447048960968076151055)
  ·
    refine ⟨13089670573441452114226583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8726447048960968076151055 13089670573441452114226583)
    ·
      refine ⟨19634505860162178171339875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13089670573441452114226583 19634505860162178171339875)
      ·
        refine ⟨29451758790243267257009813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19634505860162178171339875 29451758790243267257009813)
        ·
          refine ⟨1380551193292653152672335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 29451758790243267257009813 1380551193292653152672335)
          ·
            refine ⟨2070826789938979729008503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1380551193292653152672335 2070826789938979729008503)
            ·
              refine ⟨3106240184908469593512755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2070826789938979729008503 3106240184908469593512755)
              ·
                refine ⟨4659360277362704390269133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3106240184908469593512755 4659360277362704390269133)
                ·
                  refine ⟨1747260104011014146350925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4659360277362704390269133 1747260104011014146350925)
                  ·
                    refine ⟨655222539004130304881597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1747260104011014146350925 655222539004130304881597)
                    ·
                      rfl

theorem cell22_1914062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 1, 3, 3].length) (baseStart_1914062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1914062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1914062 prefixEnd_1914062 := by exact prefixLift 1914062
  have htrace : WordTrace (prefixWord ++ tailWord_1914062) baseStart_1914062 baseEnd_1914062 := by
    simpa [prefixWord, tailWord_1914062, baseEnd_1914062] using wordTrace_append hprefix tailTrace_1914062
  have hstable : (prefixWord ++ tailWord_1914062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914062).length < 2 ^ (prefixWord ++ tailWord_1914062).sum := by decide
  have hdescent : baseEnd_1914062 < baseStart_1914062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914120 : List Nat := [2, 1, 3, 2, 4, 1, 1, 4, 4]
def baseStart_1914120 : Nat := 118140960795 + 1914120 * 2 ^ 59
def prefixEnd_1914120 : Nat := 4983230072969 + 3 ^ 40 * 1914120 * 2
def baseEnd_1914120 : Nat := 218414131196479162310473

theorem tailTrace_1914120 : CollatzResearch.WordTrace tailWord_1914120 prefixEnd_1914120 218414131196479162310473 := by
  unfold tailWord_1914120
  simp only [CollatzResearch.WordTrace]
  refine ⟨34906845912738810257409907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46542461216985080343213209 34906845912738810257409907)
  ·
    refine ⟨52360268869108215386114861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34906845912738810257409907 52360268869108215386114861)
    ·
      refine ⟨19635100825915580769793073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52360268869108215386114861 19635100825915580769793073)
      ·
        refine ⟨14726325619436685577344805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19635100825915580769793073 14726325619436685577344805)
        ·
          refine ⟨2761186053644378545752151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14726325619436685577344805 2761186053644378545752151)
          ·
            refine ⟨4141779080466567818628227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2761186053644378545752151 4141779080466567818628227)
            ·
              refine ⟨6212668620699851727942341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4141779080466567818628227 6212668620699851727942341)
              ·
                refine ⟨1164875366381222198989189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6212668620699851727942341 1164875366381222198989189)
                ·
                  refine ⟨218414131196479162310473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1164875366381222198989189 218414131196479162310473)
                  ·
                    rfl

theorem cell22_1914120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 4, 4].length) (baseStart_1914120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1914120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1914120 prefixEnd_1914120 := by exact prefixLift 1914120
  have htrace : WordTrace (prefixWord ++ tailWord_1914120) baseStart_1914120 baseEnd_1914120 := by
    simpa [prefixWord, tailWord_1914120, baseEnd_1914120] using wordTrace_append hprefix tailTrace_1914120
  have hstable : (prefixWord ++ tailWord_1914120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914120).length < 2 ^ (prefixWord ++ tailWord_1914120).sum := by decide
  have hdescent : baseEnd_1914120 < baseStart_1914120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914148 : List Nat := [2, 3, 1, 3, 1, 1, 5, 6]
def baseStart_1914148 : Nat := 118140960795 + 1914148 * 2 ^ 59
def prefixEnd_1914148 : Nat := 4983230072969 + 3 ^ 40 * 1914148 * 2
def baseEnd_1914148 : Nat := 72805775395739416359037

theorem tailTrace_1914148 : CollatzResearch.WordTrace tailWord_1914148 prefixEnd_1914148 72805775395739416359037 := by
  unfold tailWord_1914148
  simp only [CollatzResearch.WordTrace]
  refine ⟨34907356534688090648419549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46543142046250787531226065 34907356534688090648419549)
  ·
    refine ⟨13090258700508033993157331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34907356534688090648419549 13090258700508033993157331)
    ·
      refine ⟨19635388050762050989735997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13090258700508033993157331 19635388050762050989735997)
      ·
        refine ⟨7363270519035769121150999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19635388050762050989735997 7363270519035769121150999)
        ·
          refine ⟨11044905778553653681726499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7363270519035769121150999 11044905778553653681726499)
          ·
            refine ⟨16567358667830480522589749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11044905778553653681726499 16567358667830480522589749)
            ·
              refine ⟨1553189875109107548992789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16567358667830480522589749 1553189875109107548992789)
              ·
                refine ⟨72805775395739416359037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1553189875109107548992789 72805775395739416359037)
                ·
                  rfl

theorem cell22_1914148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 5, 6].length) (baseStart_1914148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1914148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1914148 prefixEnd_1914148 := by exact prefixLift 1914148
  have htrace : WordTrace (prefixWord ++ tailWord_1914148) baseStart_1914148 baseEnd_1914148 := by
    simpa [prefixWord, tailWord_1914148, baseEnd_1914148] using wordTrace_append hprefix tailTrace_1914148
  have hstable : (prefixWord ++ tailWord_1914148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914148).length < 2 ^ (prefixWord ++ tailWord_1914148).sum := by decide
  have hdescent : baseEnd_1914148 < baseStart_1914148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914169 : List Nat := [1, 2, 1, 6, 3, 1, 1, 2, 2, 3]
def baseStart_1914169 : Nat := 118140960795 + 1914169 * 2 ^ 59
def prefixEnd_1914169 : Nat := 4983230072969 + 3 ^ 40 * 1914169 * 2
def baseEnd_1914169 : Nat := 655259167290817692456269

theorem tailTrace_1914169 : CollatzResearch.WordTrace tailWord_1914169 prefixEnd_1914169 655259167290817692456269 := by
  unfold tailWord_1914169
  simp only [CollatzResearch.WordTrace]
  refine ⟨69815479002300101883353561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46543652668200067922235707 69815479002300101883353561)
  ·
    refine ⟨52361609251725076412515171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69815479002300101883353561 52361609251725076412515171)
    ·
      refine ⟨78542413877587614618772757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52361609251725076412515171 78542413877587614618772757)
      ·
        refine ⟨3681675650511919435254973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 78542413877587614618772757 3681675650511919435254973)
        ·
          refine ⟨1380628368941969788220615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3681675650511919435254973 1380628368941969788220615)
          ·
            refine ⟨2070942553412954682330923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1380628368941969788220615 2070942553412954682330923)
            ·
              refine ⟨3106413830119432023496385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2070942553412954682330923 3106413830119432023496385)
              ·
                refine ⟨2329810372589574017622289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3106413830119432023496385 2329810372589574017622289)
                ·
                  refine ⟨1747357779442180513216717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2329810372589574017622289 1747357779442180513216717)
                  ·
                    refine ⟨655259167290817692456269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1747357779442180513216717 655259167290817692456269)
                    ·
                      rfl

theorem cell22_1914169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 2, 2, 3].length) (baseStart_1914169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1914169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1914169 prefixEnd_1914169 := by exact prefixLift 1914169
  have htrace : WordTrace (prefixWord ++ tailWord_1914169) baseStart_1914169 baseEnd_1914169 := by
    simpa [prefixWord, tailWord_1914169, baseEnd_1914169] using wordTrace_append hprefix tailTrace_1914169
  have hstable : (prefixWord ++ tailWord_1914169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914169).length < 2 ^ (prefixWord ++ tailWord_1914169).sum := by decide
  have hdescent : baseEnd_1914169 < baseStart_1914169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914176 : List Nat := [2, 1, 1, 2, 2, 1, 5, 1, 7]
def baseStart_1914176 : Nat := 118140960795 + 1914176 * 2 ^ 59
def prefixEnd_1914176 : Nat := 4983230072969 + 3 ^ 40 * 1914176 * 2
def baseEnd_1914176 : Nat := 218420521177957335843749

theorem tailTrace_1914176 : CollatzResearch.WordTrace tailWord_1914176 prefixEnd_1914176 218420521177957335843749 := by
  unfold tailWord_1914176
  simp only [CollatzResearch.WordTrace]
  refine ⟨34907867156637371039429191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46543822875516494719238921 34907867156637371039429191)
  ·
    refine ⟨52361800734956056559143787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34907867156637371039429191 52361800734956056559143787)
    ·
      refine ⟨78542701102434084838715681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52361800734956056559143787 78542701102434084838715681)
      ·
        refine ⟨58907025826825563629036761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78542701102434084838715681 58907025826825563629036761)
        ·
          refine ⟨44180269370119172721777571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58907025826825563629036761 44180269370119172721777571)
          ·
            refine ⟨66270404055178759082666357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44180269370119172721777571 66270404055178759082666357)
            ·
              refine ⟨6212850380173008663999971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66270404055178759082666357 6212850380173008663999971)
              ·
                refine ⟨9319275570259512995999957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6212850380173008663999971 9319275570259512995999957)
                ·
                  refine ⟨218420521177957335843749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9319275570259512995999957 218420521177957335843749)
                  ·
                    rfl

theorem cell22_1914176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 1, 7].length) (baseStart_1914176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1914176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1914176 prefixEnd_1914176 := by exact prefixLift 1914176
  have htrace : WordTrace (prefixWord ++ tailWord_1914176) baseStart_1914176 baseEnd_1914176 := by
    simpa [prefixWord, tailWord_1914176, baseEnd_1914176] using wordTrace_append hprefix tailTrace_1914176
  have hstable : (prefixWord ++ tailWord_1914176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914176).length < 2 ^ (prefixWord ++ tailWord_1914176).sum := by decide
  have hdescent : baseEnd_1914176 < baseStart_1914176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914223 : List Nat := [1, 1, 2, 1, 3, 1, 3, 5, 1, 4]
def baseStart_1914223 : Nat := 118140960795 + 1914223 * 2 ^ 59
def prefixEnd_1914223 : Nat := 4983230072969 + 3 ^ 40 * 1914223 * 2
def baseEnd_1914223 : Nat := 655277652594379551606103

theorem tailTrace_1914223 : CollatzResearch.WordTrace tailWord_1914223 prefixEnd_1914223 655277652594379551606103 := by
  unfold tailWord_1914223
  simp only [CollatzResearch.WordTrace]
  refine ⟨69817448544104469105819323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46544965696069646070546215 69817448544104469105819323)
  ·
    refine ⟨104726172816156703658728985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69817448544104469105819323 104726172816156703658728985)
    ·
      refine ⟨78544629612117527744046739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104726172816156703658728985 78544629612117527744046739)
      ·
        refine ⟨117816944418176291616070109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78544629612117527744046739 117816944418176291616070109)
        ·
          refine ⟨44181354156816109356026291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117816944418176291616070109 44181354156816109356026291)
          ·
            refine ⟨66272031235224164034039437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44181354156816109356026291 66272031235224164034039437)
            ·
              refine ⟨24852011713209061512764789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66272031235224164034039437 24852011713209061512764789)
              ·
                refine ⟨2329876098113349516821699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24852011713209061512764789 2329876098113349516821699)
                ·
                  refine ⟨3494814147170024275232549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2329876098113349516821699 3494814147170024275232549)
                  ·
                    refine ⟨655277652594379551606103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3494814147170024275232549 655277652594379551606103)
                    ·
                      rfl

theorem cell22_1914223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 5, 1, 4].length) (baseStart_1914223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1914223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1914223 prefixEnd_1914223 := by exact prefixLift 1914223
  have htrace : WordTrace (prefixWord ++ tailWord_1914223) baseStart_1914223 baseEnd_1914223 := by
    simpa [prefixWord, tailWord_1914223, baseEnd_1914223] using wordTrace_append hprefix tailTrace_1914223
  have hstable : (prefixWord ++ tailWord_1914223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914223).length < 2 ^ (prefixWord ++ tailWord_1914223).sum := by decide
  have hdescent : baseEnd_1914223 < baseStart_1914223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914306 : List Nat := [3, 5, 2, 1, 1, 1, 1, 2, 6]
def baseStart_1914306 : Nat := 118140960795 + 1914306 * 2 ^ 59
def prefixEnd_1914306 : Nat := 4983230072969 + 3 ^ 40 * 1914306 * 2
def baseEnd_1914306 : Nat := 218435355063531667260283

theorem tailTrace_1914306 : CollatzResearch.WordTrace tailWord_1914306 prefixEnd_1914306 218435355063531667260283 := by
  unfold tailWord_1914306
  simp only [CollatzResearch.WordTrace]
  refine ⟨17455118950700943570272693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46546983868535849520727181 17455118950700943570272693)
  ·
    refine ⟨1636417401628213459713065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17455118950700943570272693 1636417401628213459713065)
    ·
      refine ⟨1227313051221160094784799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1636417401628213459713065 1227313051221160094784799)
      ·
        refine ⟨1840969576831740142177199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1227313051221160094784799 1840969576831740142177199)
        ·
          refine ⟨2761454365247610213265799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1840969576831740142177199 2761454365247610213265799)
          ·
            refine ⟨4142181547871415319898699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2761454365247610213265799 4142181547871415319898699)
            ·
              refine ⟨6213272321807122979848049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4142181547871415319898699 6213272321807122979848049)
              ·
                refine ⟨4659954241355342234886037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6213272321807122979848049 4659954241355342234886037)
                ·
                  refine ⟨218435355063531667260283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4659954241355342234886037 218435355063531667260283)
                  ·
                    rfl

theorem cell22_1914306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_1914306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1914306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1914306 prefixEnd_1914306 := by exact prefixLift 1914306
  have htrace : WordTrace (prefixWord ++ tailWord_1914306) baseStart_1914306 baseEnd_1914306 := by
    simpa [prefixWord, tailWord_1914306, baseEnd_1914306] using wordTrace_append hprefix tailTrace_1914306
  have hstable : (prefixWord ++ tailWord_1914306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914306).length < 2 ^ (prefixWord ++ tailWord_1914306).sum := by decide
  have hdescent : baseEnd_1914306 < baseStart_1914306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914349 : List Nat := [1, 5, 1, 3, 2, 1, 2, 1, 3, 3]
def baseStart_1914349 : Nat := 118140960795 + 1914349 * 2 ^ 59
def prefixEnd_1914349 : Nat := 4983230072969 + 3 ^ 40 * 1914349 * 2
def baseEnd_1914349 : Nat := 655320784969357222955717

theorem tailTrace_1914349 : CollatzResearch.WordTrace tailWord_1914349 prefixEnd_1914349 655320784969357222955717 := by
  unfold tailWord_1914349
  simp only [CollatzResearch.WordTrace]
  refine ⟨69822044141647992624906101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46548029427765328416604067 69822044141647992624906101)
  ·
    refine ⟨6545816638279499308584947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69822044141647992624906101 6545816638279499308584947)
    ·
      refine ⟨9818724957419248962877421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6545816638279499308584947 9818724957419248962877421)
      ·
        refine ⟨3682021859032218361079033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9818724957419248962877421 3682021859032218361079033)
        ·
          refine ⟨2761516394274163770809275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3682021859032218361079033 2761516394274163770809275)
          ·
            refine ⟨4142274591411245656213913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2761516394274163770809275 4142274591411245656213913)
            ·
              refine ⟨3106705943558434242160435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4142274591411245656213913 3106705943558434242160435)
              ·
                refine ⟨4660058915337651363240653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3106705943558434242160435 4660058915337651363240653)
                ·
                  refine ⟨1747522093251619261215245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4660058915337651363240653 1747522093251619261215245)
                  ·
                    refine ⟨655320784969357222955717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1747522093251619261215245 655320784969357222955717)
                    ·
                      rfl

theorem cell22_1914349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 1, 3, 3].length) (baseStart_1914349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1914349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1914349 prefixEnd_1914349 := by exact prefixLift 1914349
  have htrace : WordTrace (prefixWord ++ tailWord_1914349) baseStart_1914349 baseEnd_1914349 := by
    simpa [prefixWord, tailWord_1914349, baseEnd_1914349] using wordTrace_append hprefix tailTrace_1914349
  have hstable : (prefixWord ++ tailWord_1914349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914349).length < 2 ^ (prefixWord ++ tailWord_1914349).sum := by decide
  have hdescent : baseEnd_1914349 < baseStart_1914349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914555 : List Nat := [1, 1, 1, 1, 1, 2, 3, 2, 6, 4]
def baseStart_1914555 : Nat := 118140960795 + 1914555 * 2 ^ 59
def prefixEnd_1914555 : Nat := 4983230072969 + 3 ^ 40 * 1914555 * 2
def baseEnd_1914555 : Nat := 655391302979241352305085

theorem tailTrace_1914555 : CollatzResearch.WordTrace tailWord_1914555 prefixEnd_1914555 655391302979241352305085 := by
  unfold tailWord_1914555
  simp only [CollatzResearch.WordTrace]
  refine ⟨69829557578901689806905119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46553038385934459871270079 69829557578901689806905119)
  ·
    refine ⟨104744336368352534710357679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69829557578901689806905119 104744336368352534710357679)
    ·
      refine ⟨157116504552528802065536519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104744336368352534710357679 157116504552528802065536519)
      ·
        refine ⟨235674756828793203098304779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157116504552528802065536519 235674756828793203098304779)
        ·
          refine ⟨353512135243189804647457169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235674756828793203098304779 353512135243189804647457169)
          ·
            refine ⟨265134101432392353485592877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 353512135243189804647457169 265134101432392353485592877)
            ·
              refine ⟨99425288037147132557097329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 265134101432392353485592877 99425288037147132557097329)
              ·
                refine ⟨74568966027860349417822997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99425288037147132557097329 74568966027860349417822997)
                ·
                  refine ⟨3495420282555953878960453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 74568966027860349417822997 3495420282555953878960453)
                  ·
                    refine ⟨655391302979241352305085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3495420282555953878960453 655391302979241352305085)
                    ·
                      rfl

theorem cell22_1914555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 6, 4].length) (baseStart_1914555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1914555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1914555 prefixEnd_1914555 := by exact prefixLift 1914555
  have htrace : WordTrace (prefixWord ++ tailWord_1914555) baseStart_1914555 baseEnd_1914555 := by
    simpa [prefixWord, tailWord_1914555, baseEnd_1914555] using wordTrace_append hprefix tailTrace_1914555
  have hstable : (prefixWord ++ tailWord_1914555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914555).length < 2 ^ (prefixWord ++ tailWord_1914555).sum := by decide
  have hdescent : baseEnd_1914555 < baseStart_1914555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914557 : List Nat := [1, 4, 1, 2, 1, 2, 1, 1, 6, 3]
def baseStart_1914557 : Nat := 118140960795 + 1914557 * 2 ^ 59
def prefixEnd_1914557 : Nat := 4983230072969 + 3 ^ 40 * 1914557 * 2
def baseEnd_1914557 : Nat := 655391987620114013755079

theorem tailTrace_1914557 : CollatzResearch.WordTrace tailWord_1914557 prefixEnd_1914557 655391987620114013755079 := by
  unfold tailWord_1914557
  simp only [CollatzResearch.WordTrace]
  refine ⟨69829630524894444148477925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46553087016596296098985283 69829630524894444148477925)
  ·
    refine ⟨13093055723417708277839611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69829630524894444148477925 13093055723417708277839611)
    ·
      refine ⟨19639583585126562416759417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13093055723417708277839611 19639583585126562416759417)
      ·
        refine ⟨14729687688844921812569563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19639583585126562416759417 14729687688844921812569563)
        ·
          refine ⟨22094531533267382718854345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14729687688844921812569563 22094531533267382718854345)
          ·
            refine ⟨16570898649950537039140759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22094531533267382718854345 16570898649950537039140759)
            ·
              refine ⟨24856347974925805558711139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16570898649950537039140759 24856347974925805558711139)
              ·
                refine ⟨37284521962388708338066709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24856347974925805558711139 37284521962388708338066709)
                ·
                  refine ⟨1747711966986970703346877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 37284521962388708338066709 1747711966986970703346877)
                  ·
                    refine ⟨655391987620114013755079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1747711966986970703346877 655391987620114013755079)
                    ·
                      rfl

theorem cell22_1914557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 6, 3].length) (baseStart_1914557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1914557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1914557 prefixEnd_1914557 := by exact prefixLift 1914557
  have htrace : WordTrace (prefixWord ++ tailWord_1914557) baseStart_1914557 baseEnd_1914557 := by
    simpa [prefixWord, tailWord_1914557, baseEnd_1914557] using wordTrace_append hprefix tailTrace_1914557
  have hstable : (prefixWord ++ tailWord_1914557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914557).length < 2 ^ (prefixWord ++ tailWord_1914557).sum := by decide
  have hdescent : baseEnd_1914557 < baseStart_1914557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914574 : List Nat := [4, 1, 1, 1, 3, 1, 2, 4, 2, 3]
def baseStart_1914574 : Nat := 118140960795 + 1914574 * 2 ^ 59
def prefixEnd_1914574 : Nat := 4983230072969 + 3 ^ 40 * 1914574 * 2
def baseEnd_1914574 : Nat := 655397807067531636080027

theorem tailTrace_1914574 : CollatzResearch.WordTrace tailWord_1914574 prefixEnd_1914574 655397807067531636080027 := by
  unfold tailWord_1914574
  simp only [CollatzResearch.WordTrace]
  refine ⟨8728781320729107006480847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46553500377221904034564517 8728781320729107006480847)
  ·
    refine ⟨13093171981093660509721271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8728781320729107006480847 13093171981093660509721271)
    ·
      refine ⟨19639757971640490764581907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13093171981093660509721271 19639757971640490764581907)
      ·
        refine ⟨29459636957460736146872861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19639757971640490764581907 29459636957460736146872861)
        ·
          refine ⟨11047363859047776055077323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29459636957460736146872861 11047363859047776055077323)
          ·
            refine ⟨16571045788571664082615985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11047363859047776055077323 16571045788571664082615985)
            ·
              refine ⟨12428284341428748061961989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16571045788571664082615985 12428284341428748061961989)
              ·
                refine ⟨2330303314017890261617873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12428284341428748061961989 2330303314017890261617873)
                ·
                  refine ⟨1747727485513417696213405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2330303314017890261617873 1747727485513417696213405)
                  ·
                    refine ⟨655397807067531636080027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1747727485513417696213405 655397807067531636080027)
                    ·
                      rfl

theorem cell22_1914574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 4, 2, 3].length) (baseStart_1914574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1914574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1914574 prefixEnd_1914574 := by exact prefixLift 1914574
  have htrace : WordTrace (prefixWord ++ tailWord_1914574) baseStart_1914574 baseEnd_1914574 := by
    simpa [prefixWord, tailWord_1914574, baseEnd_1914574] using wordTrace_append hprefix tailTrace_1914574
  have hstable : (prefixWord ++ tailWord_1914574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914574).length < 2 ^ (prefixWord ++ tailWord_1914574).sum := by decide
  have hdescent : baseEnd_1914574 < baseStart_1914574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914615 : List Nat := [1, 1, 3, 1, 1, 1, 4, 1, 9]
def baseStart_1914615 : Nat := 118140960795 + 1914615 * 2 ^ 59
def prefixEnd_1914615 : Nat := 4983230072969 + 3 ^ 40 * 1914615 * 2
def baseEnd_1914615 : Nat := 218470614068473731934967

theorem tailTrace_1914615 : CollatzResearch.WordTrace tailWord_1914615 prefixEnd_1914615 218470614068473731934967 := by
  unfold tailWord_1914615
  simp only [CollatzResearch.WordTrace]
  refine ⟨69831745958684320054089299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46554497305789546702726199 69831745958684320054089299)
  ·
    refine ⟨104747618938026480081133949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69831745958684320054089299 104747618938026480081133949)
    ·
      refine ⟨39280357101759930030425231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104747618938026480081133949 39280357101759930030425231)
      ·
        refine ⟨58920535652639895045637847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39280357101759930030425231 58920535652639895045637847)
        ·
          refine ⟨88380803478959842568456771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58920535652639895045637847 88380803478959842568456771)
          ·
            refine ⟨132571205218439763852685157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88380803478959842568456771 132571205218439763852685157)
            ·
              refine ⟨24857100978457455722378467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 132571205218439763852685157 24857100978457455722378467)
              ·
                refine ⟨37285651467686183583567701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24857100978457455722378467 37285651467686183583567701)
                ·
                  refine ⟨218470614068473731934967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 37285651467686183583567701 218470614068473731934967)
                  ·
                    rfl

theorem cell22_1914615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 9].length) (baseStart_1914615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1914615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1914615 prefixEnd_1914615 := by exact prefixLift 1914615
  have htrace : WordTrace (prefixWord ++ tailWord_1914615) baseStart_1914615 baseEnd_1914615 := by
    simpa [prefixWord, tailWord_1914615, baseEnd_1914615] using wordTrace_append hprefix tailTrace_1914615
  have hstable : (prefixWord ++ tailWord_1914615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914615).length < 2 ^ (prefixWord ++ tailWord_1914615).sum := by decide
  have hdescent : baseEnd_1914615 < baseStart_1914615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914647 : List Nat := [1, 1, 3, 4, 2, 1, 1, 1, 1, 7]
def baseStart_1914647 : Nat := 118140960795 + 1914647 * 2 ^ 59
def prefixEnd_1914647 : Nat := 4983230072969 + 3 ^ 40 * 1914647 * 2
def baseEnd_1914647 : Nat := 655422796459383779004803

theorem tailTrace_1914647 : CollatzResearch.WordTrace tailWord_1914647 prefixEnd_1914647 655422796459383779004803 := by
  unfold tailWord_1914647
  simp only [CollatzResearch.WordTrace]
  refine ⟨69832913094568389519254195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46555275396378926346169463 69832913094568389519254195)
  ·
    refine ⟨104749369641852584278881293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69832913094568389519254195 104749369641852584278881293)
    ·
      refine ⟨39281013615694719104580485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104749369641852584278881293 39281013615694719104580485)
      ·
        refine ⟨7365190052942759832108841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39281013615694719104580485 7365190052942759832108841)
        ·
          refine ⟨5523892539707069874081631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7365190052942759832108841 5523892539707069874081631)
          ·
            refine ⟨8285838809560604811122447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5523892539707069874081631 8285838809560604811122447)
            ·
              refine ⟨12428758214340907216683671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8285838809560604811122447 12428758214340907216683671)
              ·
                refine ⟨18643137321511360825025507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12428758214340907216683671 18643137321511360825025507)
                ·
                  refine ⟨27964705982267041237538261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18643137321511360825025507 27964705982267041237538261)
                  ·
                    refine ⟨655422796459383779004803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27964705982267041237538261 655422796459383779004803)
                    ·
                      rfl

theorem cell22_1914647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 7].length) (baseStart_1914647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1914647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1914647 prefixEnd_1914647 := by exact prefixLift 1914647
  have htrace : WordTrace (prefixWord ++ tailWord_1914647) baseStart_1914647 baseEnd_1914647 := by
    simpa [prefixWord, tailWord_1914647, baseEnd_1914647] using wordTrace_append hprefix tailTrace_1914647
  have hstable : (prefixWord ++ tailWord_1914647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914647).length < 2 ^ (prefixWord ++ tailWord_1914647).sum := by decide
  have hdescent : baseEnd_1914647 < baseStart_1914647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914670 : List Nat := [4, 1, 3, 2, 2, 1, 2, 3, 1, 3]
def baseStart_1914670 : Nat := 118140960795 + 1914670 * 2 ^ 59
def prefixEnd_1914670 : Nat := 4983230072969 + 3 ^ 40 * 1914670 * 2
def baseEnd_1914670 : Nat := 655430669829419385679733

theorem tailTrace_1914670 : CollatzResearch.WordTrace tailWord_1914670 prefixEnd_1914670 655430669829419385679733 := by
  unfold tailWord_1914670
  simp only [CollatzResearch.WordTrace]
  refine ⟨8729218996685633055917683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46555834648990042964894309 8729218996685633055917683)
  ·
    refine ⟨13093828495028449583876525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8729218996685633055917683 13093828495028449583876525)
    ·
      refine ⟨4910185685635668593953697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13093828495028449583876525 4910185685635668593953697)
      ·
        refine ⟨3682639264226751445465273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4910185685635668593953697 3682639264226751445465273)
        ·
          refine ⟨2761979448170063584098955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3682639264226751445465273 2761979448170063584098955)
          ·
            refine ⟨4142969172255095376148433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2761979448170063584098955 4142969172255095376148433)
            ·
              refine ⟨3107226879191321532111325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4142969172255095376148433 3107226879191321532111325)
              ·
                refine ⟨1165210079696745574541747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3107226879191321532111325 1165210079696745574541747)
                ·
                  refine ⟨1747815119545118361812621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1165210079696745574541747 1747815119545118361812621)
                  ·
                    refine ⟨655430669829419385679733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1747815119545118361812621 655430669829419385679733)
                    ·
                      rfl

theorem cell22_1914670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_1914670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1914670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1914670 prefixEnd_1914670 := by exact prefixLift 1914670
  have htrace : WordTrace (prefixWord ++ tailWord_1914670) baseStart_1914670 baseEnd_1914670 := by
    simpa [prefixWord, tailWord_1914670, baseEnd_1914670] using wordTrace_append hprefix tailTrace_1914670
  have hstable : (prefixWord ++ tailWord_1914670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914670).length < 2 ^ (prefixWord ++ tailWord_1914670).sum := by decide
  have hdescent : baseEnd_1914670 < baseStart_1914670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914709 : List Nat := [1, 3, 2, 2, 2, 2, 3, 1, 1, 5]
def baseStart_1914709 : Nat := 118140960795 + 1914709 * 2 ^ 59
def prefixEnd_1914709 : Nat := 4983230072969 + 3 ^ 40 * 1914709 * 2
def baseEnd_1914709 : Nat := 655444020326436283954613

theorem tailTrace_1914709 : CollatzResearch.WordTrace tailWord_1914709 prefixEnd_1914709 655444020326436283954613 := by
  unfold tailWord_1914709
  simp only [CollatzResearch.WordTrace]
  refine ⟨69835174420343774108011181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46556782946895849405340787 69835174420343774108011181)
  ·
    refine ⟨26188190407628915290504193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69835174420343774108011181 26188190407628915290504193)
    ·
      refine ⟨19641142805721686467878145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26188190407628915290504193 19641142805721686467878145)
      ·
        refine ⟨14730857104291264850908609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19641142805721686467878145 14730857104291264850908609)
        ·
          refine ⟨11048142828218448638181457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14730857104291264850908609 11048142828218448638181457)
          ·
            refine ⟨8286107121163836478636093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11048142828218448638181457 8286107121163836478636093)
            ·
              refine ⟨3107290170436438679488535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8286107121163836478636093 3107290170436438679488535)
              ·
                refine ⟨4660935255654658019232803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3107290170436438679488535 4660935255654658019232803)
                ·
                  refine ⟨6991402883481987028849205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4660935255654658019232803 6991402883481987028849205)
                  ·
                    refine ⟨655444020326436283954613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6991402883481987028849205 655444020326436283954613)
                    ·
                      rfl

theorem cell22_1914709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 1, 1, 5].length) (baseStart_1914709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1914709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1914709 prefixEnd_1914709 := by exact prefixLift 1914709
  have htrace : WordTrace (prefixWord ++ tailWord_1914709) baseStart_1914709 baseEnd_1914709 := by
    simpa [prefixWord, tailWord_1914709, baseEnd_1914709] using wordTrace_append hprefix tailTrace_1914709
  have hstable : (prefixWord ++ tailWord_1914709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914709).length < 2 ^ (prefixWord ++ tailWord_1914709).sum := by decide
  have hdescent : baseEnd_1914709 < baseStart_1914709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914752 : List Nat := [2, 1, 1, 2, 1, 2, 4, 1, 2, 6]
def baseStart_1914752 : Nat := 118140960795 + 1914752 * 2 ^ 59
def prefixEnd_1914752 : Nat := 4983230072969 + 3 ^ 40 * 1914752 * 2
def baseEnd_1914752 : Nat := 655458740105198505129481

theorem tailTrace_1914752 : CollatzResearch.WordTrace tailWord_1914752 prefixEnd_1914752 655458740105198505129481 := by
  unfold tailWord_1914752
  simp only [CollatzResearch.WordTrace]
  refine ⟨34918371379593996225913255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46557828506125328301217673 34918371379593996225913255)
  ·
    refine ⟨52377557069390994338869883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34918371379593996225913255 52377557069390994338869883)
    ·
      refine ⟨78566335604086491508304825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52377557069390994338869883 78566335604086491508304825)
      ·
        refine ⟨58924751703064868631228619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78566335604086491508304825 58924751703064868631228619)
        ·
          refine ⟨88387127554597302946842929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58924751703064868631228619 88387127554597302946842929)
          ·
            refine ⟨66290345665947977210132197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88387127554597302946842929 66290345665947977210132197)
            ·
              refine ⟨12429439812365245726899787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66290345665947977210132197 12429439812365245726899787)
              ·
                refine ⟨18644159718547868590349681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12429439812365245726899787 18644159718547868590349681)
                ·
                  refine ⟨13983119788910901442762261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18644159718547868590349681 13983119788910901442762261)
                  ·
                    refine ⟨655458740105198505129481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13983119788910901442762261 655458740105198505129481)
                    ·
                      rfl

theorem cell22_1914752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 2, 6].length) (baseStart_1914752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1914752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1914752 prefixEnd_1914752 := by exact prefixLift 1914752
  have htrace : WordTrace (prefixWord ++ tailWord_1914752) baseStart_1914752 baseEnd_1914752 := by
    simpa [prefixWord, tailWord_1914752, baseEnd_1914752] using wordTrace_append hprefix tailTrace_1914752
  have hstable : (prefixWord ++ tailWord_1914752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914752).length < 2 ^ (prefixWord ++ tailWord_1914752).sum := by decide
  have hdescent : baseEnd_1914752 < baseStart_1914752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914760 : List Nat := [2, 1, 3, 3, 3, 2, 2, 1, 2, 3]
def baseStart_1914760 : Nat := 118140960795 + 1914760 * 2 ^ 59
def prefixEnd_1914760 : Nat := 4983230072969 + 3 ^ 40 * 1914760 * 2
def baseEnd_1914760 : Nat := 655461478668689150929457

theorem tailTrace_1914760 : CollatzResearch.WordTrace tailWord_1914760 prefixEnd_1914760 655461478668689150929457 := by
  unfold tailWord_1914760
  simp only [CollatzResearch.WordTrace]
  refine ⟨34918517271579504909058867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46558023028772673212078489 34918517271579504909058867)
  ·
    refine ⟨52377775907369257363588301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34918517271579504909058867 52377775907369257363588301)
    ·
      refine ⟨19641665965263471511345613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52377775907369257363588301 19641665965263471511345613)
      ·
        refine ⟨7365624736973801816754605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19641665965263471511345613 7365624736973801816754605)
        ·
          refine ⟨2762109276365175681282977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7365624736973801816754605 2762109276365175681282977)
          ·
            refine ⟨2071581957273881760962233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2762109276365175681282977 2071581957273881760962233)
            ·
              refine ⟨1553686467955411320721675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2071581957273881760962233 1553686467955411320721675)
              ·
                refine ⟨2330529701933116981082513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1553686467955411320721675 2330529701933116981082513)
                ·
                  refine ⟨1747897276449837735811885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2330529701933116981082513 1747897276449837735811885)
                  ·
                    refine ⟨655461478668689150929457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1747897276449837735811885 655461478668689150929457)
                    ·
                      rfl

theorem cell22_1914760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 2, 1, 2, 3].length) (baseStart_1914760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1914760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1914760 prefixEnd_1914760 := by exact prefixLift 1914760
  have htrace : WordTrace (prefixWord ++ tailWord_1914760) baseStart_1914760 baseEnd_1914760 := by
    simpa [prefixWord, tailWord_1914760, baseEnd_1914760] using wordTrace_append hprefix tailTrace_1914760
  have hstable : (prefixWord ++ tailWord_1914760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914760).length < 2 ^ (prefixWord ++ tailWord_1914760).sum := by decide
  have hdescent : baseEnd_1914760 < baseStart_1914760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914801 : List Nat := [1, 2, 2, 4, 2, 2, 2, 2, 5]
def baseStart_1914801 : Nat := 118140960795 + 1914801 * 2 ^ 59
def prefixEnd_1914801 : Nat := 4983230072969 + 3 ^ 40 * 1914801 * 2
def baseEnd_1914801 : Nat := 218491837935526236884777

theorem tailTrace_1914801 : CollatzResearch.WordTrace tailWord_1914801 prefixEnd_1914801 218491837935526236884777 := by
  unfold tailWord_1914801
  simp only [CollatzResearch.WordTrace]
  refine ⟨69838529936010473820360257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46559019957340315880240171 69838529936010473820360257)
  ·
    refine ⟨52378897452007855365270193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69838529936010473820360257 52378897452007855365270193)
    ·
      refine ⟨39284173089005891523952645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52378897452007855365270193 39284173089005891523952645)
      ·
        refine ⟨7365782454188604660741121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39284173089005891523952645 7365782454188604660741121)
        ·
          refine ⟨5524336840641453495555841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7365782454188604660741121 5524336840641453495555841)
          ·
            refine ⟨4143252630481090121666881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5524336840641453495555841 4143252630481090121666881)
            ·
              refine ⟨3107439472860817591250161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4143252630481090121666881 3107439472860817591250161)
              ·
                refine ⟨2330579604645613193437621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3107439472860817591250161 2330579604645613193437621)
                ·
                  refine ⟨218491837935526236884777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2330579604645613193437621 218491837935526236884777)
                  ·
                    rfl

theorem cell22_1914801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 2, 5].length) (baseStart_1914801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1914801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1914801 prefixEnd_1914801 := by exact prefixLift 1914801
  have htrace : WordTrace (prefixWord ++ tailWord_1914801) baseStart_1914801 baseEnd_1914801 := by
    simpa [prefixWord, tailWord_1914801, baseEnd_1914801] using wordTrace_append hprefix tailTrace_1914801
  have hstable : (prefixWord ++ tailWord_1914801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914801).length < 2 ^ (prefixWord ++ tailWord_1914801).sum := by decide
  have hdescent : baseEnd_1914801 < baseStart_1914801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914805 : List Nat := [1, 3, 3, 2, 1, 2, 4, 2, 1, 3]
def baseStart_1914805 : Nat := 118140960795 + 1914805 * 2 ^ 59
def prefixEnd_1914805 : Nat := 4983230072969 + 3 ^ 40 * 1914805 * 2
def baseEnd_1914805 : Nat := 655476883088324033554319

theorem tailTrace_1914805 : CollatzResearch.WordTrace tailWord_1914805 prefixEnd_1914805 655476883088324033554319 := by
  unfold tailWord_1914805
  simp only [CollatzResearch.WordTrace]
  refine ⟨69838675827995982503505869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46559117218663988335670579 69838675827995982503505869)
  ·
    refine ⟨26189503435498493438814701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69838675827995982503505869 26189503435498493438814701)
    ·
      refine ⟨9821063788311935039555513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26189503435498493438814701 9821063788311935039555513)
      ·
        refine ⟨7365797841233951279666635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9821063788311935039555513 7365797841233951279666635)
        ·
          refine ⟨11048696761850926919499953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7365797841233951279666635 11048696761850926919499953)
          ·
            refine ⟨8286522571388195189624965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11048696761850926919499953 8286522571388195189624965)
            ·
              refine ⟨1553722982135286598054681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8286522571388195189624965 1553722982135286598054681)
              ·
                refine ⟨1165292236601464948541011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1553722982135286598054681 1165292236601464948541011)
                ·
                  refine ⟨1747938354902197422811517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1165292236601464948541011 1747938354902197422811517)
                  ·
                    refine ⟨655476883088324033554319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1747938354902197422811517 655476883088324033554319)
                    ·
                      rfl

theorem cell22_1914805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 4, 2, 1, 3].length) (baseStart_1914805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1914805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1914805 prefixEnd_1914805 := by exact prefixLift 1914805
  have htrace : WordTrace (prefixWord ++ tailWord_1914805) baseStart_1914805 baseEnd_1914805 := by
    simpa [prefixWord, tailWord_1914805, baseEnd_1914805] using wordTrace_append hprefix tailTrace_1914805
  have hstable : (prefixWord ++ tailWord_1914805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914805).length < 2 ^ (prefixWord ++ tailWord_1914805).sum := by decide
  have hdescent : baseEnd_1914805 < baseStart_1914805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914859 : List Nat := [1, 1, 1, 1, 2, 3, 1, 6, 2, 4]
def baseStart_1914859 : Nat := 118140960795 + 1914859 * 2 ^ 59
def prefixEnd_1914859 : Nat := 4983230072969 + 3 ^ 40 * 1914859 * 2
def baseEnd_1914859 : Nat := 655495368391885892704153

theorem tailTrace_1914859 : CollatzResearch.WordTrace tailWord_1914859 prefixEnd_1914859 655495368391885892704153 := by
  unfold tailWord_1914859
  simp only [CollatzResearch.WordTrace]
  refine ⟨69840645369800349725971631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46560430246533566483981087 69840645369800349725971631)
  ·
    refine ⟨104760968054700524588957447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69840645369800349725971631 104760968054700524588957447)
    ·
      refine ⟨157141452082050786883436171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104760968054700524588957447 157141452082050786883436171)
      ·
        refine ⟨235712178123076180325154257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157141452082050786883436171 235712178123076180325154257)
        ·
          refine ⟨176784133592307135243865693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235712178123076180325154257 176784133592307135243865693)
          ·
            refine ⟨66294050097115175716449635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176784133592307135243865693 66294050097115175716449635)
            ·
              refine ⟨99441075145672763574674453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66294050097115175716449635 99441075145672763574674453)
              ·
                refine ⟨4661300397453410792562865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 99441075145672763574674453 4661300397453410792562865)
                ·
                  refine ⟨3495975298090058094422149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4661300397453410792562865 3495975298090058094422149)
                  ·
                    refine ⟨655495368391885892704153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3495975298090058094422149 655495368391885892704153)
                    ·
                      rfl

theorem cell22_1914859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 6, 2, 4].length) (baseStart_1914859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1914859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1914859 prefixEnd_1914859 := by exact prefixLift 1914859
  have htrace : WordTrace (prefixWord ++ tailWord_1914859) baseStart_1914859 baseEnd_1914859 := by
    simpa [prefixWord, tailWord_1914859, baseEnd_1914859] using wordTrace_append hprefix tailTrace_1914859
  have hstable : (prefixWord ++ tailWord_1914859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914859).length < 2 ^ (prefixWord ++ tailWord_1914859).sum := by decide
  have hdescent : baseEnd_1914859 < baseStart_1914859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914878 : List Nat := [4, 2, 2, 2, 1, 1, 3, 1, 1, 5]
def baseStart_1914878 : Nat := 118140960795 + 1914878 * 2 ^ 59
def prefixEnd_1914878 : Nat := 4983230072969 + 3 ^ 40 * 1914878 * 2
def baseEnd_1914878 : Nat := 655501872480176176479095

theorem tailTrace_1914878 : CollatzResearch.WordTrace tailWord_1914878 prefixEnd_1914878 655501872480176176479095 := by
  unfold tailWord_1914878
  simp only [CollatzResearch.WordTrace]
  refine ⟨8730167294591439496364161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46560892237821010647275525 8730167294591439496364161)
  ·
    refine ⟨6547625470943579622273121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8730167294591439496364161 6547625470943579622273121)
    ·
      refine ⟨4910719103207684716704841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6547625470943579622273121 4910719103207684716704841)
      ·
        refine ⟨3683039327405763537528631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4910719103207684716704841 3683039327405763537528631)
        ·
          refine ⟨5524558991108645306292947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3683039327405763537528631 5524558991108645306292947)
          ·
            refine ⟨8286838486662967959439421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5524558991108645306292947 8286838486662967959439421)
            ·
              refine ⟨3107564432498612984789783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8286838486662967959439421 3107564432498612984789783)
              ·
                refine ⟨4661346648747919477184675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3107564432498612984789783 4661346648747919477184675)
                ·
                  refine ⟨6992019973121879215777013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4661346648747919477184675 6992019973121879215777013)
                  ·
                    refine ⟨655501872480176176479095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6992019973121879215777013 655501872480176176479095)
                    ·
                      rfl

theorem cell22_1914878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_1914878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1914878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1914878 prefixEnd_1914878 := by exact prefixLift 1914878
  have htrace : WordTrace (prefixWord ++ tailWord_1914878) baseStart_1914878 baseEnd_1914878 := by
    simpa [prefixWord, tailWord_1914878, baseEnd_1914878] using wordTrace_append hprefix tailTrace_1914878
  have hstable : (prefixWord ++ tailWord_1914878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914878).length < 2 ^ (prefixWord ++ tailWord_1914878).sum := by decide
  have hdescent : baseEnd_1914878 < baseStart_1914878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1914998 : List Nat := [5, 1, 1, 2, 1, 3, 1, 2, 6]
def baseStart_1914998 : Nat := 118140960795 + 1914998 * 2 ^ 59
def prefixEnd_1914998 : Nat := 4983230072969 + 3 ^ 40 * 1914998 * 2
def baseEnd_1914998 : Nat := 218514316977511954492909

theorem tailTrace_1914998 : CollatzResearch.WordTrace tailWord_1914998 prefixEnd_1914998 218514316977511954492909 := by
  unfold tailWord_1914998
  simp only [CollatzResearch.WordTrace]
  refine ⟨4365357194768548529080103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46563810077531184310187765 4365357194768548529080103)
  ·
    refine ⟨6548035792152822793620155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4365357194768548529080103 6548035792152822793620155)
    ·
      refine ⟨9822053688229234190430233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6548035792152822793620155 9822053688229234190430233)
      ·
        refine ⟨7366540266171925642822675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9822053688229234190430233 7366540266171925642822675)
        ·
          refine ⟨11049810399257888464234013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7366540266171925642822675 11049810399257888464234013)
          ·
            refine ⟨4143678899721708174087755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11049810399257888464234013 4143678899721708174087755)
            ·
              refine ⟨6215518349582562261131633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4143678899721708174087755 6215518349582562261131633)
              ·
                refine ⟨4661638762186921695848725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6215518349582562261131633 4661638762186921695848725)
                ·
                  refine ⟨218514316977511954492909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4661638762186921695848725 218514316977511954492909)
                  ·
                    rfl

theorem cell22_1914998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 2, 6].length) (baseStart_1914998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1914998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1914998 prefixEnd_1914998 := by exact prefixLift 1914998
  have htrace : WordTrace (prefixWord ++ tailWord_1914998) baseStart_1914998 baseEnd_1914998 := by
    simpa [prefixWord, tailWord_1914998, baseEnd_1914998] using wordTrace_append hprefix tailTrace_1914998
  have hstable : (prefixWord ++ tailWord_1914998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1914998).length < 2 ^ (prefixWord ++ tailWord_1914998).sum := by decide
  have hdescent : baseEnd_1914998 < baseStart_1914998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1914998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915011 : List Nat := [1, 1, 1, 3, 3, 4, 1, 1, 1, 6]
def baseStart_1915011 : Nat := 118140960795 + 1915011 * 2 ^ 59
def prefixEnd_1915011 : Nat := 4983230072969 + 3 ^ 40 * 1915011 * 2
def baseEnd_1915011 : Nat := 655547401098208162903687

theorem tailTrace_1915011 : CollatzResearch.WordTrace tailWord_1915011 prefixEnd_1915011 655547401098208162903687 := by
  unfold tailWord_1915011
  simp only [CollatzResearch.WordTrace]
  refine ⟨69846189265249679685504887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46564126176833119790336591 69846189265249679685504887)
  ·
    refine ⟨104769283897874519528257331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69846189265249679685504887 104769283897874519528257331)
    ·
      refine ⟨157153925846811779292385997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104769283897874519528257331 157153925846811779292385997)
      ·
        refine ⟨58932722192554417234644749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157153925846811779292385997 58932722192554417234644749)
        ·
          refine ⟨22099770822207906462991781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58932722192554417234644749 22099770822207906462991781)
          ·
            refine ⟨4143707029163982461810959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22099770822207906462991781 4143707029163982461810959)
            ·
              refine ⟨6215560543745973692716439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4143707029163982461810959 6215560543745973692716439)
              ·
                refine ⟨9323340815618960539074659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6215560543745973692716439 9323340815618960539074659)
                ·
                  refine ⟨13985011223428440808611989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9323340815618960539074659 13985011223428440808611989)
                  ·
                    refine ⟨655547401098208162903687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13985011223428440808611989 655547401098208162903687)
                    ·
                      rfl

theorem cell22_1915011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 1, 1, 6].length) (baseStart_1915011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1915011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1915011 prefixEnd_1915011 := by exact prefixLift 1915011
  have htrace : WordTrace (prefixWord ++ tailWord_1915011) baseStart_1915011 baseEnd_1915011 := by
    simpa [prefixWord, tailWord_1915011, baseEnd_1915011] using wordTrace_append hprefix tailTrace_1915011
  have hstable : (prefixWord ++ tailWord_1915011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915011).length < 2 ^ (prefixWord ++ tailWord_1915011).sum := by decide
  have hdescent : baseEnd_1915011 < baseStart_1915011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915026 : List Nat := [3, 2, 3, 1, 1, 1, 11]
def baseStart_1915026 : Nat := 118140960795 + 1915026 * 2 ^ 59
def prefixEnd_1915026 : Nat := 4983230072969 + 3 ^ 40 * 1915026 * 2
def baseEnd_1915026 : Nat := 24279723552027893473283

theorem tailTrace_1915026 : CollatzResearch.WordTrace tailWord_1915026 prefixEnd_1915026 24279723552027893473283 := by
  unfold tailWord_1915026
  simp only [CollatzResearch.WordTrace]
  refine ⟨17461684090048834311825233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46564490906796891498200621 17461684090048834311825233)
  ·
    refine ⟨13096263067536625733868925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17461684090048834311825233 13096263067536625733868925)
    ·
      refine ⟨4911098650326234650200847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13096263067536625733868925 4911098650326234650200847)
      ·
        refine ⟨7366647975489351975301271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4911098650326234650200847 7366647975489351975301271)
        ·
          refine ⟨11049971963234027962951907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7366647975489351975301271 11049971963234027962951907)
          ·
            refine ⟨16574957944851041944427861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11049971963234027962951907 16574957944851041944427861)
            ·
              refine ⟨24279723552027893473283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 16574957944851041944427861 24279723552027893473283)
              ·
                rfl

theorem cell22_1915026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 11].length) (baseStart_1915026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1915026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1915026 prefixEnd_1915026 := by exact prefixLift 1915026
  have htrace : WordTrace (prefixWord ++ tailWord_1915026) baseStart_1915026 baseEnd_1915026 := by
    simpa [prefixWord, tailWord_1915026, baseEnd_1915026] using wordTrace_append hprefix tailTrace_1915026
  have hstable : (prefixWord ++ tailWord_1915026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915026).length < 2 ^ (prefixWord ++ tailWord_1915026).sum := by decide
  have hdescent : baseEnd_1915026 < baseStart_1915026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915047 : List Nat := [1, 1, 6, 2, 3, 1, 1, 1, 1, 5]
def baseStart_1915047 : Nat := 118140960795 + 1915047 * 2 ^ 59
def prefixEnd_1915047 : Nat := 4983230072969 + 3 ^ 40 * 1915047 * 2
def baseEnd_1915047 : Nat := 655559724633916069003577

theorem tailTrace_1915047 : CollatzResearch.WordTrace tailWord_1915047 prefixEnd_1915047 655559724633916069003577 := by
  unfold tailWord_1915047
  simp only [CollatzResearch.WordTrace]
  refine ⟨69847502293119257833815395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46565001528746171889210263 69847502293119257833815395)
  ·
    refine ⟨104771253439678886750723093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69847502293119257833815395 104771253439678886750723093)
    ·
      refine ⟨4911152504984947816440145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 104771253439678886750723093 4911152504984947816440145)
      ·
        refine ⟨3683364378738710862330109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4911152504984947816440145 3683364378738710862330109)
        ·
          refine ⟨1381261642027016573373791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3683364378738710862330109 1381261642027016573373791)
          ·
            refine ⟨2071892463040524860060687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1381261642027016573373791 2071892463040524860060687)
            ·
              refine ⟨3107838694560787290091031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2071892463040524860060687 3107838694560787290091031)
              ·
                refine ⟨4661758041841180935136547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3107838694560787290091031 4661758041841180935136547)
                ·
                  refine ⟨6992637062761771402704821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4661758041841180935136547 6992637062761771402704821)
                  ·
                    refine ⟨655559724633916069003577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6992637062761771402704821 655559724633916069003577)
                    ·
                      rfl

theorem cell22_1915047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_1915047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1915047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1915047 prefixEnd_1915047 := by exact prefixLift 1915047
  have htrace : WordTrace (prefixWord ++ tailWord_1915047) baseStart_1915047 baseEnd_1915047 := by
    simpa [prefixWord, tailWord_1915047, baseEnd_1915047] using wordTrace_append hprefix tailTrace_1915047
  have hstable : (prefixWord ++ tailWord_1915047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915047).length < 2 ^ (prefixWord ++ tailWord_1915047).sum := by decide
  have hdescent : baseEnd_1915047 < baseStart_1915047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915058 : List Nat := [3, 2, 1, 1, 1, 3, 1, 4, 3, 3]
def baseStart_1915058 : Nat := 118140960795 + 1915058 * 2 ^ 59
def prefixEnd_1915058 : Nat := 4983230072969 + 3 ^ 40 * 1915058 * 2
def baseEnd_1915058 : Nat := 655563490158715706978543

theorem tailTrace_1915058 : CollatzResearch.WordTrace tailWord_1915058 prefixEnd_1915058 655563490158715706978543 := by
  unfold tailWord_1915058
  simp only [CollatzResearch.WordTrace]
  refine ⟨17461975874019851678116457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46565268997386271141643885 17461975874019851678116457)
  ·
    refine ⟨13096481905514888758587343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17461975874019851678116457 13096481905514888758587343)
    ·
      refine ⟨19644722858272333137881015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13096481905514888758587343 19644722858272333137881015)
      ·
        refine ⟨29467084287408499706821523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19644722858272333137881015 29467084287408499706821523)
        ·
          refine ⟨44200626431112749560232285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29467084287408499706821523 44200626431112749560232285)
          ·
            refine ⟨16575234911667281085087107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44200626431112749560232285 16575234911667281085087107)
            ·
              refine ⟨24862852367500921627630661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16575234911667281085087107 24862852367500921627630661)
              ·
                refine ⟨4661784818906422805180749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24862852367500921627630661 4661784818906422805180749)
                ·
                  refine ⟨1748169307089908551942781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4661784818906422805180749 1748169307089908551942781)
                  ·
                    refine ⟨655563490158715706978543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1748169307089908551942781 655563490158715706978543)
                    ·
                      rfl

theorem cell22_1915058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 4, 3, 3].length) (baseStart_1915058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1915058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1915058 prefixEnd_1915058 := by exact prefixLift 1915058
  have htrace : WordTrace (prefixWord ++ tailWord_1915058) baseStart_1915058 baseEnd_1915058 := by
    simpa [prefixWord, tailWord_1915058, baseEnd_1915058] using wordTrace_append hprefix tailTrace_1915058
  have hstable : (prefixWord ++ tailWord_1915058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915058).length < 2 ^ (prefixWord ++ tailWord_1915058).sum := by decide
  have hdescent : baseEnd_1915058 < baseStart_1915058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915116 : List Nat := [2, 2, 1, 1, 2, 3, 2, 1, 8]
def baseStart_1915116 : Nat := 118140960795 + 1915116 * 2 ^ 59
def prefixEnd_1915116 : Nat := 4983230072969 + 3 ^ 40 * 1915116 * 2
def baseEnd_1915116 : Nat := 218527781581340963009455

theorem tailTrace_1915116 : CollatzResearch.WordTrace tailWord_1915116 prefixEnd_1915116 218527781581340963009455 := by
  unfold tailWord_1915116
  simp only [CollatzResearch.WordTrace]
  refine ⟨34925009464934641309038601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46566679286579521745384801 34925009464934641309038601)
  ·
    refine ⟨26193757098700980981778951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34925009464934641309038601 26193757098700980981778951)
    ·
      refine ⟨39290635648051471472668427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26193757098700980981778951 39290635648051471472668427)
      ·
        refine ⟨58935953472077207209002641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39290635648051471472668427 58935953472077207209002641)
        ·
          refine ⟨44201965104057905406751981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58935953472077207209002641 44201965104057905406751981)
          ·
            refine ⟨16575736914021714527531993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44201965104057905406751981 16575736914021714527531993)
            ·
              refine ⟨12431802685516285895648995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16575736914021714527531993 12431802685516285895648995)
              ·
                refine ⟨18647704028274428843473493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12431802685516285895648995 18647704028274428843473493)
                ·
                  refine ⟨218527781581340963009455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18647704028274428843473493 218527781581340963009455)
                  ·
                    rfl

theorem cell22_1915116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 8].length) (baseStart_1915116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1915116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1915116 prefixEnd_1915116 := by exact prefixLift 1915116
  have htrace : WordTrace (prefixWord ++ tailWord_1915116) baseStart_1915116 baseEnd_1915116 := by
    simpa [prefixWord, tailWord_1915116, baseEnd_1915116] using wordTrace_append hprefix tailTrace_1915116
  have hstable : (prefixWord ++ tailWord_1915116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915116).length < 2 ^ (prefixWord ++ tailWord_1915116).sum := by decide
  have hdescent : baseEnd_1915116 < baseStart_1915116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915135 : List Nat := [1, 1, 2, 2, 1, 4, 5, 1, 1, 4]
def baseStart_1915135 : Nat := 118140960795 + 1915135 * 2 ^ 59
def prefixEnd_1915135 : Nat := 4983230072969 + 3 ^ 40 * 1915135 * 2
def baseEnd_1915135 : Nat := 655589848832313172803307

theorem tailTrace_1915135 : CollatzResearch.WordTrace tailWord_1915135 prefixEnd_1915135 655589848832313172803307 := by
  unfold tailWord_1915135
  simp only [CollatzResearch.WordTrace]
  refine ⟨69850711916800448863018859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46567141277866965908679239 69850711916800448863018859)
  ·
    refine ⟨104776067875200673294528289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69850711916800448863018859 104776067875200673294528289)
    ·
      refine ⟨78582050906400504970896217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104776067875200673294528289 78582050906400504970896217)
      ·
        refine ⟨58936538179800378728172163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78582050906400504970896217 58936538179800378728172163)
        ·
          refine ⟨88404807269700568092258245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58936538179800378728172163 88404807269700568092258245)
          ·
            refine ⟨16575901363068856517298421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88404807269700568092258245 16575901363068856517298421)
            ·
              refine ⟨1553990752787705298496727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16575901363068856517298421 1553990752787705298496727)
              ·
                refine ⟨2330986129181557947745091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1553990752787705298496727 2330986129181557947745091)
                ·
                  refine ⟨3496479193772336921617637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2330986129181557947745091 3496479193772336921617637)
                  ·
                    refine ⟨655589848832313172803307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3496479193772336921617637 655589848832313172803307)
                    ·
                      rfl

theorem cell22_1915135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 5, 1, 1, 4].length) (baseStart_1915135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1915135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1915135 prefixEnd_1915135 := by exact prefixLift 1915135
  have htrace : WordTrace (prefixWord ++ tailWord_1915135) baseStart_1915135 baseEnd_1915135 := by
    simpa [prefixWord, tailWord_1915135, baseEnd_1915135] using wordTrace_append hprefix tailTrace_1915135
  have hstable : (prefixWord ++ tailWord_1915135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915135).length < 2 ^ (prefixWord ++ tailWord_1915135).sum := by decide
  have hdescent : baseEnd_1915135 < baseStart_1915135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915143 : List Nat := [1, 1, 4, 5, 2, 1, 2, 2, 1, 3]
def baseStart_1915143 : Nat := 118140960795 + 1915143 * 2 ^ 59
def prefixEnd_1915143 : Nat := 4983230072969 + 3 ^ 40 * 1915143 * 2
def baseEnd_1915143 : Nat := 655592587395803818603283

theorem tailTrace_1915143 : CollatzResearch.WordTrace tailWord_1915143 prefixEnd_1915143 655592587395803818603283 := by
  unfold tailWord_1915143
  simp only [CollatzResearch.WordTrace]
  refine ⟨69851003700771466229310083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46567335800514310819540055 69851003700771466229310083)
  ·
    refine ⟨104776505551157199343965125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69851003700771466229310083 104776505551157199343965125)
    ·
      refine ⟨19645594790841974876993461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104776505551157199343965125 19645594790841974876993461)
      ·
        refine ⟨1841774511641435144718137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19645594790841974876993461 1841774511641435144718137)
        ·
          refine ⟨1381330883731076358538603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1841774511641435144718137 1381330883731076358538603)
          ·
            refine ⟨2071996325596614537807905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1381330883731076358538603 2071996325596614537807905)
            ·
              refine ⟨1553997244197460903355929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2071996325596614537807905 1553997244197460903355929)
              ·
                refine ⟨1165497933148095677516947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1553997244197460903355929 1165497933148095677516947)
                ·
                  refine ⟨1748246899722143516275421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1165497933148095677516947 1748246899722143516275421)
                  ·
                    refine ⟨655592587395803818603283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1748246899722143516275421 655592587395803818603283)
                    ·
                      rfl

theorem cell22_1915143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 2, 2, 1, 3].length) (baseStart_1915143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1915143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1915143 prefixEnd_1915143 := by exact prefixLift 1915143
  have htrace : WordTrace (prefixWord ++ tailWord_1915143) baseStart_1915143 baseEnd_1915143 := by
    simpa [prefixWord, tailWord_1915143, baseEnd_1915143] using wordTrace_append hprefix tailTrace_1915143
  have hstable : (prefixWord ++ tailWord_1915143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915143).length < 2 ^ (prefixWord ++ tailWord_1915143).sum := by decide
  have hdescent : baseEnd_1915143 < baseStart_1915143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915150 : List Nat := [4, 1, 1, 2, 1, 2, 3, 4, 4]
def baseStart_1915150 : Nat := 118140960795 + 1915150 * 2 ^ 59
def prefixEnd_1915150 : Nat := 4983230072969 + 3 ^ 40 * 1915150 * 2
def baseEnd_1915150 : Nat := 218531661212952711226087

theorem tailTrace_1915150 : CollatzResearch.WordTrace tailWord_1915150 prefixEnd_1915150 218531661212952711226087 := by
  unfold tailWord_1915150
  simp only [CollatzResearch.WordTrace]
  refine ⟨8731407376468263303101863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46567506007830737616543269 8731407376468263303101863)
  ·
    refine ⟨13097111064702394954652795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8731407376468263303101863 13097111064702394954652795)
    ·
      refine ⟨19645666597053592431979193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13097111064702394954652795 19645666597053592431979193)
      ·
        refine ⟨14734249947790194323984395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19645666597053592431979193 14734249947790194323984395)
        ·
          refine ⟨22101374921685291485976593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14734249947790194323984395 22101374921685291485976593)
          ·
            refine ⟨16576031191263968614482445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22101374921685291485976593 16576031191263968614482445)
            ·
              refine ⟨6216011696723988230430917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16576031191263968614482445 6216011696723988230430917)
              ·
                refine ⟨1165502193135747793205797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6216011696723988230430917 1165502193135747793205797)
                ·
                  refine ⟨218531661212952711226087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1165502193135747793205797 218531661212952711226087)
                  ·
                    rfl

theorem cell22_1915150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 4, 4].length) (baseStart_1915150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1915150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1915150 prefixEnd_1915150 := by exact prefixLift 1915150
  have htrace : WordTrace (prefixWord ++ tailWord_1915150) baseStart_1915150 baseEnd_1915150 := by
    simpa [prefixWord, tailWord_1915150, baseEnd_1915150] using wordTrace_append hprefix tailTrace_1915150
  have hstable : (prefixWord ++ tailWord_1915150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915150).length < 2 ^ (prefixWord ++ tailWord_1915150).sum := by decide
  have hdescent : baseEnd_1915150 < baseStart_1915150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915300 : List Nat := [2, 3, 1, 2, 1, 1, 2, 1, 6, 3]
def baseStart_1915300 : Nat := 118140960795 + 1915300 * 2 ^ 59
def prefixEnd_1915300 : Nat := 4983230072969 + 3 ^ 40 * 1915300 * 2
def baseEnd_1915300 : Nat := 655646331704307742427801

theorem tailTrace_1915300 : CollatzResearch.WordTrace tailWord_1915300 prefixEnd_1915300 655646331704307742427801 := by
  unfold tailWord_1915300
  simp only [CollatzResearch.WordTrace]
  refine ⟨34928364980601341021387677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46571153307468454695183569 34928364980601341021387677)
  ·
    refine ⟨13098136867725502883020379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34928364980601341021387677 13098136867725502883020379)
    ·
      refine ⟨19647205301588254324530569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13098136867725502883020379 19647205301588254324530569)
      ·
        refine ⟨14735403976191190743397927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19647205301588254324530569 14735403976191190743397927)
        ·
          refine ⟨22103105964286786115096891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14735403976191190743397927 22103105964286786115096891)
          ·
            refine ⟨33154658946430179172645337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22103105964286786115096891 33154658946430179172645337)
            ·
              refine ⟨24865994209822634379484003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33154658946430179172645337 24865994209822634379484003)
              ·
                refine ⟨37298991314733951569226005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24865994209822634379484003 37298991314733951569226005)
                ·
                  refine ⟨1748390217878153979807469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 37298991314733951569226005 1748390217878153979807469)
                  ·
                    refine ⟨655646331704307742427801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1748390217878153979807469 655646331704307742427801)
                    ·
                      rfl

theorem cell22_1915300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 6, 3].length) (baseStart_1915300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1915300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1915300 prefixEnd_1915300 := by exact prefixLift 1915300
  have htrace : WordTrace (prefixWord ++ tailWord_1915300) baseStart_1915300 baseEnd_1915300 := by
    simpa [prefixWord, tailWord_1915300, baseEnd_1915300] using wordTrace_append hprefix tailTrace_1915300
  have hstable : (prefixWord ++ tailWord_1915300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915300).length < 2 ^ (prefixWord ++ tailWord_1915300).sum := by decide
  have hdescent : baseEnd_1915300 < baseStart_1915300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915313 : List Nat := [1, 2, 2, 4, 1, 12]
def baseStart_1915313 : Nat := 118140960795 + 1915313 * 2 ^ 59
def prefixEnd_1915313 : Nat := 4983230072969 + 3 ^ 40 * 1915313 * 2
def baseEnd_1915313 : Nat := 8094454097160247430281

theorem tailTrace_1915313 : CollatzResearch.WordTrace tailWord_1915313 prefixEnd_1915313 8094454097160247430281 := by
  unfold tailWord_1915313
  simp only [CollatzResearch.WordTrace]
  refine ⟨69857204110155585262998593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46571469406770390175332395 69857204110155585262998593)
  ·
    refine ⟨52392903082616688947248945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69857204110155585262998593 52392903082616688947248945)
    ·
      refine ⟨39294677311962516710436709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52392903082616688947248945 39294677311962516710436709)
      ·
        refine ⟨7367751995992971883206883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39294677311962516710436709 7367751995992971883206883)
        ·
          refine ⟨11051627993989457824810325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7367751995992971883206883 11051627993989457824810325)
          ·
            refine ⟨8094454097160247430281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 11051627993989457824810325 8094454097160247430281)
            ·
              rfl

theorem cell22_1915313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 12].length) (baseStart_1915313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1915313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1915313 prefixEnd_1915313 := by exact prefixLift 1915313
  have htrace : WordTrace (prefixWord ++ tailWord_1915313) baseStart_1915313 baseEnd_1915313 := by
    simpa [prefixWord, tailWord_1915313, baseEnd_1915313] using wordTrace_append hprefix tailTrace_1915313
  have hstable : (prefixWord ++ tailWord_1915313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915313).length < 2 ^ (prefixWord ++ tailWord_1915313).sum := by decide
  have hdescent : baseEnd_1915313 < baseStart_1915313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915319 : List Nat := [1, 1, 3, 1, 3, 5, 2, 2, 4]
def baseStart_1915319 : Nat := 118140960795 + 1915319 * 2 ^ 59
def prefixEnd_1915319 : Nat := 4983230072969 + 3 ^ 40 * 1915319 * 2
def baseEnd_1915319 : Nat := 218550945264199342067581

theorem tailTrace_1915319 : CollatzResearch.WordTrace tailWord_1915319 prefixEnd_1915319 218550945264199342067581 := by
  unfold tailWord_1915319
  simp only [CollatzResearch.WordTrace]
  refine ⟨69857422948133848287717011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46571615298755898858478007 69857422948133848287717011)
  ·
    refine ⟨104786134422200772431575517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69857422948133848287717011 104786134422200772431575517)
    ·
      refine ⟨39294800408325289661840819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104786134422200772431575517 39294800408325289661840819)
      ·
        refine ⟨58942200612487934492761229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39294800408325289661840819 58942200612487934492761229)
        ·
          refine ⟨22103325229682975434785461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58942200612487934492761229 22103325229682975434785461)
          ·
            refine ⟨2072186740282778947011137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22103325229682975434785461 2072186740282778947011137)
            ·
              refine ⟨1554140055212084210258353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2072186740282778947011137 1554140055212084210258353)
              ·
                refine ⟨1165605041409063157693765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1554140055212084210258353 1165605041409063157693765)
                ·
                  refine ⟨218550945264199342067581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1165605041409063157693765 218550945264199342067581)
                  ·
                    rfl

theorem cell22_1915319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 2, 2, 4].length) (baseStart_1915319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1915319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1915319 prefixEnd_1915319 := by exact prefixLift 1915319
  have htrace : WordTrace (prefixWord ++ tailWord_1915319) baseStart_1915319 baseEnd_1915319 := by
    simpa [prefixWord, tailWord_1915319, baseEnd_1915319] using wordTrace_append hprefix tailTrace_1915319
  have hstable : (prefixWord ++ tailWord_1915319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915319).length < 2 ^ (prefixWord ++ tailWord_1915319).sum := by decide
  have hdescent : baseEnd_1915319 < baseStart_1915319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915328 : List Nat := [2, 1, 1, 2, 3, 1, 1, 2, 2, 7]
def baseStart_1915328 : Nat := 118140960795 + 1915328 * 2 ^ 59
def prefixEnd_1915328 : Nat := 4983230072969 + 3 ^ 40 * 1915328 * 2
def baseEnd_1915328 : Nat := 655655916676525002727715

theorem tailTrace_1915328 : CollatzResearch.WordTrace tailWord_1915328 prefixEnd_1915328 655655916676525002727715 := by
  unfold tailWord_1915328
  simp only [CollatzResearch.WordTrace]
  refine ⟨34928875602550621412397319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46571834136734161883196425 34928875602550621412397319)
  ·
    refine ⟨52393313403825932118595979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34928875602550621412397319 52393313403825932118595979)
    ·
      refine ⟨78589970105738898177893969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52393313403825932118595979 78589970105738898177893969)
      ·
        refine ⟨58942477579304173633420477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78589970105738898177893969 58942477579304173633420477)
        ·
          refine ⟨22103429092239065112532679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58942477579304173633420477 22103429092239065112532679)
          ·
            refine ⟨33155143638358597668799019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22103429092239065112532679 33155143638358597668799019)
            ·
              refine ⟨49732715457537896503198529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33155143638358597668799019 49732715457537896503198529)
              ·
                refine ⟨37299536593153422377398897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49732715457537896503198529 37299536593153422377398897)
                ·
                  refine ⟨27974652444865066783049173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37299536593153422377398897 27974652444865066783049173)
                  ·
                    refine ⟨655655916676525002727715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27974652444865066783049173 655655916676525002727715)
                    ·
                      rfl

theorem cell22_1915328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 2, 7].length) (baseStart_1915328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1915328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1915328 prefixEnd_1915328 := by exact prefixLift 1915328
  have htrace : WordTrace (prefixWord ++ tailWord_1915328) baseStart_1915328 baseEnd_1915328 := by
    simpa [prefixWord, tailWord_1915328, baseEnd_1915328] using wordTrace_append hprefix tailTrace_1915328
  have hstable : (prefixWord ++ tailWord_1915328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915328).length < 2 ^ (prefixWord ++ tailWord_1915328).sum := by decide
  have hdescent : baseEnd_1915328 < baseStart_1915328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915343 : List Nat := [1, 1, 2, 1, 1, 4, 1, 1, 4, 6]
def baseStart_1915343 : Nat := 118140960795 + 1915343 * 2 ^ 59
def prefixEnd_1915343 : Nat := 4983230072969 + 3 ^ 40 * 1915343 * 2
def baseEnd_1915343 : Nat := 655661051483069963602669

theorem tailTrace_1915343 : CollatzResearch.WordTrace tailWord_1915343 prefixEnd_1915343 655661051483069963602669 := by
  unfold tailWord_1915343
  simp only [CollatzResearch.WordTrace]
  refine ⟨69858298300046900386590683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46572198866697933591060455 69858298300046900386590683)
  ·
    refine ⟨104787447450070350579886025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69858298300046900386590683 104787447450070350579886025)
    ·
      refine ⟨78590585587552762934914519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104787447450070350579886025 78590585587552762934914519)
      ·
        refine ⟨117885878381329144402371779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78590585587552762934914519 117885878381329144402371779)
        ·
          refine ⟨176828817571993716603557669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117885878381329144402371779 176828817571993716603557669)
          ·
            refine ⟨33155403294748821863167063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 176828817571993716603557669 33155403294748821863167063)
            ·
              refine ⟨49733104942123232794750595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33155403294748821863167063 49733104942123232794750595)
              ·
                refine ⟨74599657413184849192125893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49733104942123232794750595 74599657413184849192125893)
                ·
                  refine ⟨13987435764972159223523605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74599657413184849192125893 13987435764972159223523605)
                  ·
                    refine ⟨655661051483069963602669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13987435764972159223523605 655661051483069963602669)
                    ·
                      rfl

theorem cell22_1915343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4, 6].length) (baseStart_1915343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1915343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1915343 prefixEnd_1915343 := by exact prefixLift 1915343
  have htrace : WordTrace (prefixWord ++ tailWord_1915343) baseStart_1915343 baseEnd_1915343 := by
    simpa [prefixWord, tailWord_1915343, baseEnd_1915343] using wordTrace_append hprefix tailTrace_1915343
  have hstable : (prefixWord ++ tailWord_1915343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915343).length < 2 ^ (prefixWord ++ tailWord_1915343).sum := by decide
  have hdescent : baseEnd_1915343 < baseStart_1915343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915398 : List Nat := [6, 2, 1, 1, 1, 3, 2, 6]
def baseStart_1915398 : Nat := 118140960795 + 1915398 * 2 ^ 59
def prefixEnd_1915398 : Nat := 4983230072969 + 3 ^ 40 * 1915398 * 2
def baseEnd_1915398 : Nat := 72853319900785350386389

theorem tailTrace_1915398 : CollatzResearch.WordTrace tailWord_1915398 prefixEnd_1915398 72853319900785350386389 := by
  unfold tailWord_1915398
  simp only [CollatzResearch.WordTrace]
  refine ⟨2183134509838988899370089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 46573536209898429853228565 2183134509838988899370089)
  ·
    refine ⟨1637350882379241674527567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2183134509838988899370089 1637350882379241674527567)
    ·
      refine ⟨2456026323568862511791351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1637350882379241674527567 2456026323568862511791351)
      ·
        refine ⟨3684039485353293767687027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2456026323568862511791351 3684039485353293767687027)
        ·
          refine ⟨5526059228029940651530541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3684039485353293767687027 5526059228029940651530541)
          ·
            refine ⟨2072272210511227744323953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5526059228029940651530541 2072272210511227744323953)
            ·
              refine ⟨1554204157883420808242965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2072272210511227744323953 1554204157883420808242965)
              ·
                refine ⟨72853319900785350386389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1554204157883420808242965 72853319900785350386389)
                ·
                  rfl

theorem cell22_1915398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 2, 6].length) (baseStart_1915398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1915398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1915398 prefixEnd_1915398 := by exact prefixLift 1915398
  have htrace : WordTrace (prefixWord ++ tailWord_1915398) baseStart_1915398 baseEnd_1915398 := by
    simpa [prefixWord, tailWord_1915398, baseEnd_1915398] using wordTrace_append hprefix tailTrace_1915398
  have hstable : (prefixWord ++ tailWord_1915398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915398).length < 2 ^ (prefixWord ++ tailWord_1915398).sum := by decide
  have hdescent : baseEnd_1915398 < baseStart_1915398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915469 : List Nat := [1, 6, 1, 1, 2, 2, 1, 2, 1, 5]
def baseStart_1915469 : Nat := 118140960795 + 1915469 * 2 ^ 59
def prefixEnd_1915469 : Nat := 4983230072969 + 3 ^ 40 * 1915469 * 2
def baseEnd_1915469 : Nat := 655704183858047634952283

theorem tailTrace_1915469 : CollatzResearch.WordTrace tailWord_1915469 prefixEnd_1915469 655704183858047634952283 := by
  unfold tailWord_1915469
  simp only [CollatzResearch.WordTrace]
  refine ⟨69862893897590423905677461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46575262598393615937118307 69862893897590423905677461)
  ·
    refine ⟨3274823151449551120578631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 69862893897590423905677461 3274823151449551120578631)
    ·
      refine ⟨4912234727174326680867947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3274823151449551120578631 4912234727174326680867947)
      ·
        refine ⟨7368352090761490021301921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4912234727174326680867947 7368352090761490021301921)
        ·
          refine ⟨5526264068071117515976441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7368352090761490021301921 5526264068071117515976441)
          ·
            refine ⟨4144698051053338136982331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5526264068071117515976441 4144698051053338136982331)
            ·
              refine ⟨6217047076580007205473497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4144698051053338136982331 6217047076580007205473497)
              ·
                refine ⟨4662785307435005404105123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6217047076580007205473497 4662785307435005404105123)
                ·
                  refine ⟨6994177961152508106157685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4662785307435005404105123 6994177961152508106157685)
                  ·
                    refine ⟨655704183858047634952283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6994177961152508106157685 655704183858047634952283)
                    ·
                      rfl

theorem cell22_1915469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_1915469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1915469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1915469 prefixEnd_1915469 := by exact prefixLift 1915469
  have htrace : WordTrace (prefixWord ++ tailWord_1915469) baseStart_1915469 baseEnd_1915469 := by
    simpa [prefixWord, tailWord_1915469, baseEnd_1915469] using wordTrace_append hprefix tailTrace_1915469
  have hstable : (prefixWord ++ tailWord_1915469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915469).length < 2 ^ (prefixWord ++ tailWord_1915469).sum := by decide
  have hdescent : baseEnd_1915469 < baseStart_1915469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915497 : List Nat := [1, 2, 1, 1, 1, 4, 1, 5, 3, 3]
def baseStart_1915497 : Nat := 118140960795 + 1915497 * 2 ^ 59
def prefixEnd_1915497 : Nat := 4983230072969 + 3 ^ 40 * 1915497 * 2
def baseEnd_1915497 : Nat := 655713768830264895252197

theorem tailTrace_1915497 : CollatzResearch.WordTrace tailWord_1915497 prefixEnd_1915497 655713768830264895252197 := by
  unfold tailWord_1915497
  simp only [CollatzResearch.WordTrace]
  refine ⟨69863915141488984687696745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46575943427659323125131163 69863915141488984687696745)
  ·
    refine ⟨52397936356116738515772559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69863915141488984687696745 52397936356116738515772559)
    ·
      refine ⟨78596904534175107773658839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52397936356116738515772559 78596904534175107773658839)
      ·
        refine ⟨117895356801262661660488259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78596904534175107773658839 117895356801262661660488259)
        ·
          refine ⟨176843035201893992490732389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117895356801262661660488259 176843035201893992490732389)
          ·
            refine ⟨33158069100355123592012323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 176843035201893992490732389 33158069100355123592012323)
            ·
              refine ⟨49737103650532685388018485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33158069100355123592012323 49737103650532685388018485)
              ·
                refine ⟨4662853467237439255126733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49737103650532685388018485 4662853467237439255126733)
                ·
                  refine ⟨1748570050214039720672525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4662853467237439255126733 1748570050214039720672525)
                  ·
                    refine ⟨655713768830264895252197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1748570050214039720672525 655713768830264895252197)
                    ·
                      rfl

theorem cell22_1915497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 5, 3, 3].length) (baseStart_1915497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1915497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1915497 prefixEnd_1915497 := by exact prefixLift 1915497
  have htrace : WordTrace (prefixWord ++ tailWord_1915497) baseStart_1915497 baseEnd_1915497 := by
    simpa [prefixWord, tailWord_1915497, baseEnd_1915497] using wordTrace_append hprefix tailTrace_1915497
  have hstable : (prefixWord ++ tailWord_1915497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915497).length < 2 ^ (prefixWord ++ tailWord_1915497).sum := by decide
  have hdescent : baseEnd_1915497 < baseStart_1915497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915617 : List Nat := [1, 2, 3, 1, 4, 1, 1, 9]
def baseStart_1915617 : Nat := 118140960795 + 1915617 * 2 ^ 59
def prefixEnd_1915617 : Nat := 4983230072969 + 3 ^ 40 * 1915617 * 2
def baseEnd_1915617 : Nat := 72861649698069398027981

theorem tailTrace_1915617 : CollatzResearch.WordTrace tailWord_1915617 prefixEnd_1915617 72861649698069398027981 := by
  unfold tailWord_1915617
  simp only [CollatzResearch.WordTrace]
  refine ⟨69868291901054245182065105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46578861267369496788043403 69868291901054245182065105)
  ·
    refine ⟨52401218925790683886548829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69868291901054245182065105 52401218925790683886548829)
    ·
      refine ⟨19650457097171506457455811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52401218925790683886548829 19650457097171506457455811)
      ·
        refine ⟨29475685645757259686183717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19650457097171506457455811 29475685645757259686183717)
        ·
          refine ⟨5526691058579486191159447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29475685645757259686183717 5526691058579486191159447)
          ·
            refine ⟨8290036587869229286739171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5526691058579486191159447 8290036587869229286739171)
            ·
              refine ⟨12435054881803843930108757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8290036587869229286739171 12435054881803843930108757)
              ·
                refine ⟨72861649698069398027981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12435054881803843930108757 72861649698069398027981)
                ·
                  rfl

theorem cell22_1915617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 9].length) (baseStart_1915617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1915617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1915617 prefixEnd_1915617 := by exact prefixLift 1915617
  have htrace : WordTrace (prefixWord ++ tailWord_1915617) baseStart_1915617 baseEnd_1915617 := by
    simpa [prefixWord, tailWord_1915617, baseEnd_1915617] using wordTrace_append hprefix tailTrace_1915617
  have hstable : (prefixWord ++ tailWord_1915617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915617).length < 2 ^ (prefixWord ++ tailWord_1915617).sum := by decide
  have hdescent : baseEnd_1915617 < baseStart_1915617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915621 : List Nat := [1, 3, 1, 4, 1, 3, 1, 3, 2, 3]
def baseStart_1915621 : Nat := 118140960795 + 1915621 * 2 ^ 59
def prefixEnd_1915621 : Nat := 4983230072969 + 3 ^ 40 * 1915621 * 2
def baseEnd_1915621 : Nat := 655756216564369905151817

theorem tailTrace_1915621 : CollatzResearch.WordTrace tailWord_1915621 prefixEnd_1915621 655756216564369905151817 := by
  unfold tailWord_1915621
  simp only [CollatzResearch.WordTrace]
  refine ⟨69868437793039753865210717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46578958528693169243473811 69868437793039753865210717)
  ·
    refine ⟨26200664172389907699454019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69868437793039753865210717 26200664172389907699454019)
    ·
      refine ⟨39300996258584861549181029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26200664172389907699454019 39300996258584861549181029)
      ·
        refine ⟨7368936798484661540471443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39300996258584861549181029 7368936798484661540471443)
        ·
          refine ⟨11053405197726992310707165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7368936798484661540471443 11053405197726992310707165)
          ·
            refine ⟨4145026949147622116515187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11053405197726992310707165 4145026949147622116515187)
            ·
              refine ⟨6217540423721433174772781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4145026949147622116515187 6217540423721433174772781)
              ·
                refine ⟨2331577658895537440539793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6217540423721433174772781 2331577658895537440539793)
                ·
                  refine ⟨1748683244171653080404845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2331577658895537440539793 1748683244171653080404845)
                  ·
                    refine ⟨655756216564369905151817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1748683244171653080404845 655756216564369905151817)
                    ·
                      rfl

theorem cell22_1915621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 3, 2, 3].length) (baseStart_1915621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1915621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1915621 prefixEnd_1915621 := by exact prefixLift 1915621
  have htrace : WordTrace (prefixWord ++ tailWord_1915621) baseStart_1915621 baseEnd_1915621 := by
    simpa [prefixWord, tailWord_1915621, baseEnd_1915621] using wordTrace_append hprefix tailTrace_1915621
  have hstable : (prefixWord ++ tailWord_1915621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915621).length < 2 ^ (prefixWord ++ tailWord_1915621).sum := by decide
  have hdescent : baseEnd_1915621 < baseStart_1915621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915679 : List Nat := [1, 1, 2, 4, 2, 2, 2, 3, 5]
def baseStart_1915679 : Nat := 118140960795 + 1915679 * 2 ^ 59
def prefixEnd_1915679 : Nat := 4983230072969 + 3 ^ 40 * 1915679 * 2
def baseEnd_1915679 : Nat := 218592023716559029067213

theorem tailTrace_1915679 : CollatzResearch.WordTrace tailWord_1915679 prefixEnd_1915679 218592023716559029067213 := by
  unfold tailWord_1915679
  simp only [CollatzResearch.WordTrace]
  refine ⟨69870553226829629770822091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46580368817886419847214727 69870553226829629770822091)
  ·
    refine ⟨104805829840244444656233137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69870553226829629770822091 104805829840244444656233137)
    ·
      refine ⟨78604372380183333492174853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104805829840244444656233137 78604372380183333492174853)
      ·
        refine ⟨14738319821284375029782785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78604372380183333492174853 14738319821284375029782785)
        ·
          refine ⟨11053739865963281272337089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14738319821284375029782785 11053739865963281272337089)
          ·
            refine ⟨8290304899472460954252817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11053739865963281272337089 8290304899472460954252817)
            ·
              refine ⟨6217728674604345715689613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8290304899472460954252817 6217728674604345715689613)
              ·
                refine ⟨2331648252976629643383605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6217728674604345715689613 2331648252976629643383605)
                ·
                  refine ⟨218592023716559029067213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2331648252976629643383605 218592023716559029067213)
                  ·
                    rfl

theorem cell22_1915679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 3, 5].length) (baseStart_1915679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1915679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1915679 prefixEnd_1915679 := by exact prefixLift 1915679
  have htrace : WordTrace (prefixWord ++ tailWord_1915679) baseStart_1915679 baseEnd_1915679 := by
    simpa [prefixWord, tailWord_1915679, baseEnd_1915679] using wordTrace_append hprefix tailTrace_1915679
  have hstable : (prefixWord ++ tailWord_1915679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915679).length < 2 ^ (prefixWord ++ tailWord_1915679).sum := by decide
  have hdescent : baseEnd_1915679 < baseStart_1915679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915724 : List Nat := [2, 2, 1, 3, 3, 1, 1, 3, 6]
def baseStart_1915724 : Nat := 118140960795 + 1915724 * 2 ^ 59
def prefixEnd_1915724 : Nat := 4983230072969 + 3 ^ 40 * 1915724 * 2
def baseEnd_1915724 : Nat := 218597158523103989942167

theorem tailTrace_1915724 : CollatzResearch.WordTrace tailWord_1915724 prefixEnd_1915724 218597158523103989942167 := by
  unfold tailWord_1915724
  simp only [CollatzResearch.WordTrace]
  refine ⟨34936097255833301228105113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46581463007777734970806817 34936097255833301228105113)
  ·
    refine ⟨26202072941874975921078835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34936097255833301228105113 26202072941874975921078835)
    ·
      refine ⟨39303109412812463881618253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26202072941874975921078835 39303109412812463881618253)
      ·
        refine ⟨14738666029804673955606845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39303109412812463881618253 14738666029804673955606845)
        ·
          refine ⟨5526999761176752733352567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14738666029804673955606845 5526999761176752733352567)
          ·
            refine ⟨8290499641765129100028851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5526999761176752733352567 8290499641765129100028851)
            ·
              refine ⟨12435749462647693650043277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8290499641765129100028851 12435749462647693650043277)
              ·
                refine ⟨4663406048492885118766229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12435749462647693650043277 4663406048492885118766229)
                ·
                  refine ⟨218597158523103989942167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4663406048492885118766229 218597158523103989942167)
                  ·
                    rfl

theorem cell22_1915724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 3, 6].length) (baseStart_1915724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1915724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1915724 prefixEnd_1915724 := by exact prefixLift 1915724
  have htrace : WordTrace (prefixWord ++ tailWord_1915724) baseStart_1915724 baseEnd_1915724 := by
    simpa [prefixWord, tailWord_1915724, baseEnd_1915724] using wordTrace_append hprefix tailTrace_1915724
  have hstable : (prefixWord ++ tailWord_1915724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915724).length < 2 ^ (prefixWord ++ tailWord_1915724).sum := by decide
  have hdescent : baseEnd_1915724 < baseStart_1915724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915769 : List Nat := [1, 2, 1, 3, 2, 5, 8]
def baseStart_1915769 : Nat := 118140960795 + 1915769 * 2 ^ 59
def prefixEnd_1915769 : Nat := 4983230072969 + 3 ^ 40 * 1915769 * 2
def baseEnd_1915769 : Nat := 24289143703294327868569

theorem tailTrace_1915769 : CollatzResearch.WordTrace tailWord_1915769 prefixEnd_1915769 24289143703294327868569 := by
  unfold tailWord_1915769
  simp only [CollatzResearch.WordTrace]
  refine ⟨69873835796503575141598361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46582557197669050094398907 69873835796503575141598361)
  ·
    refine ⟨52405376847377681356198771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69873835796503575141598361 52405376847377681356198771)
    ·
      refine ⟨78608065271066522034298157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52405376847377681356198771 78608065271066522034298157)
      ·
        refine ⟨29478024476649945762861809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78608065271066522034298157 29478024476649945762861809)
        ·
          refine ⟨22108518357487459322146357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29478024476649945762861809 22108518357487459322146357)
          ·
            refine ⟨2072673596014449311451221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22108518357487459322146357 2072673596014449311451221)
            ·
              refine ⟨24289143703294327868569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2072673596014449311451221 24289143703294327868569)
              ·
                rfl

theorem cell22_1915769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 8].length) (baseStart_1915769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1915769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1915769 prefixEnd_1915769 := by exact prefixLift 1915769
  have htrace : WordTrace (prefixWord ++ tailWord_1915769) baseStart_1915769 baseEnd_1915769 := by
    simpa [prefixWord, tailWord_1915769, baseEnd_1915769] using wordTrace_append hprefix tailTrace_1915769
  have hstable : (prefixWord ++ tailWord_1915769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915769).length < 2 ^ (prefixWord ++ tailWord_1915769).sum := by decide
  have hdescent : baseEnd_1915769 < baseStart_1915769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1915786 : List Nat := [3, 1, 2, 4, 1, 2, 2, 7]
def baseStart_1915786 : Nat := 118140960795 + 1915786 * 2 ^ 59
def prefixEnd_1915786 : Nat := 4983230072969 + 3 ^ 40 * 1915786 * 2
def baseEnd_1915786 : Nat := 72868077715151608308479

theorem tailTrace_1915786 : CollatzResearch.WordTrace tailWord_1915786 prefixEnd_1915786 72868077715151608308479 := by
  unfold tailWord_1915786
  simp only [CollatzResearch.WordTrace]
  refine ⟨17468613959360496761241803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46582970558294658029978141 17468613959360496761241803)
  ·
    refine ⟨26202920939040745141862705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17468613959360496761241803 26202920939040745141862705)
    ·
      refine ⟨19652190704280558856397029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26202920939040745141862705 19652190704280558856397029)
      ·
        refine ⟨3684785757052604785574443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19652190704280558856397029 3684785757052604785574443)
        ·
          refine ⟨5527178635578907178361665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3684785757052604785574443 5527178635578907178361665)
          ·
            refine ⟨4145383976684180383771249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5527178635578907178361665 4145383976684180383771249)
            ·
              refine ⟨3109037982513135287828437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4145383976684180383771249 3109037982513135287828437)
              ·
                refine ⟨72868077715151608308479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3109037982513135287828437 72868077715151608308479)
                ·
                  rfl

theorem cell22_1915786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 7].length) (baseStart_1915786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1915786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1915786 prefixEnd_1915786 := by exact prefixLift 1915786
  have htrace : WordTrace (prefixWord ++ tailWord_1915786) baseStart_1915786 baseEnd_1915786 := by
    simpa [prefixWord, tailWord_1915786, baseEnd_1915786] using wordTrace_append hprefix tailTrace_1915786
  have hstable : (prefixWord ++ tailWord_1915786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915786).length < 2 ^ (prefixWord ++ tailWord_1915786).sum := by decide
  have hdescent : baseEnd_1915786 < baseStart_1915786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916013 : List Nat := [1, 5, 1, 1, 2, 2, 1, 2, 3, 4]
def baseStart_1916013 : Nat := 118140960795 + 1916013 * 2 ^ 59
def prefixEnd_1916013 : Nat := 4983230072969 + 3 ^ 40 * 1916013 * 2
def baseEnd_1916013 : Nat := 655890406175411549350615

theorem tailTrace_1916013 : CollatzResearch.WordTrace tailWord_1916013 prefixEnd_1916013 655890406175411549350615 := by
  unfold tailWord_1916013
  simp only [CollatzResearch.WordTrace]
  refine ⟨69882735207619604813480693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46588490138413069875653795 69882735207619604813480693)
  ·
    refine ⟨6551506425714337951263815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69882735207619604813480693 6551506425714337951263815)
    ·
      refine ⟨9827259638571506926895723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6551506425714337951263815 9827259638571506926895723)
      ·
        refine ⟨14740889457857260390343585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9827259638571506926895723 14740889457857260390343585)
        ·
          refine ⟨11055667093392945292757689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14740889457857260390343585 11055667093392945292757689)
          ·
            refine ⟨8291750320044708969568267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11055667093392945292757689 8291750320044708969568267)
            ·
              refine ⟨12437625480067063454352401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8291750320044708969568267 12437625480067063454352401)
              ·
                refine ⟨9328219110050297590764301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12437625480067063454352401 9328219110050297590764301)
                ·
                  refine ⟨3498082166268861596536613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9328219110050297590764301 3498082166268861596536613)
                  ·
                    refine ⟨655890406175411549350615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3498082166268861596536613 655890406175411549350615)
                    ·
                      rfl

theorem cell22_1916013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_1916013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1916013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1916013 prefixEnd_1916013 := by exact prefixLift 1916013
  have htrace : WordTrace (prefixWord ++ tailWord_1916013) baseStart_1916013 baseEnd_1916013 := by
    simpa [prefixWord, tailWord_1916013, baseEnd_1916013] using wordTrace_append hprefix tailTrace_1916013
  have hstable : (prefixWord ++ tailWord_1916013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916013).length < 2 ^ (prefixWord ++ tailWord_1916013).sum := by decide
  have hdescent : baseEnd_1916013 < baseStart_1916013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916060 : List Nat := [2, 2, 3, 2, 1, 3, 1, 1, 4, 3]
def baseStart_1916060 : Nat := 118140960795 + 1916060 * 2 ^ 59
def prefixEnd_1916060 : Nat := 4983230072969 + 3 ^ 40 * 1916060 * 2
def baseEnd_1916060 : Nat := 655906495235919093425471

theorem tailTrace_1916060 : CollatzResearch.WordTrace tailWord_1916060 prefixEnd_1916060 655906495235919093425471 := by
  unfold tailWord_1916060
  simp only [CollatzResearch.WordTrace]
  refine ⟨34942224719224665920220817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46589632958966221226961089 34942224719224665920220817)
  ·
    refine ⟨26206668539418499440165613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34942224719224665920220817 26206668539418499440165613)
    ·
      refine ⟨9827500702281937290062105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26206668539418499440165613 9827500702281937290062105)
      ·
        refine ⟨7370625526711452967546579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9827500702281937290062105 7370625526711452967546579)
        ·
          refine ⟨11055938290067179451319869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7370625526711452967546579 11055938290067179451319869)
          ·
            refine ⟨4145976858775192294244951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11055938290067179451319869 4145976858775192294244951)
            ·
              refine ⟨6218965288162788441367427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4145976858775192294244951 6218965288162788441367427)
              ·
                refine ⟨9328447932244182662051141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6218965288162788441367427 9328447932244182662051141)
                ·
                  refine ⟨1749083987295784249134589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9328447932244182662051141 1749083987295784249134589)
                  ·
                    refine ⟨655906495235919093425471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1749083987295784249134589 655906495235919093425471)
                    ·
                      rfl

theorem cell22_1916060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 1, 4, 3].length) (baseStart_1916060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1916060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1916060 prefixEnd_1916060 := by exact prefixLift 1916060
  have htrace : WordTrace (prefixWord ++ tailWord_1916060) baseStart_1916060 baseEnd_1916060 := by
    simpa [prefixWord, tailWord_1916060, baseEnd_1916060] using wordTrace_append hprefix tailTrace_1916060
  have hstable : (prefixWord ++ tailWord_1916060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916060).length < 2 ^ (prefixWord ++ tailWord_1916060).sum := by decide
  have hdescent : baseEnd_1916060 < baseStart_1916060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916062 : List Nat := [4, 3, 1, 1, 2, 1, 2, 4, 4]
def baseStart_1916062 : Nat := 118140960795 + 1916062 * 2 ^ 59
def prefixEnd_1916062 : Nat := 4983230072969 + 3 ^ 40 * 1916062 * 2
def baseEnd_1916062 : Nat := 218635726625597251625155

theorem tailTrace_1916062 : CollatzResearch.WordTrace tailWord_1916062 prefixEnd_1916062 218635726625597251625155 := by
  unfold tailWord_1916062
  simp only [CollatzResearch.WordTrace]
  refine ⟨8735565298055260772751805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46589681589628057454676293 8735565298055260772751805)
  ·
    refine ⟨3275836986770722789781927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8735565298055260772751805 3275836986770722789781927)
    ·
      refine ⟨4913755480156084184672891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3275836986770722789781927 4913755480156084184672891)
      ·
        refine ⟨7370633220234126277009337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4913755480156084184672891 7370633220234126277009337)
        ·
          refine ⟨5527974915175594707757003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7370633220234126277009337 5527974915175594707757003)
          ·
            refine ⟨8291962372763392061635505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5527974915175594707757003 8291962372763392061635505)
            ·
              refine ⟨6218971779572544046226629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8291962372763392061635505 6218971779572544046226629)
              ·
                refine ⟨1166057208669852008667493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6218971779572544046226629 1166057208669852008667493)
                ·
                  refine ⟨218635726625597251625155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1166057208669852008667493 218635726625597251625155)
                  ·
                    rfl

theorem cell22_1916062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_1916062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1916062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1916062 prefixEnd_1916062 := by exact prefixLift 1916062
  have htrace : WordTrace (prefixWord ++ tailWord_1916062) baseStart_1916062 baseEnd_1916062 := by
    simpa [prefixWord, tailWord_1916062, baseEnd_1916062] using wordTrace_append hprefix tailTrace_1916062
  have hstable : (prefixWord ++ tailWord_1916062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916062).length < 2 ^ (prefixWord ++ tailWord_1916062).sum := by decide
  have hdescent : baseEnd_1916062 < baseStart_1916062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916077 : List Nat := [1, 5, 2, 1, 3, 2, 1, 1, 1, 5]
def baseStart_1916077 : Nat := 118140960795 + 1916077 * 2 ^ 59
def prefixEnd_1916077 : Nat := 4983230072969 + 3 ^ 40 * 1916077 * 2
def baseEnd_1916077 : Nat := 655912314683336715750419

theorem tailTrace_1916077 : CollatzResearch.WordTrace tailWord_1916077 prefixEnd_1916077 655912314683336715750419 := by
  unfold tailWord_1916077
  simp only [CollatzResearch.WordTrace]
  refine ⟨69885069479387743743810485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46590046319591829162540323 69885069479387743743810485)
  ·
    refine ⟨6551725263692600975982233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69885069479387743743810485 6551725263692600975982233)
    ·
      refine ⟨4913793947769450731986675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6551725263692600975982233 4913793947769450731986675)
      ·
        refine ⟨7370690921654176097980013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4913793947769450731986675 7370690921654176097980013)
        ·
          refine ⟨2764009095620316036742505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7370690921654176097980013 2764009095620316036742505)
          ·
            refine ⟨2073006821715237027556879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2764009095620316036742505 2073006821715237027556879)
            ·
              refine ⟨3109510232572855541335319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2073006821715237027556879 3109510232572855541335319)
              ·
                refine ⟨4664265348859283312002979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3109510232572855541335319 4664265348859283312002979)
                ·
                  refine ⟨6996398023288924968004469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4664265348859283312002979 6996398023288924968004469)
                  ·
                    refine ⟨655912314683336715750419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6996398023288924968004469 655912314683336715750419)
                    ·
                      rfl

theorem cell22_1916077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_1916077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1916077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1916077 prefixEnd_1916077 := by exact prefixLift 1916077
  have htrace : WordTrace (prefixWord ++ tailWord_1916077) baseStart_1916077 baseEnd_1916077 := by
    simpa [prefixWord, tailWord_1916077, baseEnd_1916077] using wordTrace_append hprefix tailTrace_1916077
  have hstable : (prefixWord ++ tailWord_1916077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916077).length < 2 ^ (prefixWord ++ tailWord_1916077).sum := by decide
  have hdescent : baseEnd_1916077 < baseStart_1916077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916088 : List Nat := [2, 1, 2, 1, 2, 1, 2, 3, 5, 3]
def baseStart_1916088 : Nat := 118140960795 + 1916088 * 2 ^ 59
def prefixEnd_1916088 : Nat := 4983230072969 + 3 ^ 40 * 1916088 * 2
def baseEnd_1916088 : Nat := 655916080208136353725385

theorem tailTrace_1916088 : CollatzResearch.WordTrace tailWord_1916088 prefixEnd_1916088 655916080208136353725385 := by
  unfold tailWord_1916088
  simp only [CollatzResearch.WordTrace]
  refine ⟨34942735341173946311230459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46590313788231928414973945 34942735341173946311230459)
  ·
    refine ⟨52414103011760919466845689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34942735341173946311230459 52414103011760919466845689)
    ·
      refine ⟨39310577258820689600134267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52414103011760919466845689 39310577258820689600134267)
      ·
        refine ⟨58965865888231034400201401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39310577258820689600134267 58965865888231034400201401)
        ·
          refine ⟨44224399416173275800151051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58965865888231034400201401 44224399416173275800151051)
          ·
            refine ⟨66336599124259913700226577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44224399416173275800151051 66336599124259913700226577)
            ·
              refine ⟨49752449343194935275169933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66336599124259913700226577 49752449343194935275169933)
              ·
                refine ⟨18657168503698100728188725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49752449343194935275169933 18657168503698100728188725)
                ·
                  refine ⟨1749109547221696943267693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18657168503698100728188725 1749109547221696943267693)
                  ·
                    refine ⟨655916080208136353725385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1749109547221696943267693 655916080208136353725385)
                    ·
                      rfl

theorem cell22_1916088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 5, 3].length) (baseStart_1916088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1916088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1916088 prefixEnd_1916088 := by exact prefixLift 1916088
  have htrace : WordTrace (prefixWord ++ tailWord_1916088) baseStart_1916088 baseEnd_1916088 := by
    simpa [prefixWord, tailWord_1916088, baseEnd_1916088] using wordTrace_append hprefix tailTrace_1916088
  have hstable : (prefixWord ++ tailWord_1916088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916088).length < 2 ^ (prefixWord ++ tailWord_1916088).sum := by decide
  have hdescent : baseEnd_1916088 < baseStart_1916088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916109 : List Nat := [1, 6, 2, 2, 1, 1, 1, 2, 2, 4]
def baseStart_1916109 : Nat := 118140960795 + 1916109 * 2 ^ 59
def prefixEnd_1916109 : Nat := 4983230072969 + 3 ^ 40 * 1916109 * 2
def baseEnd_1916109 : Nat := 655923268937299298950321

theorem tailTrace_1916109 : CollatzResearch.WordTrace tailWord_1916109 prefixEnd_1916109 655923268937299298950321 := by
  unfold tailWord_1916109
  simp only [CollatzResearch.WordTrace]
  refine ⟨69886236615271813208975381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46590824410181208805983587 69886236615271813208975381)
  ·
    refine ⟨3275917341340866244170721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 69886236615271813208975381 3275917341340866244170721)
    ·
      refine ⟨2456938006005649683128041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3275917341340866244170721 2456938006005649683128041)
      ·
        refine ⟨1842703504504237262346031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2456938006005649683128041 1842703504504237262346031)
        ·
          refine ⟨2764055256756355893519047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1842703504504237262346031 2764055256756355893519047)
          ·
            refine ⟨4146082885134533840278571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2764055256756355893519047 4146082885134533840278571)
            ·
              refine ⟨6219124327701800760417857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4146082885134533840278571 6219124327701800760417857)
              ·
                refine ⟨4664343245776350570313393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6219124327701800760417857 4664343245776350570313393)
                ·
                  refine ⟨3498257434332262927735045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4664343245776350570313393 3498257434332262927735045)
                  ·
                    refine ⟨655923268937299298950321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3498257434332262927735045 655923268937299298950321)
                    ·
                      rfl

theorem cell22_1916109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_1916109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1916109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1916109 prefixEnd_1916109 := by exact prefixLift 1916109
  have htrace : WordTrace (prefixWord ++ tailWord_1916109) baseStart_1916109 baseEnd_1916109 := by
    simpa [prefixWord, tailWord_1916109, baseEnd_1916109] using wordTrace_append hprefix tailTrace_1916109
  have hstable : (prefixWord ++ tailWord_1916109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916109).length < 2 ^ (prefixWord ++ tailWord_1916109).sum := by decide
  have hdescent : baseEnd_1916109 < baseStart_1916109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916193 : List Nat := [1, 2, 3, 2, 1, 1, 1, 4, 1, 6]
def baseStart_1916193 : Nat := 118140960795 + 1916193 * 2 ^ 59
def prefixEnd_1916193 : Nat := 4983230072969 + 3 ^ 40 * 1916193 * 2
def baseEnd_1916193 : Nat := 655952023853951079850063

theorem tailTrace_1916193 : CollatzResearch.WordTrace tailWord_1916193 prefixEnd_1916193 655952023853951079850063 := by
  unfold tailWord_1916193
  simp only [CollatzResearch.WordTrace]
  refine ⟨69889300346967495555033233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46592866897978330370022155 69889300346967495555033233)
  ·
    refine ⟨52416975260225621666274925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69889300346967495555033233 52416975260225621666274925)
    ·
      refine ⟨19656365722584608124853097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52416975260225621666274925 19656365722584608124853097)
      ·
        refine ⟨14742274291938456093639823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19656365722584608124853097 14742274291938456093639823)
        ·
          refine ⟨22113411437907684140459735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14742274291938456093639823 22113411437907684140459735)
          ·
            refine ⟨33170117156861526210689603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22113411437907684140459735 33170117156861526210689603)
            ·
              refine ⟨49755175735292289316034405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33170117156861526210689603 49755175735292289316034405)
              ·
                refine ⟨9329095450367304246756451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49755175735292289316034405 9329095450367304246756451)
                ·
                  refine ⟨13993643175550956370134677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9329095450367304246756451 13993643175550956370134677)
                  ·
                    refine ⟨655952023853951079850063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13993643175550956370134677 655952023853951079850063)
                    ·
                      rfl

theorem cell22_1916193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 6].length) (baseStart_1916193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1916193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1916193 prefixEnd_1916193 := by exact prefixLift 1916193
  have htrace : WordTrace (prefixWord ++ tailWord_1916193) baseStart_1916193 baseEnd_1916193 := by
    simpa [prefixWord, tailWord_1916193, baseEnd_1916193] using wordTrace_append hprefix tailTrace_1916193
  have hstable : (prefixWord ++ tailWord_1916193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916193).length < 2 ^ (prefixWord ++ tailWord_1916193).sum := by decide
  have hdescent : baseEnd_1916193 < baseStart_1916193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916195 : List Nat := [1, 1, 1, 4, 2, 4, 2, 1, 1, 5]
def baseStart_1916195 : Nat := 118140960795 + 1916195 * 2 ^ 59
def prefixEnd_1916195 : Nat := 4983230072969 + 3 ^ 40 * 1916195 * 2
def baseEnd_1916195 : Nat := 655952708494823741300057

theorem tailTrace_1916195 : CollatzResearch.WordTrace tailWord_1916195 prefixEnd_1916195 655952708494823741300057 := by
  unfold tailWord_1916195
  simp only [CollatzResearch.WordTrace]
  refine ⟨69889373292960249896606039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46592915528640166597737359 69889373292960249896606039)
  ·
    refine ⟨104834059939440374844909059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69889373292960249896606039 104834059939440374844909059)
    ·
      refine ⟨157251089909160562267363589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104834059939440374844909059 157251089909160562267363589)
      ·
        refine ⟨29484579357967605425130673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157251089909160562267363589 29484579357967605425130673)
        ·
          refine ⟨22113434518475704068848005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29484579357967605425130673 22113434518475704068848005)
          ·
            refine ⟨4146268972214194512909001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22113434518475704068848005 4146268972214194512909001)
            ·
              refine ⟨3109701729160645884681751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4146268972214194512909001 3109701729160645884681751)
              ·
                refine ⟨4664552593740968827022627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3109701729160645884681751 4664552593740968827022627)
                ·
                  refine ⟨6996828890611453240533941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4664552593740968827022627 6996828890611453240533941)
                  ·
                    refine ⟨655952708494823741300057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6996828890611453240533941 655952708494823741300057)
                    ·
                      rfl

theorem cell22_1916195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 1, 1, 5].length) (baseStart_1916195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1916195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1916195 prefixEnd_1916195 := by exact prefixLift 1916195
  have htrace : WordTrace (prefixWord ++ tailWord_1916195) baseStart_1916195 baseEnd_1916195 := by
    simpa [prefixWord, tailWord_1916195, baseEnd_1916195] using wordTrace_append hprefix tailTrace_1916195
  have hstable : (prefixWord ++ tailWord_1916195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916195).length < 2 ^ (prefixWord ++ tailWord_1916195).sum := by decide
  have hdescent : baseEnd_1916195 < baseStart_1916195 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916210 : List Nat := [3, 2, 1, 1, 4, 2, 1, 1, 1, 6]
def baseStart_1916210 : Nat := 118140960795 + 1916210 * 2 ^ 59
def prefixEnd_1916210 : Nat := 4983230072969 + 3 ^ 40 * 1916210 * 2
def baseEnd_1916210 : Nat := 655957843301368702175011

theorem tailTrace_1916210 : CollatzResearch.WordTrace tailWord_1916210 prefixEnd_1916210 655957843301368702175011 := by
  unfold tailWord_1916210
  simp only [CollatzResearch.WordTrace]
  refine ⟨17472480096976476864600521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46593280258603938305601389 17472480096976476864600521)
  ·
    refine ⟨13104360072732357648450391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17472480096976476864600521 13104360072732357648450391)
    ·
      refine ⟨19656540109098536472675587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13104360072732357648450391 19656540109098536472675587)
      ·
        refine ⟨29484810163647804709013381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19656540109098536472675587 29484810163647804709013381)
        ·
          refine ⟨5528401905683963382940009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29484810163647804709013381 5528401905683963382940009)
          ·
            refine ⟨4146301429262972537205007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5528401905683963382940009 4146301429262972537205007)
            ·
              refine ⟨6219452143894458805807511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4146301429262972537205007 6219452143894458805807511)
              ·
                refine ⟨9329178215841688208711267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6219452143894458805807511 9329178215841688208711267)
                ·
                  refine ⟨13993767323762532313066901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9329178215841688208711267 13993767323762532313066901)
                  ·
                    refine ⟨655957843301368702175011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13993767323762532313066901 655957843301368702175011)
                    ·
                      rfl

theorem cell22_1916210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 1, 1, 6].length) (baseStart_1916210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1916210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1916210 prefixEnd_1916210 := by exact prefixLift 1916210
  have htrace : WordTrace (prefixWord ++ tailWord_1916210) baseStart_1916210 baseEnd_1916210 := by
    simpa [prefixWord, tailWord_1916210, baseEnd_1916210] using wordTrace_append hprefix tailTrace_1916210
  have hstable : (prefixWord ++ tailWord_1916210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916210).length < 2 ^ (prefixWord ++ tailWord_1916210).sum := by decide
  have hdescent : baseEnd_1916210 < baseStart_1916210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916212 : List Nat := [2, 5, 1, 1, 1, 1, 2, 2, 4, 3]
def baseStart_1916212 : Nat := 118140960795 + 1916212 * 2 ^ 59
def prefixEnd_1916212 : Nat := 4983230072969 + 3 ^ 40 * 1916212 * 2
def baseEnd_1916212 : Nat := 655958527942241363625005

theorem tailTrace_1916212 : CollatzResearch.WordTrace tailWord_1916212 prefixEnd_1916212 655958527942241363625005 := by
  unfold tailWord_1916212
  simp only [CollatzResearch.WordTrace]
  refine ⟨34944996666949330899987445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46593328889265774533316593 34944996666949330899987445)
  ·
    refine ⟨3276093437526499771873823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34944996666949330899987445 3276093437526499771873823)
    ·
      refine ⟨4914140156289749657810735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3276093437526499771873823 4914140156289749657810735)
      ·
        refine ⟨7371210234434624486716103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4914140156289749657810735 7371210234434624486716103)
        ·
          refine ⟨11056815351651936730074155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7371210234434624486716103 11056815351651936730074155)
          ·
            refine ⟨16585223027477905095111233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11056815351651936730074155 16585223027477905095111233)
            ·
              refine ⟨12438917270608428821333425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16585223027477905095111233 12438917270608428821333425)
              ·
                refine ⟨9329187952956321616000069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12438917270608428821333425 9329187952956321616000069)
                ·
                  refine ⟨1749222741179310303000013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9329187952956321616000069 1749222741179310303000013)
                  ·
                    refine ⟨655958527942241363625005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1749222741179310303000013 655958527942241363625005)
                    ·
                      rfl

theorem cell22_1916212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_1916212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1916212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1916212 prefixEnd_1916212 := by exact prefixLift 1916212
  have htrace : WordTrace (prefixWord ++ tailWord_1916212) baseStart_1916212 baseEnd_1916212 := by
    simpa [prefixWord, tailWord_1916212, baseEnd_1916212] using wordTrace_append hprefix tailTrace_1916212
  have hstable : (prefixWord ++ tailWord_1916212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916212).length < 2 ^ (prefixWord ++ tailWord_1916212).sum := by decide
  have hdescent : baseEnd_1916212 < baseStart_1916212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916225 : List Nat := [1, 2, 5, 2, 1, 2, 9]
def baseStart_1916225 : Nat := 118140960795 + 1916225 * 2 ^ 59
def prefixEnd_1916225 : Nat := 4983230072969 + 3 ^ 40 * 1916225 * 2
def baseEnd_1916225 : Nat := 24294925115107913446295

theorem tailTrace_1916225 : CollatzResearch.WordTrace tailWord_1916225 prefixEnd_1916225 24294925115107913446295 := by
  unfold tailWord_1916225
  simp only [CollatzResearch.WordTrace]
  refine ⟨69890467482851565020198129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46593644988567710013465419 69890467482851565020198129)
  ·
    refine ⟨52417850612138673765148597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69890467482851565020198129 52417850612138673765148597)
    ·
      refine ⟨4914173494888000665482681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52417850612138673765148597 4914173494888000665482681)
      ·
        refine ⟨3685630121166000499112011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4914173494888000665482681 3685630121166000499112011)
        ·
          refine ⟨5528445181749000748668017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3685630121166000499112011 5528445181749000748668017)
          ·
            refine ⟨4146333886311750561501013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5528445181749000748668017 4146333886311750561501013)
            ·
              refine ⟨24294925115107913446295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4146333886311750561501013 24294925115107913446295)
              ·
                rfl

theorem cell22_1916225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 9].length) (baseStart_1916225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1916225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1916225 prefixEnd_1916225 := by exact prefixLift 1916225
  have htrace : WordTrace (prefixWord ++ tailWord_1916225) baseStart_1916225 baseEnd_1916225 := by
    simpa [prefixWord, tailWord_1916225, baseEnd_1916225] using wordTrace_append hprefix tailTrace_1916225
  have hstable : (prefixWord ++ tailWord_1916225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916225).length < 2 ^ (prefixWord ++ tailWord_1916225).sum := by decide
  have hdescent : baseEnd_1916225 < baseStart_1916225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916291 : List Nat := [1, 1, 1, 3, 5, 2, 3, 2, 1, 3]
def baseStart_1916291 : Nat := 118140960795 + 1916291 * 2 ^ 59
def prefixEnd_1916291 : Nat := 4983230072969 + 3 ^ 40 * 1916291 * 2
def baseEnd_1916291 : Nat := 655985571256711490899763

theorem tailTrace_1916291 : CollatzResearch.WordTrace tailWord_1916291 prefixEnd_1916291 655985571256711490899763 := by
  unfold tailWord_1916291
  simp only [CollatzResearch.WordTrace]
  refine ⟨69892874700612458292100727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46595249800408305528067151 69892874700612458292100727)
  ·
    refine ⟨104839312050918687438151091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69892874700612458292100727 104839312050918687438151091)
    ·
      refine ⟨157258968076378031157226637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104839312050918687438151091 157258968076378031157226637)
      ·
        refine ⟨58972113028641761683959989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157258968076378031157226637 58972113028641761683959989)
        ·
          refine ⟨5528635596435165157871249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58972113028641761683959989 5528635596435165157871249)
          ·
            refine ⟨4146476697326373868403437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5528635596435165157871249 4146476697326373868403437)
            ·
              refine ⟨1554928761497390200651289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4146476697326373868403437 1554928761497390200651289)
              ·
                refine ⟨1166196571123042650488467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1554928761497390200651289 1166196571123042650488467)
                ·
                  refine ⟨1749294856684563975732701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1166196571123042650488467 1749294856684563975732701)
                  ·
                    refine ⟨655985571256711490899763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1749294856684563975732701 655985571256711490899763)
                    ·
                      rfl

theorem cell22_1916291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 3, 2, 1, 3].length) (baseStart_1916291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1916291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1916291 prefixEnd_1916291 := by exact prefixLift 1916291
  have htrace : WordTrace (prefixWord ++ tailWord_1916291) baseStart_1916291 baseEnd_1916291 := by
    simpa [prefixWord, tailWord_1916291, baseEnd_1916291] using wordTrace_append hprefix tailTrace_1916291
  have hstable : (prefixWord ++ tailWord_1916291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916291).length < 2 ^ (prefixWord ++ tailWord_1916291).sum := by decide
  have hdescent : baseEnd_1916291 < baseStart_1916291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916300 : List Nat := [2, 2, 1, 2, 1, 3, 2, 2, 3, 4]
def baseStart_1916300 : Nat := 118140960795 + 1916300 * 2 ^ 59
def prefixEnd_1916300 : Nat := 4983230072969 + 3 ^ 40 * 1916300 * 2
def baseEnd_1916300 : Nat := 655988652140638467424735

theorem tailTrace_1916300 : CollatzResearch.WordTrace tailWord_1916300 prefixEnd_1916300 655988652140638467424735 := by
  unfold tailWord_1916300
  simp only [CollatzResearch.WordTrace]
  refine ⟨34946601478789926414589177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46595468638386568552785569 34946601478789926414589177)
  ·
    refine ⟨26209951109092444810941883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34946601478789926414589177 26209951109092444810941883)
    ·
      refine ⟨39314926663638667216412825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26209951109092444810941883 39314926663638667216412825)
      ·
        refine ⟨29486194997729000412309619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39314926663638667216412825 29486194997729000412309619)
        ·
          refine ⟨44229292496593500618464429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29486194997729000412309619 44229292496593500618464429)
          ·
            refine ⟨16585984686222562731924161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44229292496593500618464429 16585984686222562731924161)
            ·
              refine ⟨12439488514666922048943121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16585984686222562731924161 12439488514666922048943121)
              ·
                refine ⟨9329616386000191536707341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12439488514666922048943121 9329616386000191536707341)
                ·
                  refine ⟨3498606144750071826265253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9329616386000191536707341 3498606144750071826265253)
                  ·
                    refine ⟨655988652140638467424735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3498606144750071826265253 655988652140638467424735)
                    ·
                      rfl

theorem cell22_1916300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 3, 4].length) (baseStart_1916300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1916300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1916300 prefixEnd_1916300 := by exact prefixLift 1916300
  have htrace : WordTrace (prefixWord ++ tailWord_1916300) baseStart_1916300 baseEnd_1916300 := by
    simpa [prefixWord, tailWord_1916300, baseEnd_1916300] using wordTrace_append hprefix tailTrace_1916300
  have hstable : (prefixWord ++ tailWord_1916300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916300).length < 2 ^ (prefixWord ++ tailWord_1916300).sum := by decide
  have hdescent : baseEnd_1916300 < baseStart_1916300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916317 : List Nat := [1, 4, 2, 1, 3, 2, 1, 1, 3, 4]
def baseStart_1916317 : Nat := 118140960795 + 1916317 * 2 ^ 59
def prefixEnd_1916317 : Nat := 4983230072969 + 3 ^ 40 * 1916317 * 2
def baseEnd_1916317 : Nat := 655994471588056089749683

theorem tailTrace_1916317 : CollatzResearch.WordTrace tailWord_1916317 prefixEnd_1916317 655994471588056089749683 := by
  unfold tailWord_1916317
  simp only [CollatzResearch.WordTrace]
  refine ⟨69893822998518264732547205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46595881999012176488364803 69893822998518264732547205)
  ·
    refine ⟨13105091812222174637352601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69893822998518264732547205 13105091812222174637352601)
    ·
      refine ⟨9828818859166630978014451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13105091812222174637352601 9828818859166630978014451)
      ·
        refine ⟨14743228288749946467021677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9828818859166630978014451 14743228288749946467021677)
        ·
          refine ⟨5528710608281229925133129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14743228288749946467021677 5528710608281229925133129)
          ·
            refine ⟨4146532956210922443849847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5528710608281229925133129 4146532956210922443849847)
            ·
              refine ⟨6219799434316383665774771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4146532956210922443849847 6219799434316383665774771)
              ·
                refine ⟨9329699151474575498662157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6219799434316383665774771 9329699151474575498662157)
                ·
                  refine ⟨3498637181802965811998309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9329699151474575498662157 3498637181802965811998309)
                  ·
                    refine ⟨655994471588056089749683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3498637181802965811998309 655994471588056089749683)
                    ·
                      rfl

theorem cell22_1916317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_1916317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1916317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1916317 prefixEnd_1916317 := by exact prefixLift 1916317
  have htrace : WordTrace (prefixWord ++ tailWord_1916317) baseStart_1916317 baseEnd_1916317 := by
    simpa [prefixWord, tailWord_1916317, baseEnd_1916317] using wordTrace_append hprefix tailTrace_1916317
  have hstable : (prefixWord ++ tailWord_1916317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916317).length < 2 ^ (prefixWord ++ tailWord_1916317).sum := by decide
  have hdescent : baseEnd_1916317 < baseStart_1916317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916364 : List Nat := [2, 2, 1, 4, 2, 1, 2, 3, 2, 3]
def baseStart_1916364 : Nat := 118140960795 + 1916364 * 2 ^ 59
def prefixEnd_1916364 : Nat := 4983230072969 + 3 ^ 40 * 1916364 * 2
def baseEnd_1916364 : Nat := 656010560648563633824539

theorem tailTrace_1916364 : CollatzResearch.WordTrace tailWord_1916364 prefixEnd_1916364 656010560648563633824539 := by
  unfold tailWord_1916364
  simp only [CollatzResearch.WordTrace]
  refine ⟨34947768614673995879754073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46597024819565327839672097 34947768614673995879754073)
  ·
    refine ⟨26210826461005496909815555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34947768614673995879754073 26210826461005496909815555)
    ·
      refine ⟨39316239691508245364723333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26210826461005496909815555 39316239691508245364723333)
      ·
        refine ⟨7371794942157796005885625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39316239691508245364723333 7371794942157796005885625)
        ·
          refine ⟨5528846206618347004414219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7371794942157796005885625 5528846206618347004414219)
          ·
            refine ⟨8293269309927520506621329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5528846206618347004414219 8293269309927520506621329)
            ·
              refine ⟨6219951982445640379965997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8293269309927520506621329 6219951982445640379965997)
              ·
                refine ⟨2332481993417115142487249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6219951982445640379965997 2332481993417115142487249)
                ·
                  refine ⟨1749361495062836356865437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2332481993417115142487249 1749361495062836356865437)
                  ·
                    refine ⟨656010560648563633824539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1749361495062836356865437 656010560648563633824539)
                    ·
                      rfl

theorem cell22_1916364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 3, 2, 3].length) (baseStart_1916364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1916364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1916364 prefixEnd_1916364 := by exact prefixLift 1916364
  have htrace : WordTrace (prefixWord ++ tailWord_1916364) baseStart_1916364 baseEnd_1916364 := by
    simpa [prefixWord, tailWord_1916364, baseEnd_1916364] using wordTrace_append hprefix tailTrace_1916364
  have hstable : (prefixWord ++ tailWord_1916364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916364).length < 2 ^ (prefixWord ++ tailWord_1916364).sum := by decide
  have hdescent : baseEnd_1916364 < baseStart_1916364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916377 : List Nat := [1, 2, 1, 2, 4, 3, 3, 6]
def baseStart_1916377 : Nat := 118140960795 + 1916377 * 2 ^ 59
def prefixEnd_1916377 : Nat := 4983230072969 + 3 ^ 40 * 1916377 * 2
def baseEnd_1916377 : Nat := 72890556757137325916611

theorem tailTrace_1916377 : CollatzResearch.WordTrace tailWord_1916377 prefixEnd_1916377 72890556757137325916611 := by
  unfold tailWord_1916377
  simp only [CollatzResearch.WordTrace]
  refine ⟨69896011378300894979731385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46597340918867263319820923 69896011378300894979731385)
  ·
    refine ⟨52422008533725671234798539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69896011378300894979731385 52422008533725671234798539)
    ·
      refine ⟨78633012800588506852197809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52422008533725671234798539 78633012800588506852197809)
      ·
        refine ⟨58974759600441380139148357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78633012800588506852197809 58974759600441380139148357)
        ·
          refine ⟨11057767425082758776090317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58974759600441380139148357 11057767425082758776090317)
          ·
            refine ⟨4146662784406034541033869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11057767425082758776090317 4146662784406034541033869)
            ·
              refine ⟨1554998544152262952887701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4146662784406034541033869 1554998544152262952887701)
              ·
                refine ⟨72890556757137325916611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1554998544152262952887701 72890556757137325916611)
                ·
                  rfl

theorem cell22_1916377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 3, 6].length) (baseStart_1916377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1916377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1916377 prefixEnd_1916377 := by exact prefixLift 1916377
  have htrace : WordTrace (prefixWord ++ tailWord_1916377) baseStart_1916377 baseEnd_1916377 := by
    simpa [prefixWord, tailWord_1916377, baseEnd_1916377] using wordTrace_append hprefix tailTrace_1916377
  have hstable : (prefixWord ++ tailWord_1916377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916377).length < 2 ^ (prefixWord ++ tailWord_1916377).sum := by decide
  have hdescent : baseEnd_1916377 < baseStart_1916377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916392 : List Nat := [2, 1, 4, 1, 1, 2, 1, 2, 5, 3]
def baseStart_1916392 : Nat := 118140960795 + 1916392 * 2 ^ 59
def prefixEnd_1916392 : Nat := 4983230072969 + 3 ^ 40 * 1916392 * 2
def baseEnd_1916392 : Nat := 656020145620780894124453

theorem tailTrace_1916392 : CollatzResearch.WordTrace tailWord_1916392 prefixEnd_1916392 656020145620780894124453 := by
  unfold tailWord_1916392
  simp only [CollatzResearch.WordTrace]
  refine ⟨34948279236623276270763715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46597705648831035027684953 34948279236623276270763715)
  ·
    refine ⟨52422418854934914406145573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34948279236623276270763715 52422418854934914406145573)
    ·
      refine ⟨9829203535300296451152295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52422418854934914406145573 9829203535300296451152295)
      ·
        refine ⟨14743805302950444676728443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9829203535300296451152295 14743805302950444676728443)
        ·
          refine ⟨22115707954425667015092665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14743805302950444676728443 22115707954425667015092665)
          ·
            refine ⟨16586780965819250261319499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22115707954425667015092665 16586780965819250261319499)
            ·
              refine ⟨24880171448728875391979249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16586780965819250261319499 24880171448728875391979249)
              ·
                refine ⟨18660128586546656543984437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24880171448728875391979249 18660128586546656543984437)
                ·
                  refine ⟨1749387054988749050998541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18660128586546656543984437 1749387054988749050998541)
                  ·
                    refine ⟨656020145620780894124453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1749387054988749050998541 656020145620780894124453)
                    ·
                      rfl

theorem cell22_1916392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 5, 3].length) (baseStart_1916392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1916392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1916392 prefixEnd_1916392 := by exact prefixLift 1916392
  have htrace : WordTrace (prefixWord ++ tailWord_1916392) baseStart_1916392 baseEnd_1916392 := by
    simpa [prefixWord, tailWord_1916392, baseEnd_1916392] using wordTrace_append hprefix tailTrace_1916392
  have hstable : (prefixWord ++ tailWord_1916392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916392).length < 2 ^ (prefixWord ++ tailWord_1916392).sum := by decide
  have hdescent : baseEnd_1916392 < baseStart_1916392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916467 : List Nat := [1, 1, 1, 2, 4, 3, 3, 1, 6]
def baseStart_1916467 : Nat := 118140960795 + 1916467 * 2 ^ 59
def prefixEnd_1916467 : Nat := 4983230072969 + 3 ^ 40 * 1916467 * 2
def baseEnd_1916467 : Nat := 218681939884501899499741

theorem tailTrace_1916467 : CollatzResearch.WordTrace tailWord_1916467 prefixEnd_1916467 218681939884501899499741 := by
  unfold tailWord_1916467
  simp only [CollatzResearch.WordTrace]
  refine ⟨69899293947974840350507655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46599529298649893567005103 69899293947974840350507655)
  ·
    refine ⟨104848940921962260525761483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69899293947974840350507655 104848940921962260525761483)
    ·
      refine ⟨157273411382943390788642225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104848940921962260525761483 157273411382943390788642225)
      ·
        refine ⟨117955058537207543091481669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157273411382943390788642225 117955058537207543091481669)
        ·
          refine ⟨22116573475726414329652813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117955058537207543091481669 22116573475726414329652813)
          ·
            refine ⟨8293715053397405373619805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22116573475726414329652813 8293715053397405373619805)
            ·
              refine ⟨3110143145024027015107427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8293715053397405373619805 3110143145024027015107427)
              ·
                refine ⟨4665214717536040522661141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3110143145024027015107427 4665214717536040522661141)
                ·
                  refine ⟨218681939884501899499741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4665214717536040522661141 218681939884501899499741)
                  ·
                    rfl

theorem cell22_1916467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 1, 6].length) (baseStart_1916467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1916467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1916467 prefixEnd_1916467 := by exact prefixLift 1916467
  have htrace : WordTrace (prefixWord ++ tailWord_1916467) baseStart_1916467 baseEnd_1916467 := by
    simpa [prefixWord, tailWord_1916467, baseEnd_1916467] using wordTrace_append hprefix tailTrace_1916467
  have hstable : (prefixWord ++ tailWord_1916467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916467).length < 2 ^ (prefixWord ++ tailWord_1916467).sum := by decide
  have hdescent : baseEnd_1916467 < baseStart_1916467 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916516 : List Nat := [2, 3, 1, 1, 2, 4, 2, 2, 2, 3]
def baseStart_1916516 : Nat := 118140960795 + 1916516 * 2 ^ 59
def prefixEnd_1916516 : Nat := 4983230072969 + 3 ^ 40 * 1916516 * 2
def baseEnd_1916516 : Nat := 656062593354885904024073

theorem tailTrace_1916516 : CollatzResearch.WordTrace tailWord_1916516 prefixEnd_1916516 656062593354885904024073 := by
  unfold tailWord_1916516
  simp only [CollatzResearch.WordTrace]
  refine ⟨34950540562398660859520701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46600720749864881146027601 34950540562398660859520701)
  ·
    refine ⟨13106452710899497822320263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34950540562398660859520701 13106452710899497822320263)
    ·
      refine ⟨19659679066349246733480395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13106452710899497822320263 19659679066349246733480395)
      ·
        refine ⟨29489518599523870100220593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19659679066349246733480395 29489518599523870100220593)
        ·
          refine ⟨22117138949642902575165445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29489518599523870100220593 22117138949642902575165445)
          ·
            refine ⟨4146963553058044232843521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22117138949642902575165445 4146963553058044232843521)
            ·
              refine ⟨3110222664793533174632641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4146963553058044232843521 3110222664793533174632641)
              ·
                refine ⟨2332666998595149880974481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3110222664793533174632641 2332666998595149880974481)
                ·
                  refine ⟨1749500248946362410730861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2332666998595149880974481 1749500248946362410730861)
                  ·
                    refine ⟨656062593354885904024073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1749500248946362410730861 656062593354885904024073)
                    ·
                      rfl

theorem cell22_1916516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 2, 2, 3].length) (baseStart_1916516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1916516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1916516 prefixEnd_1916516 := by exact prefixLift 1916516
  have htrace : WordTrace (prefixWord ++ tailWord_1916516) baseStart_1916516 baseEnd_1916516 := by
    simpa [prefixWord, tailWord_1916516, baseEnd_1916516] using wordTrace_append hprefix tailTrace_1916516
  have hstable : (prefixWord ++ tailWord_1916516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916516).length < 2 ^ (prefixWord ++ tailWord_1916516).sum := by decide
  have hdescent : baseEnd_1916516 < baseStart_1916516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916544 : List Nat := [2, 1, 1, 2, 1, 4, 3, 2, 3, 3]
def baseStart_1916544 : Nat := 118140960795 + 1916544 * 2 ^ 59
def prefixEnd_1916544 : Nat := 4983230072969 + 3 ^ 40 * 1916544 * 2
def baseEnd_1916544 : Nat := 656072178327103164323987

theorem tailTrace_1916544 : CollatzResearch.WordTrace tailWord_1916544 prefixEnd_1916544 656072178327103164323987 := by
  unfold tailWord_1916544
  simp only [CollatzResearch.WordTrace]
  refine ⟨34951051184347941250530343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46601401579130588334040457 34951051184347941250530343)
  ·
    refine ⟨52426576776521911875795515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34951051184347941250530343 52426576776521911875795515)
    ·
      refine ⟨78639865164782867813693273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52426576776521911875795515 78639865164782867813693273)
      ·
        refine ⟨58979898873587150860269955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78639865164782867813693273 58979898873587150860269955)
        ·
          refine ⟨88469848310380726290404933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58979898873587150860269955 88469848310380726290404933)
          ·
            refine ⟨16588096558196386179450925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88469848310380726290404933 16588096558196386179450925)
            ·
              refine ⟨6220536209323644817294097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16588096558196386179450925 6220536209323644817294097)
              ·
                refine ⟨4665402156992733612970573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6220536209323644817294097 4665402156992733612970573)
                ·
                  refine ⟨1749525808872275104863965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4665402156992733612970573 1749525808872275104863965)
                  ·
                    refine ⟨656072178327103164323987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1749525808872275104863965 656072178327103164323987)
                    ·
                      rfl

theorem cell22_1916544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 2, 3, 3].length) (baseStart_1916544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1916544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1916544 prefixEnd_1916544 := by exact prefixLift 1916544
  have htrace : WordTrace (prefixWord ++ tailWord_1916544) baseStart_1916544 baseEnd_1916544 := by
    simpa [prefixWord, tailWord_1916544, baseEnd_1916544] using wordTrace_append hprefix tailTrace_1916544
  have hstable : (prefixWord ++ tailWord_1916544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916544).length < 2 ^ (prefixWord ++ tailWord_1916544).sum := by decide
  have hdescent : baseEnd_1916544 < baseStart_1916544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916548 : List Nat := [2, 3, 2, 1, 5, 1, 1, 1, 2, 4]
def baseStart_1916548 : Nat := 118140960795 + 1916548 * 2 ^ 59
def prefixEnd_1916548 : Nat := 4983230072969 + 3 ^ 40 * 1916548 * 2
def baseEnd_1916548 : Nat := 656073547608848487223975

theorem tailTrace_1916548 : CollatzResearch.WordTrace tailWord_1916548 prefixEnd_1916548 656073547608848487223975 := by
  unfold tailWord_1916548
  simp only [CollatzResearch.WordTrace]
  refine ⟨34951124130340695592103149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46601498840454260789470865 34951124130340695592103149)
  ·
    refine ⟨13106671548877760847038681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34951124130340695592103149 13106671548877760847038681)
    ·
      refine ⟨9830003661658320635279011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13106671548877760847038681 9830003661658320635279011)
      ·
        refine ⟨14745005492487480952918517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9830003661658320635279011 14745005492487480952918517)
        ·
          refine ⟨1382344264920701339336111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14745005492487480952918517 1382344264920701339336111)
          ·
            refine ⟨2073516397381052009004167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1382344264920701339336111 2073516397381052009004167)
            ·
              refine ⟨3110274596071578013506251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2073516397381052009004167 3110274596071578013506251)
              ·
                refine ⟨4665411894107367020259377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3110274596071578013506251 4665411894107367020259377)
                ·
                  refine ⟨3499058920580525265194533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4665411894107367020259377 3499058920580525265194533)
                  ·
                    refine ⟨656073547608848487223975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3499058920580525265194533 656073547608848487223975)
                    ·
                      rfl

theorem cell22_1916548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 1, 2, 4].length) (baseStart_1916548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1916548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1916548 prefixEnd_1916548 := by exact prefixLift 1916548
  have htrace : WordTrace (prefixWord ++ tailWord_1916548) baseStart_1916548 baseEnd_1916548 := by
    simpa [prefixWord, tailWord_1916548, baseEnd_1916548] using wordTrace_append hprefix tailTrace_1916548
  have hstable : (prefixWord ++ tailWord_1916548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916548).length < 2 ^ (prefixWord ++ tailWord_1916548).sum := by decide
  have hdescent : baseEnd_1916548 < baseStart_1916548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916589 : List Nat := [1, 5, 2, 1, 1, 1, 1, 3, 2, 5]
def baseStart_1916589 : Nat := 118140960795 + 1916589 * 2 ^ 59
def prefixEnd_1916589 : Nat := 4983230072969 + 3 ^ 40 * 1916589 * 2
def baseEnd_1916589 : Nat := 656087582746738046948849

theorem tailTrace_1916589 : CollatzResearch.WordTrace tailWord_1916589 prefixEnd_1916589 656087582746738046948849 := by
  unfold tailWord_1916589
  simp only [CollatzResearch.WordTrace]
  refine ⟨69903743653532855186448821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46602495769021903457632547 69903743653532855186448821)
  ·
    refine ⟨6553475967518705173729577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69903743653532855186448821 6553475967518705173729577)
    ·
      refine ⟨4915106975639028880297183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6553475967518705173729577 4915106975639028880297183)
      ·
        refine ⟨7372660463458543320445775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4915106975639028880297183 7372660463458543320445775)
        ·
          refine ⟨11058990695187814980668663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7372660463458543320445775 11058990695187814980668663)
          ·
            refine ⟨16588486042781722471002995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11058990695187814980668663 16588486042781722471002995)
            ·
              refine ⟨24882729064172583706504493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16588486042781722471002995 24882729064172583706504493)
              ·
                refine ⟨9331023399064718889939185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24882729064172583706504493 9331023399064718889939185)
                ·
                  refine ⟨6998267549298539167454389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9331023399064718889939185 6998267549298539167454389)
                  ·
                    refine ⟨656087582746738046948849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6998267549298539167454389 656087582746738046948849)
                    ·
                      rfl

theorem cell22_1916589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_1916589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1916589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1916589 prefixEnd_1916589 := by exact prefixLift 1916589
  have htrace : WordTrace (prefixWord ++ tailWord_1916589) baseStart_1916589 baseEnd_1916589 := by
    simpa [prefixWord, tailWord_1916589, baseEnd_1916589] using wordTrace_append hprefix tailTrace_1916589
  have hstable : (prefixWord ++ tailWord_1916589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916589).length < 2 ^ (prefixWord ++ tailWord_1916589).sum := by decide
  have hdescent : baseEnd_1916589 < baseStart_1916589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916730 : List Nat := [3, 1, 1, 1, 5, 2, 2, 3, 1, 3]
def baseStart_1916730 : Nat := 118140960795 + 1916730 * 2 ^ 59
def prefixEnd_1916730 : Nat := 4983230072969 + 3 ^ 40 * 1916730 * 2
def baseEnd_1916730 : Nat := 656135849928260679173417

theorem tailTrace_1916730 : CollatzResearch.WordTrace tailWord_1916730 prefixEnd_1916730 656135849928260679173417 := by
  unfold tailWord_1916730
  simp only [CollatzResearch.WordTrace]
  refine ⟨17477221586505509066832911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46605924230681357511554429 17477221586505509066832911)
  ·
    refine ⟨26215832379758263600249367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17477221586505509066832911 26215832379758263600249367)
    ·
      refine ⟨39323748569637395400374051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26215832379758263600249367 39323748569637395400374051)
      ·
        refine ⟨58985622854456093100561077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39323748569637395400374051 58985622854456093100561077)
        ·
          refine ⟨5529902142605258728177601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58985622854456093100561077 5529902142605258728177601)
          ·
            refine ⟨4147426606953944046133201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5529902142605258728177601 4147426606953944046133201)
            ·
              refine ⟨3110569955215458034599901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4147426606953944046133201 3110569955215458034599901)
              ·
                refine ⟨1166463733205796762974963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3110569955215458034599901 1166463733205796762974963)
                ·
                  refine ⟨1749695599808695144462445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1166463733205796762974963 1749695599808695144462445)
                  ·
                    refine ⟨656135849928260679173417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1749695599808695144462445 656135849928260679173417)
                    ·
                      rfl

theorem cell22_1916730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 3, 1, 3].length) (baseStart_1916730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1916730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1916730 prefixEnd_1916730 := by exact prefixLift 1916730
  have htrace : WordTrace (prefixWord ++ tailWord_1916730) baseStart_1916730 baseEnd_1916730 := by
    simpa [prefixWord, tailWord_1916730, baseEnd_1916730] using wordTrace_append hprefix tailTrace_1916730
  have hstable : (prefixWord ++ tailWord_1916730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916730).length < 2 ^ (prefixWord ++ tailWord_1916730).sum := by decide
  have hdescent : baseEnd_1916730 < baseStart_1916730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916820 : List Nat := [2, 4, 2, 1, 1, 3, 1, 3, 2, 3]
def baseStart_1916820 : Nat := 118140960795 + 1916820 * 2 ^ 59
def prefixEnd_1916820 : Nat := 4983230072969 + 3 ^ 40 * 1916820 * 2
def baseEnd_1916820 : Nat := 656166658767530444423141

theorem tailTrace_1916820 : CollatzResearch.WordTrace tailWord_1916820 prefixEnd_1916820 656166658767530444423141 := by
  unfold tailWord_1916820
  simp only [CollatzResearch.WordTrace]
  refine ⟨34956084457847990819053957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46608112610463987758738609 34956084457847990819053957)
  ·
    refine ⟨6554265835846498278572617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34956084457847990819053957 6554265835846498278572617)
    ·
      refine ⟨4915699376884873708929463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6554265835846498278572617 4915699376884873708929463)
      ·
        refine ⟨7373549065327310563394195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4915699376884873708929463 7373549065327310563394195)
        ·
          refine ⟨11060323597990965845091293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7373549065327310563394195 11060323597990965845091293)
          ·
            refine ⟨4147621349246612191909235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11060323597990965845091293 4147621349246612191909235)
            ·
              refine ⟨6221432023869918287863853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4147621349246612191909235 6221432023869918287863853)
              ·
                refine ⟨2333037008951219357948945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6221432023869918287863853 2333037008951219357948945)
                ·
                  refine ⟨1749777756713414518461709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2333037008951219357948945 1749777756713414518461709)
                  ·
                    refine ⟨656166658767530444423141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1749777756713414518461709 656166658767530444423141)
                    ·
                      rfl

theorem cell22_1916820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_1916820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1916820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1916820 prefixEnd_1916820 := by exact prefixLift 1916820
  have htrace : WordTrace (prefixWord ++ tailWord_1916820) baseStart_1916820 baseEnd_1916820 := by
    simpa [prefixWord, tailWord_1916820, baseEnd_1916820] using wordTrace_append hprefix tailTrace_1916820
  have hstable : (prefixWord ++ tailWord_1916820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916820).length < 2 ^ (prefixWord ++ tailWord_1916820).sum := by decide
  have hdescent : baseEnd_1916820 < baseStart_1916820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916876 : List Nat := [2, 2, 1, 4, 1, 2, 1, 1, 1, 7]
def baseStart_1916876 : Nat := 118140960795 + 1916876 * 2 ^ 59
def prefixEnd_1916876 : Nat := 4983230072969 + 3 ^ 40 * 1916876 * 2
def baseEnd_1916876 : Nat := 656185828711964965022969

theorem tailTrace_1916876 : CollatzResearch.WordTrace tailWord_1916876 prefixEnd_1916876 656185828711964965022969 := by
  unfold tailWord_1916876
  simp only [CollatzResearch.WordTrace]
  refine ⟨34957105701746551601073241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46609474268995402134764321 34957105701746551601073241)
  ·
    refine ⟨26217829276309913700804931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34957105701746551601073241 26217829276309913700804931)
    ·
      refine ⟨39326743914464870551207397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26217829276309913700804931 39326743914464870551207397)
      ·
        refine ⟨7373764483962163228351387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39326743914464870551207397 7373764483962163228351387)
        ·
          refine ⟨11060646725943244842527081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7373764483962163228351387 11060646725943244842527081)
          ·
            refine ⟨8295485044457433631895311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11060646725943244842527081 8295485044457433631895311)
            ·
              refine ⟨12443227566686150447842967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8295485044457433631895311 12443227566686150447842967)
              ·
                refine ⟨18664841350029225671764451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12443227566686150447842967 18664841350029225671764451)
                ·
                  refine ⟨27997262025043838507646677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18664841350029225671764451 27997262025043838507646677)
                  ·
                    refine ⟨656185828711964965022969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27997262025043838507646677 656185828711964965022969)
                    ·
                      rfl

theorem cell22_1916876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 1, 7].length) (baseStart_1916876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1916876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1916876 prefixEnd_1916876 := by exact prefixLift 1916876
  have htrace : WordTrace (prefixWord ++ tailWord_1916876) baseStart_1916876 baseEnd_1916876 := by
    simpa [prefixWord, tailWord_1916876, baseEnd_1916876] using wordTrace_append hprefix tailTrace_1916876
  have hstable : (prefixWord ++ tailWord_1916876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916876).length < 2 ^ (prefixWord ++ tailWord_1916876).sum := by decide
  have hdescent : baseEnd_1916876 < baseStart_1916876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916906 : List Nat := [3, 1, 3, 1, 2, 1, 1, 2, 8]
def baseStart_1916906 : Nat := 118140960795 + 1916906 * 2 ^ 59
def prefixEnd_1916906 : Nat := 4983230072969 + 3 ^ 40 * 1916906 * 2
def baseEnd_1916906 : Nat := 218732032775018295590959

theorem tailTrace_1916906 : CollatzResearch.WordTrace tailWord_1916906 prefixEnd_1916906 218732032775018295590959 := by
  unfold tailWord_1916906
  simp only [CollatzResearch.WordTrace]
  refine ⟨17478826398346104581434643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46610203728922945550492381 17478826398346104581434643)
  ·
    refine ⟨26218239597519156872151965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17478826398346104581434643 26218239597519156872151965)
    ·
      refine ⟨9831839849069683827056987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26218239597519156872151965 9831839849069683827056987)
      ·
        refine ⟨14747759773604525740585481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9831839849069683827056987 14747759773604525740585481)
        ·
          refine ⟨11060819830203394305439111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14747759773604525740585481 11060819830203394305439111)
          ·
            refine ⟨16591229745305091458158667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11060819830203394305439111 16591229745305091458158667)
            ·
              refine ⟨24886844617957637187238001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16591229745305091458158667 24886844617957637187238001)
              ·
                refine ⟨18665133463468227890428501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24886844617957637187238001 18665133463468227890428501)
                ·
                  refine ⟨218732032775018295590959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18665133463468227890428501 218732032775018295590959)
                  ·
                    rfl

theorem cell22_1916906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 8].length) (baseStart_1916906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1916906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1916906 prefixEnd_1916906 := by exact prefixLift 1916906
  have htrace : WordTrace (prefixWord ++ tailWord_1916906) baseStart_1916906 baseEnd_1916906 := by
    simpa [prefixWord, tailWord_1916906, baseEnd_1916906] using wordTrace_append hprefix tailTrace_1916906
  have hstable : (prefixWord ++ tailWord_1916906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916906).length < 2 ^ (prefixWord ++ tailWord_1916906).sum := by decide
  have hdescent : baseEnd_1916906 < baseStart_1916906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916923 : List Nat := [1, 1, 1, 1, 1, 3, 6, 4, 4]
def baseStart_1916923 : Nat := 118140960795 + 1916923 * 2 ^ 59
def prefixEnd_1916923 : Nat := 4983230072969 + 3 ^ 40 * 1916923 * 2
def baseEnd_1916923 : Nat := 218733972590824169699275

theorem tailTrace_1916923 : CollatzResearch.WordTrace tailWord_1916923 prefixEnd_1916923 218733972590824169699275 := by
  unfold tailWord_1916923
  simp only [CollatzResearch.WordTrace]
  refine ⟨69915925634322830229107423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46610617089548553486071615 69915925634322830229107423)
  ·
    refine ⟨104873888451484245343661135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69915925634322830229107423 104873888451484245343661135)
    ·
      refine ⟨157310832677226368015491703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104873888451484245343661135 157310832677226368015491703)
      ·
        refine ⟨235966249015839552023237555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157310832677226368015491703 235966249015839552023237555)
        ·
          refine ⟨353949373523759328034856333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235966249015839552023237555 353949373523759328034856333)
          ·
            refine ⟨132731015071409748013071125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 353949373523759328034856333 132731015071409748013071125)
            ·
              refine ⟨6221766331472331938112709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 132731015071409748013071125 6221766331472331938112709)
              ·
                refine ⟨1166581187151062238396133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6221766331472331938112709 1166581187151062238396133)
                ·
                  refine ⟨218733972590824169699275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1166581187151062238396133 218733972590824169699275)
                  ·
                    rfl

theorem cell22_1916923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 4, 4].length) (baseStart_1916923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1916923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1916923 prefixEnd_1916923 := by exact prefixLift 1916923
  have htrace : WordTrace (prefixWord ++ tailWord_1916923) baseStart_1916923 baseEnd_1916923 := by
    simpa [prefixWord, tailWord_1916923, baseEnd_1916923] using wordTrace_append hprefix tailTrace_1916923
  have hstable : (prefixWord ++ tailWord_1916923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916923).length < 2 ^ (prefixWord ++ tailWord_1916923).sum := by decide
  have hdescent : baseEnd_1916923 < baseStart_1916923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916936 : List Nat := [2, 1, 3, 2, 1, 2, 1, 1, 3, 6]
def baseStart_1916936 : Nat := 118140960795 + 1916936 * 2 ^ 59
def prefixEnd_1916936 : Nat := 4983230072969 + 3 ^ 40 * 1916936 * 2
def baseEnd_1916936 : Nat := 656206367938144808522785

theorem tailTrace_1916936 : CollatzResearch.WordTrace tailWord_1916936 prefixEnd_1916936 656206367938144808522785 := by
  unfold tailWord_1916936
  simp only [CollatzResearch.WordTrace]
  refine ⟨34958199891637866724665331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46610933188850488966220441 34958199891637866724665331)
  ·
    refine ⟨52437299837456800086997997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34958199891637866724665331 52437299837456800086997997)
    ·
      refine ⟨19663987439046300032624249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52437299837456800086997997 19663987439046300032624249)
      ·
        refine ⟨14747990579284725024468187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19663987439046300032624249 14747990579284725024468187)
        ·
          refine ⟨22121985868927087536702281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14747990579284725024468187 22121985868927087536702281)
          ·
            refine ⟨16591489401695315652526711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22121985868927087536702281 16591489401695315652526711)
            ·
              refine ⟨24887234102542973478790067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16591489401695315652526711 24887234102542973478790067)
              ·
                refine ⟨37330851153814460218185101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24887234102542973478790067 37330851153814460218185101)
                ·
                  refine ⟨13999069182680422581819413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37330851153814460218185101 13999069182680422581819413)
                  ·
                    refine ⟨656206367938144808522785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13999069182680422581819413 656206367938144808522785)
                    ·
                      rfl

theorem cell22_1916936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 3, 6].length) (baseStart_1916936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1916936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1916936 prefixEnd_1916936 := by exact prefixLift 1916936
  have htrace : WordTrace (prefixWord ++ tailWord_1916936) baseStart_1916936 baseEnd_1916936 := by
    simpa [prefixWord, tailWord_1916936, baseEnd_1916936] using wordTrace_append hprefix tailTrace_1916936
  have hstable : (prefixWord ++ tailWord_1916936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916936).length < 2 ^ (prefixWord ++ tailWord_1916936).sum := by decide
  have hdescent : baseEnd_1916936 < baseStart_1916936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916957 : List Nat := [1, 4, 2, 2, 2, 3, 1, 3, 4]
def baseStart_1916957 : Nat := 118140960795 + 1916957 * 2 ^ 59
def prefixEnd_1916957 : Nat := 4983230072969 + 3 ^ 40 * 1916957 * 2
def baseEnd_1916957 : Nat := 218737852222435917915907

theorem tailTrace_1916957 : CollatzResearch.WordTrace tailWord_1916957 prefixEnd_1916957 218737852222435917915907 := by
  unfold tailWord_1916957
  simp only [CollatzResearch.WordTrace]
  refine ⟨69917165716199654035845125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46611443810799769357230083 69917165716199654035845125)
  ·
    refine ⟨13109468571787435131720961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69917165716199654035845125 13109468571787435131720961)
    ·
      refine ⟨9832101428840576348790721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13109468571787435131720961 9832101428840576348790721)
      ·
        refine ⟨7374076071630432261593041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9832101428840576348790721 7374076071630432261593041)
        ·
          refine ⟨5530557053722824196194781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7374076071630432261593041 5530557053722824196194781)
          ·
            refine ⟨2073958895146059073573043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5530557053722824196194781 2073958895146059073573043)
            ·
              refine ⟨3110938342719088610359565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2073958895146059073573043 3110938342719088610359565)
              ·
                refine ⟨1166601878519658228884837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3110938342719088610359565 1166601878519658228884837)
                ·
                  refine ⟨218737852222435917915907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1166601878519658228884837 218737852222435917915907)
                  ·
                    rfl

theorem cell22_1916957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 3, 4].length) (baseStart_1916957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1916957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1916957 prefixEnd_1916957 := by exact prefixLift 1916957
  have htrace : WordTrace (prefixWord ++ tailWord_1916957) baseStart_1916957 baseEnd_1916957 := by
    simpa [prefixWord, tailWord_1916957, baseEnd_1916957] using wordTrace_append hprefix tailTrace_1916957
  have hstable : (prefixWord ++ tailWord_1916957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916957).length < 2 ^ (prefixWord ++ tailWord_1916957).sum := by decide
  have hdescent : baseEnd_1916957 < baseStart_1916957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916970 : List Nat := [3, 1, 4, 1, 2, 2, 1, 2, 2, 4]
def baseStart_1916970 : Nat := 118140960795 + 1916970 * 2 ^ 59
def prefixEnd_1916970 : Nat := 4983230072969 + 3 ^ 40 * 1916970 * 2
def baseEnd_1916970 : Nat := 656218006832980053172681

theorem tailTrace_1916970 : CollatzResearch.WordTrace tailWord_1916970 prefixEnd_1916970 656218006832980053172681 := by
  unfold tailWord_1916970
  simp only [CollatzResearch.WordTrace]
  refine ⟨17479409966288139314017091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46611759910101704837378909 17479409966288139314017091)
  ·
    refine ⟨26219114949432208971025637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17479409966288139314017091 26219114949432208971025637)
    ·
      refine ⟨4916084053018539182067307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26219114949432208971025637 4916084053018539182067307)
      ·
        refine ⟨7374126079527808773100961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4916084053018539182067307 7374126079527808773100961)
        ·
          refine ⟨5530594559645856579825721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7374126079527808773100961 5530594559645856579825721)
          ·
            refine ⟨4147945919734392434869291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5530594559645856579825721 4147945919734392434869291)
            ·
              refine ⟨6221918879601588652303937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4147945919734392434869291 6221918879601588652303937)
              ·
                refine ⟨4666439159701191489227953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6221918879601588652303937 4666439159701191489227953)
                ·
                  refine ⟨3499829369775893616920965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4666439159701191489227953 3499829369775893616920965)
                  ·
                    refine ⟨656218006832980053172681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3499829369775893616920965 656218006832980053172681)
                    ·
                      rfl

theorem cell22_1916970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_1916970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1916970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1916970 prefixEnd_1916970 := by exact prefixLift 1916970
  have htrace : WordTrace (prefixWord ++ tailWord_1916970) baseStart_1916970 baseEnd_1916970 := by
    simpa [prefixWord, tailWord_1916970, baseEnd_1916970] using wordTrace_append hprefix tailTrace_1916970
  have hstable : (prefixWord ++ tailWord_1916970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916970).length < 2 ^ (prefixWord ++ tailWord_1916970).sum := by decide
  have hdescent : baseEnd_1916970 < baseStart_1916970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917034 : List Nat := [3, 1, 3, 2, 3, 1, 1, 4, 1, 3]
def baseStart_1917034 : Nat := 118140960795 + 1917034 * 2 ^ 59
def prefixEnd_1917034 : Nat := 4983230072969 + 3 ^ 40 * 1917034 * 2
def baseEnd_1917034 : Nat := 656239915340905219572485

theorem tailTrace_1917034 : CollatzResearch.WordTrace tailWord_1917034 prefixEnd_1917034 656239915340905219572485 := by
  unfold tailWord_1917034
  simp only [CollatzResearch.WordTrace]
  refine ⟨17479993534230174046599539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46613316091280464124265437 17479993534230174046599539)
  ·
    refine ⟨26219990301345261069899309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17479993534230174046599539 26219990301345261069899309)
    ·
      refine ⟨9832496363004472901212241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26219990301345261069899309 9832496363004472901212241)
      ·
        refine ⟨7374372272253354675909181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9832496363004472901212241 7374372272253354675909181)
        ·
          refine ⟨2765389602095008003465943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7374372272253354675909181 2765389602095008003465943)
          ·
            refine ⟨4148084403142512005198915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2765389602095008003465943 4148084403142512005198915)
            ·
              refine ⟨6222126604713768007798373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4148084403142512005198915 6222126604713768007798373)
              ·
                refine ⟨1166648738383831501462195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6222126604713768007798373 1166648738383831501462195)
                ·
                  refine ⟨1749973107575747252193293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1166648738383831501462195 1749973107575747252193293)
                  ·
                    refine ⟨656239915340905219572485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1749973107575747252193293 656239915340905219572485)
                    ·
                      rfl

theorem cell22_1917034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 4, 1, 3].length) (baseStart_1917034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1917034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1917034 prefixEnd_1917034 := by exact prefixLift 1917034
  have htrace : WordTrace (prefixWord ++ tailWord_1917034) baseStart_1917034 baseEnd_1917034 := by
    simpa [prefixWord, tailWord_1917034, baseEnd_1917034] using wordTrace_append hprefix tailTrace_1917034
  have hstable : (prefixWord ++ tailWord_1917034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917034).length < 2 ^ (prefixWord ++ tailWord_1917034).sum := by decide
  have hdescent : baseEnd_1917034 < baseStart_1917034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917060 : List Nat := [2, 3, 2, 1, 2, 1, 2, 4, 1, 4]
def baseStart_1917060 : Nat := 118140960795 + 1917060 * 2 ^ 59
def prefixEnd_1917060 : Nat := 4983230072969 + 3 ^ 40 * 1917060 * 2
def baseEnd_1917060 : Nat := 656248815672249818422405

theorem tailTrace_1917060 : CollatzResearch.WordTrace tailWord_1917060 prefixEnd_1917060 656248815672249818422405 := by
  unfold tailWord_1917060
  simp only [CollatzResearch.WordTrace]
  refine ⟨34960461217413251313422317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46613948289884335084563089 34960461217413251313422317)
  ·
    refine ⟨13110172956529969242533369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34960461217413251313422317 13110172956529969242533369)
    ·
      refine ⟨9832629717397476931900027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13110172956529969242533369 9832629717397476931900027)
      ·
        refine ⟨14748944576096215397850041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9832629717397476931900027 14748944576096215397850041)
        ·
          refine ⟨11061708432072161548387531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14748944576096215397850041 11061708432072161548387531)
          ·
            refine ⟨16592562648108242322581297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11061708432072161548387531 16592562648108242322581297)
            ·
              refine ⟨12444421986081181741935973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16592562648108242322581297 12444421986081181741935973)
              ·
                refine ⟨2333329122390221576612995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12444421986081181741935973 2333329122390221576612995)
                ·
                  refine ⟨3499993683585332364919493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2333329122390221576612995 3499993683585332364919493)
                  ·
                    refine ⟨656248815672249818422405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3499993683585332364919493 656248815672249818422405)
                    ·
                      rfl

theorem cell22_1917060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_1917060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1917060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1917060 prefixEnd_1917060 := by exact prefixLift 1917060
  have htrace : WordTrace (prefixWord ++ tailWord_1917060) baseStart_1917060 baseEnd_1917060 := by
    simpa [prefixWord, tailWord_1917060, baseEnd_1917060] using wordTrace_append hprefix tailTrace_1917060
  have hstable : (prefixWord ++ tailWord_1917060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917060).length < 2 ^ (prefixWord ++ tailWord_1917060).sum := by decide
  have hdescent : baseEnd_1917060 < baseStart_1917060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917120 : List Nat := [2, 1, 1, 2, 5, 1, 4, 6]
def baseStart_1917120 : Nat := 118140960795 + 1917120 * 2 ^ 59
def prefixEnd_1917120 : Nat := 4983230072969 + 3 ^ 40 * 1917120 * 2
def baseEnd_1917120 : Nat := 72918817210936629102469

theorem tailTrace_1917120 : CollatzResearch.WordTrace tailWord_1917120 prefixEnd_1917120 72918817210936629102469 := by
  unfold tailWord_1917120
  simp only [CollatzResearch.WordTrace]
  refine ⟨34961555407304566437014407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46615407209739421916019209 34961555407304566437014407)
  ·
    refine ⟨52442333110956849655521611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34961555407304566437014407 52442333110956849655521611)
    ·
      refine ⟨78663499666435274483282417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52442333110956849655521611 78663499666435274483282417)
      ·
        refine ⟨58997624749826455862461813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78663499666435274483282417 58997624749826455862461813)
        ·
          refine ⟨5531027320296230237105795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58997624749826455862461813 5531027320296230237105795)
          ·
            refine ⟨8296540980444345355658693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5531027320296230237105795 8296540980444345355658693)
            ·
              refine ⟨1555601433833314754186005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8296540980444345355658693 1555601433833314754186005)
              ·
                refine ⟨72918817210936629102469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1555601433833314754186005 72918817210936629102469)
                ·
                  rfl

theorem cell22_1917120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 4, 6].length) (baseStart_1917120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1917120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1917120 prefixEnd_1917120 := by exact prefixLift 1917120
  have htrace : WordTrace (prefixWord ++ tailWord_1917120) baseStart_1917120 baseEnd_1917120 := by
    simpa [prefixWord, tailWord_1917120, baseEnd_1917120] using wordTrace_append hprefix tailTrace_1917120
  have hstable : (prefixWord ++ tailWord_1917120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917120).length < 2 ^ (prefixWord ++ tailWord_1917120).sum := by decide
  have hdescent : baseEnd_1917120 < baseStart_1917120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917163 : List Nat := [1, 1, 1, 1, 2, 5, 2, 1, 1, 7]
def baseStart_1917163 : Nat := 118140960795 + 1917163 * 2 ^ 59
def prefixEnd_1917163 : Nat := 4983230072969 + 3 ^ 40 * 1917163 * 2
def baseEnd_1917163 : Nat := 656284074677191883097089

theorem tailTrace_1917163 : CollatzResearch.WordTrace tailWord_1917163 prefixEnd_1917163 656284074677191883097089 := by
  unfold tailWord_1917163
  simp only [CollatzResearch.WordTrace]
  refine ⟨69924679153453351217844143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46616452768968900811896095 69924679153453351217844143)
  ·
    refine ⟨104887018730180026826766215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69924679153453351217844143 104887018730180026826766215)
    ·
      refine ⟨157330528095270040240149323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104887018730180026826766215 157330528095270040240149323)
      ·
        refine ⟨235995792142905060360223985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157330528095270040240149323 235995792142905060360223985)
        ·
          refine ⟨176996844107178795270167989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235995792142905060360223985 176996844107178795270167989)
          ·
            refine ⟨16593454135048012056578249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 176996844107178795270167989 16593454135048012056578249)
            ·
              refine ⟨12445090601286009042433687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16593454135048012056578249 12445090601286009042433687)
              ·
                refine ⟨18667635901929013563650531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12445090601286009042433687 18667635901929013563650531)
                ·
                  refine ⟨28001453852893520345475797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18667635901929013563650531 28001453852893520345475797)
                  ·
                    refine ⟨656284074677191883097089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28001453852893520345475797 656284074677191883097089)
                    ·
                      rfl

theorem cell22_1917163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 7].length) (baseStart_1917163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1917163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1917163 prefixEnd_1917163 := by exact prefixLift 1917163
  have htrace : WordTrace (prefixWord ++ tailWord_1917163) baseStart_1917163 baseEnd_1917163 := by
    simpa [prefixWord, tailWord_1917163, baseEnd_1917163] using wordTrace_append hprefix tailTrace_1917163
  have hstable : (prefixWord ++ tailWord_1917163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917163).length < 2 ^ (prefixWord ++ tailWord_1917163).sum := by decide
  have hdescent : baseEnd_1917163 < baseStart_1917163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917214 : List Nat := [4, 3, 2, 1, 1, 2, 1, 1, 2, 5]
def baseStart_1917214 : Nat := 118140960795 + 1917214 * 2 ^ 59
def prefixEnd_1917214 : Nat := 4983230072969 + 3 ^ 40 * 1917214 * 2
def baseEnd_1917214 : Nat := 656301533019444750071933

theorem tailTrace_1917214 : CollatzResearch.WordTrace tailWord_1917214 prefixEnd_1917214 656301533019444750071933 := by
  unfold tailWord_1917214
  simp only [CollatzResearch.WordTrace]
  refine ⟨8740817409533573365993837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46617692850845724618633797 8740817409533573365993837)
  ·
    refine ⟨3277806528575090012247689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8740817409533573365993837 3277806528575090012247689)
    ·
      refine ⟨2458354896431317509185767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3277806528575090012247689 2458354896431317509185767)
      ·
        refine ⟨3687532344646976263778651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2458354896431317509185767 3687532344646976263778651)
        ·
          refine ⟨5531298516970464395667977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3687532344646976263778651 5531298516970464395667977)
          ·
            refine ⟨4148473887727848296750983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5531298516970464395667977 4148473887727848296750983)
            ·
              refine ⟨6222710831591772445126475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4148473887727848296750983 6222710831591772445126475)
              ·
                refine ⟨9334066247387658667689713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6222710831591772445126475 9334066247387658667689713)
                ·
                  refine ⟨7000549685540744000767285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9334066247387658667689713 7000549685540744000767285)
                  ·
                    refine ⟨656301533019444750071933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7000549685540744000767285 656301533019444750071933)
                    ·
                      rfl

theorem cell22_1917214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_1917214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1917214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1917214 prefixEnd_1917214 := by exact prefixLift 1917214
  have htrace : WordTrace (prefixWord ++ tailWord_1917214) baseStart_1917214 baseEnd_1917214 := by
    simpa [prefixWord, tailWord_1917214, baseEnd_1917214] using wordTrace_append hprefix tailTrace_1917214
  have hstable : (prefixWord ++ tailWord_1917214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917214).length < 2 ^ (prefixWord ++ tailWord_1917214).sum := by decide
  have hdescent : baseEnd_1917214 < baseStart_1917214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
